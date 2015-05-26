(* ------------------------------------------------------------------------------------------------ *)
(* enable quotation and preprocessing																*)
#require "camlp5";;
#load "camlp5o.cma";;

(* macro expansion evil... *)
let quotexpander s =
	if String.sub s 0 1 = "|" && String.sub s (String.length s-1) 1 = "|" then
		"secondary_parser \""^
		(String.escaped (String.sub s 1 (String.length s -2)))^"\""
	else "default_parser \""^(String.escaped s)^"\"";;

Quotation.add "" (Quotation.ExStr (fun x -> quotexpander));;
	
(* ------------------------------------------------------------------------------------------------ *)
(* pretty printer library																			*)

open Format
(* ------------------------------------------------------------------------------------------------ *)
(* helper list functions																			*)

let length l =
	let rec len k l =
		match l with
		| [] -> k
		| _::t -> len (k+1) t
	in len 0 l
		
let hd l =
	match l with 
	| h::t -> h
	| _ -> failwith "hd"

let tl l =
	match l with
	| h::t -> t
	| _ -> failwith "tl"	(* why not []? *)

let explode s =
	let rec exap n l =
		if n < 0 then l else
		exap (n - 1) ((String.sub s n 1)::l) in
	exap (String.length s -1) []

let rec mem x l =
	match l with
	| [] -> false
	| (h::t) -> Pervasives.compare x h = 0 || mem x t

let rec forall p l =
	match l with
	| [] -> true
	| h::t -> p(h) && forall p t

let rec exists p l =
	match l with
	| [] -> false
	| h::t -> p(h) || exists p t

let rec do_list f l =
	match l with
	| [] -> ()
	| x::t -> f x; do_list f t

let rec el n l =
	if n = 0 then hd l else el (n - 1) (tl l)

(* ------------------------------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------------------------------ *)
(* the types to parse *)

(* ------------------------------------------------------------------------------------------------ *)
(* type formula *)
type ('a)formula =
	| False
	| True
	| Atom of 'a
	| Not of ('a)formula
	| And of ('a)formula * ('a)formula
	| Or of ('a)formula * ('a)formula
	| Imp of ('a)formula * ('a)formula
	| Iff of ('a)formula * ('a)formula
	| Forall of string * ('a)formula
	| Exists of string * ('a)formula

(* ------------------------------------------------------------------------------------------------ *)
(* prop for propositions *)
type prop = P of string

let pname(P s) = s

(* ------------------------------------------------------------------------------------------------ *)
(* atomic propositions can be build up from non-propositional variables								*)
(* the non-propositional variables can be bound with quantifiers									*)
(* we make the syntactic distinction between formulas (true,false) and terms which denote objects	*)
(* a term is either a variable or a function applied to any number of other 'argument' terms		*)
(* functions can have any number of arguments, this number being known as their "arity".
	in particular we can accommodate constants like 1 or π as nullary functions:
		Fn("1",[])

	example: sqrt(1-cos^2(x+y)) becomes:

	Fn("sqrt",[
		FN ("-",[
			Fn(1,[];
			Fn("cos",[
				Fn("power",[
					Fn("plus",[
						Var "x";
						Var "y"l]]]]]
*)
type term = 
	| Var of string
	| Fn of string * term list

(* ------------------------------------------------------------------------------------------------ *)
(* create a new type for first order atomic propositions -- why "R"? *)
type fol = R of string * term list

(* this type can be embedded in ('a)formula -- we than get formula fol								*)
(* example:																							*)
(*		x + y < z:																					*)
(*		Atom(R("<",[Fn("+",[Var "x";Var "y"]); Var "z"]))											*)


(* ------------------------------------------------------------------------------------------------ *)
(* Lexical analysis.                                                         *)

let matches s = let chars = explode s in fun c -> mem c chars

let space = matches " \t\n\r"
and punctuation = matches "()[]{},"
and symbolic = matches "~`!@#$%^&*-+=|\\:;<>.?/"
and numeric = matches "0123456789"
and alphanumeric = matches
  "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

let rec lexwhile prop inp =
	match inp with
	| c::cs when prop c -> let (tok,rest) = lexwhile prop cs in (c^tok,rest)
	| _ -> ("",inp)

let rec lex inp =
	match snd(lexwhile space inp) with
	| [] -> []
	| c::cs -> let prop = if alphanumeric(c) then alphanumeric
							else if symbolic(c) then symbolic
							else fun c -> false in
				let toktl,rest = lexwhile prop cs in
				(c^toktl)::lex rest

(* ------------------------------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------------------------------ *)
(* general parsing functions																		*)

(* associativity for infix operators: *)
(*	opsym :		operator symbol
	opupdate:	modifies the function accordingly when a new item is parsed	
				so this changes associativity ???
	sof:		takes the current input (tokens or the AST?) and combines it in some way with the items arrived so far
	subparser:
	inp:		token input	

	helper functions:
	hd:			head of a list
	tl:			tail of a list
*)

let rec parse_ginfix opsym opupdate sof subparser inp =
	let (e1,inp1) = subparser inp in
	if inp1 <> [] && hd inp1 = opsym then		
		parse_ginfix opsym opupdate (opupdate sof e1) subparser (tl inp1)
	else (sof e1,inp1)

let parse_left_infix opsym opcon =
	parse_ginfix opsym 
	(fun f e1 e2 -> opcon(f e1,e2)) 
	(fun x -> x)

let parse_right_infix opsym opcon =
	parse_ginfix 
	opsym
	(fun f e1 e2 -> f(opcon(e1,e2)))
	(fun x -> x)

let parse_list opsym =
	parse_ginfix 
	opsym 
	(fun f e1 e2 -> (f e1)@[e2])
	(fun x -> [x])

(* mapping over some ast *)
let papply f (ast,rest) = (f ast,rest)

(* checks whether the next item in the head of a list (typically some unparsed input)
   is some specific item and that the list os nonempty *)
(* is this a comparison for physical equality? *)
let nextin inp tok = inp <> [] && hd inp = tok

(* parsing bracketed expressions *)
let parse_bracketed subparser cbra inp =
	let (ast,rest) = subparser inp in
	if nextin rest cbra then (ast,tl rest)
	else failwith "Closing bracket expected"

let make_parser pfn s =
	let (expr,rest) = pfn (lex(explode s)) in
	if rest = [] then expr else failwith "Unparsed input"


(* ------------------------------------------------------------------------------------------------ *)
(* parsing formulas *)
(* lexer can be unchanged *)

let rec parse_atomic_formula (ifn,afn) vs inp =
	match inp with
	| [] -> failwith "formula exected"
	| "false"::rest -> (False,rest)
	| "true"::rest -> (True,rest)
	| "("::rest -> (try ifn vs inp with Failure _ -> 
					parse_bracketed (parse_formula (ifn,afn) vs) ")" rest)
	| "~"::rest -> papply (fun p -> Not p)
							(parse_atomic_formula (ifn,afn) vs rest)
	| "forall"::x::rest -> 
			parse_quant (ifn,afn) (x::vs) (fun (x,p) -> Forall(x,p)) x rest 
	| "exists"::x::rest -> 
			parse_quant (ifn,afn) (x::vs) (fun (x,p) -> Exists(x,p)) x rest 
	| _ -> afn vs inp
and parse_quant (ifn,afn) vs qcon x inp =
	match inp with
	| [] -> failwith "Body of quantified term expected"
	| y::rest -> 
		papply (fun fm -> qcon(x,fm))
				(if y = "." then parse_formula (ifn,afn) vs rest
				else parse_quant (ifn,afn) (y::vs) qcon y rest)
and parse_formula (ifn,afn) vs inp =
	parse_right_infix "<=>" (fun (p,q) -> Iff(p,q))
		(parse_right_infix "==>" (fun (p,q) -> Imp(p,q))
			(parse_right_infix "\\/" (fun (p,q) -> Or(p,q))
				(parse_right_infix "/\\" (fun (p,q) -> And(p,q))
					(parse_atomic_formula (ifn,afn) vs )))) inp

(* ------------------------------------------------------------------------------------------------ *)
(* parsing propositions *)
let parse_propvar vs inp =
	match inp with
	| p::oinp when p <> "(" -> (Atom(P(p)),oinp)
	| _ -> failwith "parse_propvar"

let parse_prop_formula =
	make_parser (parse_formula ((fun _ _ -> failwith ""),parse_propvar) [])

(* ------------------------------------------------------------------------------------------------ *)
(* parsing first-order terms and formulas *)

(* only numerals and the empty list constant "nil" are considered as constants *)

(* is_cont_name s : s -> bool *)
let is_const_name s = forall numeric (explode s) || s = "nil"

(* additional argument "vs":
In order to check whether a name is within the scope of a quantifier,
all the parsing functions take an additional argument "vs" 
which is the set of bound variables in the current scope.
parsing is then straightforard
*)

let rec parse_atomic_term vs inp =
	match inp with
	| [] -> failwith "term expected"
	| "("::rest -> parse_bracketed (parse_term vs) ")" rest
	| "~"::rest -> papply (fun t -> Fn("~",[t])) (parse_atomic_term vs rest)
	| f::"("::")"::rest -> (Fn(f,[]), rest)
	| f::"("::rest -> 
		papply (fun args -> Fn(f,args))
				(parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
	| a :: rest -> 
		((if is_const_name a && not(mem a vs) then Fn(a,[]) else Var a), rest)
and parse_term vs inp =
	parse_right_infix "::" (fun (e1,e2) -> Fn("::",[e1;e2]))
		(parse_right_infix "+" (fun (e1,e2) -> Fn("+",[e1;e2]))
			(parse_left_infix "-" (fun (e1,e2) -> Fn("-",[e1;e2]))
				(parse_right_infix "*" (fun (e1,e2) -> Fn("*",[e1;e2]))
					(parse_left_infix "^" (fun (e1,e2) -> Fn("^",[e1;e2]))
						(parse_atomic_term vs))))) inp

let parset = make_parser (parse_term [])

(* recognizer for "infix" formulas like s < t *)
let parse_infix_atom vs inp =
	let (tm,rest) = parse_term vs inp in
	if exists (nextin rest) ["=";"<";"<=";">";">="] then
	papply (fun tm' -> Atom(R(hd rest,[tm;tm'])))
			(parse_term vs (tl rest))
	else failwith ""

(* *)
let parse_atom vs inp =
	try parse_infix_atom vs inp with Failure _ -> 
	match inp with
	| p::"("::")"::rest -> (Atom(R(p,[])),rest)
	| p::"("::rest -> 
		papply (fun args -> Atom(R(p,args)))
			(parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
	| p::rest when p <> "(" -> (Atom(R(p,[])),rest)
	| _ -> failwith "parse Atom"


(* A major problem is that we keep using the error mechanism for backtracking ... use OCaml's maybe type!*)

let parse = make_parser
	(parse_formula (parse_infix_atom,parse_atom) [])

(* test: parse "sqrt(1-cos^2(x+y))" *)

(* let default_parser = parse *)
let default_parser = parse_prop_formula
let secondary_parser = parset

(* ------------------------------------------------------------------------------------------------ *)
(* pretty printing *)
(* outputs directly to stdout using the "Format" library facilites									*)

let bracket p n f x y =
	(if p then print_string "(" else ());
	open_box n;
	f x y;
	close_box();
	(if p then print_string ")" else ())


(* convention: omitt the quantifiers symbol with repeated quantifiers								*)
let rec strip_quant fm =
	match fm with
	| Forall(x,(Forall(y,p) as yp)) | Exists(x,(Exists(y,p) as yp)) -> 
		let (xs,q) = strip_quant yp 
		in (x::xs,q)
	| Forall(x,p) | Exists(x,p) -> ([x],p)
	| _ -> ([],fm);;


(* printing is parameterized by a function to print atoms (pfn)										*)
let print_formula pfn =
	let rec print_formula pr fm =
		match fm with
		| False -> print_string "false"
		| True -> print_string "true"
		| Atom(pargs) -> pfn pr pargs
		| Not(p) -> bracket (pr > 10) 1 (print_prefix 10) "~" p
		| And(p,q) -> bracket (pr > 8) 0 (print_infix 8 "/\\") p q
		| Or(p,q) -> bracket (pr > 6) 0 (print_infix 6 "\\/") p q
		| Imp(p,q) -> bracket (pr > 4) 0 (print_infix 4 "==>") p q
		| Iff(p,q) -> bracket (pr > 2) 0 (print_infix 2 "<=>") p q
		| Forall(x,p) -> bracket (pr > 0) 2 print_qnt "forall" (strip_quant fm)
		| Exists(x,p) -> bracket (pr > 0) 2 print_qnt "exists" (strip_quant fm)
	and print_qnt qname (bvs,bod) =
		print_string qname;
		do_list (fun v -> print_string " "; print_string v) bvs;
		print_string "."; print_space(); open_box 0;
		print_formula 0 bod;
		close_box()
	and print_prefix newpr sym p =
		print_string sym; print_formula (newpr+1) p
	and print_infix newpr sym p q =
		print_formula (newpr+1) p;
		print_string(" "^sym); print_space();
		print_formula newpr q in
	print_formula 0	

let print_qformula pfn fm =
	open_box 0;
	print_string "<<";
	open_box 0;
	print_formula pfn fm; close_box();
	print_string ">>";
	close_box()

let rec print_term prec fm =
	match fm with 
	| Var x -> print_string x
	| Fn("^",[tm1;tm2]) -> print_infix_term true prec 24 "^" tm1 tm2
	| Fn("/",[tm1;tm2]) -> print_infix_term true prec 22 " /" tm1 tm2
	| Fn("*",[tm1;tm2]) -> print_infix_term false prec 20 " *" tm1 tm2
	| Fn("-",[tm1;tm2]) -> print_infix_term true prec 18 " -" tm1 tm2
	| Fn("+",[tm1;tm2]) -> print_infix_term false prec 16 " +" tm1 tm2
	| Fn("::",[tm1;tm2]) -> print_infix_term false prec 14 "::" tm1 tm2
	| Fn(f,args) -> print_fargs f args
and print_fargs f args =
	print_string f;
	if args = [] then () else
	( print_string "(";
		open_box 0;
		print_term 0 (hd args); print_break 0 0;
		do_list (fun t -> print_string ","; print_break 0 0; print_term 0 t)
				(tl args);
		close_box();
		print_string ")")
and print_infix_term isleft oldprec newprec sym p q =
	if oldprec > newprec then (print_string "("; open_box 0) else ();
	print_term (if isleft then newprec else newprec+1) p;
	print_string sym;
	print_break (if String.sub sym 0 1 = "" then 1 else 0)0;
	print_term (if isleft then newprec+1 else newprec) q;
	if oldprec > newprec then (close_box(); print_string ")") else ()

(* printing of terms *)
let printert tm =
	open_box 0; print_string "<<|";
	open_box 0; print_term 0 tm; close_box();
	print_string "|>>"; close_box()

let print_atom prec (R(p,args)) =
	if mem p ["="; "<"; "<="; ">"; ">="] && length args = 2
	then print_infix_term false 12 12 (" "^p) (el 0 args) (el 1 args)
	else print_fargs p args


let print_fol_formula = print_qformula print_atom

let print_propvar prec p = print_string(pname p);;
let print_prop_formula = print_qformula print_propvar;;


#install_printer printert;;
#install_printer print_prop_formula;;
#install_printer print_fol_formula;;

(* ------------------------------------------------------------------------ *)
(* propositional logic														*)
