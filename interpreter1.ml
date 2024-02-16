type acl = 
    | Empty
    | AC of string*acl;;

type expr =
 | CstI of int
 | CstB of bool
 | Var of string
 | Let of string * expr * expr
 | Prim of string * expr * expr
 | LetEM of string * expr * acl * expr 
 | If of expr * expr * expr
 | Fun of string * expr * expr
 | Call of expr * expr
 | Read of string
 | Open of string
 | Write of expr * string
 | Perm of int * int * int;;


type 'v env = (string * 'v) list;;

let rec lookup env x =
   match env with
   | []        -> failwith (x ^ " not found")
   | (y, v)::r -> if x=y then v else lookup r x;;

let rec emCheck alist op = 
    match alist with   
        | Empty -> false
        | AC(aop,als) -> if op=aop then true else emCheck als op;;

let rec extend al1 al2 = match al2 with 
    | Empty -> al1 
    | AC(aop, als) -> AC(aop, (extend al1 als));;

type iexpr =
 | CstI of int
 | CstB of bool
 | Var of string
 | Let of string * iexpr * iexpr
 | Prim of string * iexpr * iexpr
 | LetEM of string * iexpr * acl * iexpr
 | If of iexpr * iexpr * iexpr
 | Fun of string * iexpr * iexpr
 | Call of iexpr * iexpr
 | Read of string
 | Open of string
 | Write of iexpr * string
 | Perm of int * int * int
 | Abort of string
 | ReadVar
 | WriteVar
 | OpenVar;;

type perm_var = int * int * (int * iexpr -> (int  option) * string) * string;; 

type ivalue =
 | Int of int
 | Closure of string * iexpr * ivalue env * iexpr;;

let rec stack_inspection (g : iexpr env) : iexpr =
  match g with
    | [] -> failwith "stack inspection fail: the stack can't be empty"
    | [("init", (Perm(1, 1, 1)) )] -> Perm(1, 1, 1) 
    | (h, p) :: t -> let t_1 = stack_inspection t in 
        match p with
            | Perm(i, j, k) -> match t_1 with 
                                    | Perm(x, y, z) -> Perm(i*x, j*y, k*z)
                                    | _ ->  failwith "stack inspection fail: the parameters passed are not allowed"
            | _ ->  failwith "stack inspection fail: the parameters passed are not allowed";;

let rec ieval (e : iexpr) (env : ivalue env) (g : iexpr env) (alist : acl) : ivalue * iexpr env  =
   match e with
   | CstI i -> (Int i, g)
   | CstB b -> (Int (if b then 1 else 0), g)
   | Var x  -> (lookup env x, g)
   | Prim(ope, e1, e2) ->
     let (v1, g) = ieval e1 env g alist in
     let (v2, g) = ieval e2 env g alist in
     begin
     match (ope, v1, v2) with
     | ("*", Int i1, Int i2) -> if (emCheck alist "*") then (Int (i1 * i2), g) else failwith("Mul not allowed")
     | ("+", Int i1, Int i2) -> if (emCheck alist "+") then (Int (i1 + i2), g) else failwith("Sum not allowed")
     | ("-", Int i1, Int i2) -> if (emCheck alist "-") then (Int (i1 - i2), g) else failwith("Sub not allowed")
     | ("=", Int i1, Int i2) -> if (emCheck alist "=") then (Int (if i1 = i2 then 1 else 0), g) else failwith("Eq not allowed")
     | ("<", Int i1, Int i2) -> if (emCheck alist "<") then (Int (if i1 < i2 then 1 else 0), g) else failwith("Comp not allowed")
     |  _ -> failwith "unknown primitive or wrong type"
     end
     | LetEM(i,e1,al,e2) -> let newal = (extend alist al) in 
                                let (xVal,g) = ieval e1 env g newal
                                        in ieval e2 ((i, xVal) :: env) g newal
   | Let(x, eRhs, letBody) ->
     let (xVal, g) = ieval eRhs env g alist in
     let letEnv = (x, xVal) :: env in
     ieval letBody letEnv g alist
   | If(e1, e2, e3) ->
     begin
     match ieval e1 env g alist with
     | (Int 0, g) -> ieval e3 env g alist
     | (Int _, g) -> ieval e2 env g alist
     | _     -> failwith "eval If"
     end
   | Fun(x,fBody, p) -> (Closure(x, fBody, env, p), g)
   | Call(eFun, eArg) ->
     let (fClosure, _) = ieval eFun env g alist in
     begin
     match fClosure with
     | Closure (x, fBody, fDeclEnv, p) ->
       let perm_stack = ("", p) :: g in 
       let (xVal, g) = ieval eArg env g alist in
       let fBodyEnv = (x, xVal) :: fDeclEnv
       in ieval fBody fBodyEnv perm_stack alist
     | _ -> failwith "eval Call: not a function"
     end
   | Read(_) -> (Int 0, g)
   | Write(x, _) -> let (_, g) = ieval x env g alist in (Int 1, g)
   | Open(_) -> (Int 2, g)
   | Abort msg -> failwith msg
   | ReadVar -> begin match (stack_inspection g) with 
   			 	    | Perm(r, _, _) -> (Int(r), g)
                    | _ -> failwith "evaluation (ieval) fail: not a permission"
   			     end
   | WriteVar -> begin match (stack_inspection g)  with 
   			 	    | Perm(_, w, _) -> (Int(w), g)
                    | _ -> failwith "evaluation (ieval) fail: not a permission"
   			     end
   | OpenVar -> begin match (stack_inspection g) with 
   			 	    | Perm(_, _, o) -> (Int(o), g)
                    | _ -> failwith "evaluation (ieval) fail: not a permission"
   			     end;;

let check_oper e  = 
    match e with   
      | Read _ -> ReadVar
		  | Write (_, _) -> WriteVar
		  | Open _ -> OpenVar
      | _ -> failwith "check operation fail: the parameter passed is not a Read, Write, Open operation";;

let demandPerm (s0, s1, delta, msg) e = 
	If(Prim("=", check_oper e, CstI s0), 
		begin match (delta(s0,e)) with 
			| (Some s, _) -> e
			| (None, str) -> Abort(str ^ " " ^ msg)
		end, 
		begin match (delta(s1,e)) with 
			| (Some s, _) -> e
			| (None, str) -> Abort(str ^ " " ^ msg)
		end)

let rec comp (pv : perm_var ) (e : expr) : iexpr = match e with
	| CstI i -> CstI i
	| CstB b -> CstB b
	| Var x ->  Var x
    | Perm(i, j, k) -> Perm(i, j, k) 
	| Prim(ope, e1, e2) -> (Prim(ope, (comp pv e1), (comp pv e2)))
    | LetEM(i,e1,al,e2) -> LetEM(i, (comp pv e1), al, (comp pv e2))
	| Let(x, e1, e2) -> Let(x, (comp pv e1), (comp pv e2))
	| If(e1, e2, e3) ->(If((comp pv e1), (comp pv e2), (comp pv e3)))
	| Fun(x, e, p) -> Fun(x, (comp pv e), (comp pv p))
	| Call(f, a) -> (Call((comp pv f), (comp pv a)))
	| Read s -> demandPerm pv (Read s)
	| Write(e, s) -> demandPerm pv (Write((comp pv e), s))
	| Open s -> demandPerm pv (Open s);;

let myDelta (s, e) = match (s, e) with
	| (0, Read _) -> (None, "read")
	| (0, Write(_, _)) -> (None, "write")
	| (0, Open _) -> (None, "open")
	| (1, _) -> (Some 1, "")
	| _ -> (None,"");;

let eval (e : expr) (env : ivalue env) (pv : perm_var) (alist : acl) : ivalue = match pv with
	| (init, _, _, _) -> let (result, _) = ieval (comp pv e) env ([("init", (Perm(init, init, init)) )]) alist in result;; (* Perm(read, write, open) *)

let myperm = (1, 0, myDelta, "permission denied");;

let acL = AC("+", AC("=", AC("*",Empty) ) );;


let first_test : expr = Let("f",Fun("x",Let("g",Fun("y",Let("h",Fun("z",Open("Hello world!"),Perm(1,1,1)),
  Call(Var "h",Var "x")),     Perm(1,1,0)     ),Call(Var "g",CstI(5))),Perm(1,1,1)),Call(Var "f", CstI(10)));;

eval first_test [] myperm acL;; 

(* test 2 (E' Permessa l'operazione di Write se la funzione ha i permessi di Write, ed e'chiamata da una o piu' funzioni con permesso di Write: 
fun_2 e fun_3 hanno solo i permessi di Write attivi(0,1,0).
In Ocaml il seguente test s potrebbe scrivere cosi' (Queste serie di funzione tornano un'intero aumentato di 110):
# let fun_1 = fun x -> x+1;;
    # let fun_2 = fun x-> let y = Open("file") in fun_1(110);;
        # let fun_3 = fun x-> fun_2(110);;
            # let result = fun_3(1);;   che ritorna sempre  int = 111
Comportamento atteso: - : ivalue = Int 111.  

let fun_1 : expr = Fun("x", Prim("+",Var("x"),CstI(1)),Perm(0,0,0));; (* Perm(read, write, open) *)
let fun_2 : expr = Fun("x", Let("y",Write(CstI 1, "file2"), Call(fun_1,CstI 110)),Perm(0,1,0));;
let fun_3 : expr = Fun("x", Call(fun_2,CstI 10), Perm(0,1,0))
let cally : expr = Call(fun_3,CstI 1);; 
eval cally [] myperm acL;;*)

(* test 3
let acL_2 = AC("+",AC("=",Empty));;
let fun_1 : expr = Fun("x", Prim("+",Var("x"),CstI(1)),Perm(1,1,1));;
let fun_2 : expr = Fun("x", Prim("*",Var("x"),Read("file2")),Perm(1,0,1));;
let fun_3 : expr = Fun("x", Call(fun_2,CstI 10), Perm(1,1,1))
let cally : expr = Call(fun_3,CstI 1);;
eval cally [] myperm acL_2;;*)

(* test 4 
let fun_1 : expr = Fun("x", Prim("+",Var("x"),CstI(1)),Perm(0,0,0));;
let fun_2 : expr = Fun("x", Let("y",Write(CstI 1, "file2"), Call(fun_1,CstI 110)),Perm(1,1,1));;
let fun_3 : expr = Fun("x", Call(fun_2,CstI 10), Perm(1,0,1))
let cally : expr = Call(fun_3,CstI 1);;
eval cally [] myperm acL;;*)

(* test 5
let fun_1 : expr = Fun("x", Prim("+",Var("x"),CstI(1)),Perm(1,1,1));;
let fun_2 : expr = Fun("x", Let("y",Write(CstI 1, "file2"), Call(fun_1,CstI 110)),Perm(1,1,1));;
let fun_3 : expr = Fun("x",Let("y",Open("file2"), Call(fun_2,CstI 11)), Perm(1,0,1))
let fun_4 : expr = Fun("x", Let("y",Read("file2"), Call(fun_2,CstI 19)), Perm(1,1,1))
let fun_5 : expr = Fun("x", Let("y",Read("file2"), Call(fun_2,CstI 11)), Perm(1,1,1))
let cally : expr = Call(fun_3,CstI 1);;
eval cally [] myperm acL;;*)

(* test 6
let fun_n : expr = Let("f",Fun("x",Let("g",Fun("y",Read(""),Perm(1,1,1)),Call(Var "g",CstI(3))),     Perm(0,1,1)     ),Call(Var "f", CstI(10)));;
eval fun_n [] myperm acL;;*)

