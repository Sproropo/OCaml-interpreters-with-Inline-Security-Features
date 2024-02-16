exception Denied of string;;
type state = int;;
type symbol = char;;
type transition = state * symbol * state;;

type dfa =
  {
    states : state list;
    sigma : symbol list;
    start : state;
    transitions : transition list;
    accepting : state list;
  };;

let explode s = 
  let rec expl i l =
    if i < 0 then l else
      expl (i - 1) (s.[i] :: l) in 
  expl (String.length s - 1) [];;

let rec contains e l = 
  match l with
  | [] -> false
  | hd::tl -> if hd = e then true else contains e tl;;

let checkAccepts str dfa = 
  let symbols = explode str in 
  let transition state symbol = 
    let rec find_state l = 
      match l with
      | (s1,sym,s2)::tl ->
          if (s1 = state && symbol = sym) then
            s2 else find_state tl
      | _ -> failwith "Transizione di stato non accettata"
    in find_state dfa.transitions
  in
  let final_state =
    let rec h symbol_list =
      match symbol_list with
      | [hd] -> (transition dfa.start hd)
      | hd::tl -> (transition (h tl) hd) 
      | _ -> failwith "Primitiva non concessa"
    in
    h (List.rev symbols) 
  in
  if (contains final_state dfa.accepting) then 
    true
  else
    false;;

let rec checkAcceptsAll str dfa_list : bool=
  match dfa_list with
  | [] -> true
  | h::t -> if checkAccepts str h then checkAcceptsAll str t else false
 
type expr =
  | CstI of int
  | CstB of bool
  | CstString of string 
  | Var of string
  | Let of string * expr * expr
  | Prim of string * expr * expr	
  | If of expr * expr* expr
  | Fun of string * expr
  | Call of expr * expr
  | Read of string
  | Write of string
  | Open of string
  | Phi of dfa * expr 
  | FunR of string * string * expr
  | Letrec of string * string * expr * expr
  | Seq of expr * expr
  | UserPolicy of string * expr;;

type proc = Proc of expr list;; 


type 'v env = (string * 'v) list;;
 
let rec lookup env x =
  match env with
  | []        -> failwith (x ^ " not found")
  | (y, v)::r -> if x=y then v else lookup r x;;
  
type value =
  | Int of int
  | String of string
  | Closure of string * expr * value env
  | RecClosure of string * string * expr * value env
;;

let create_tuple_transition (s:char)(n:int) = match s with 
        | 'O' -> [(n,'o',n+1); (n+1,'r',n+1); (n+1,'w',n+1); (n+1,'o',n+1); (n,'r',n); (n,'w',n)]
        | 'R' -> [(n,'r',n+1); (n+1,'w',n+1); (n+1,'o',n+1); (n+1,'r',n+1); (n,'w',n); (n,'o',n)]
        | 'W' -> [(n,'w',n+1); (n+1,'r',n+1); (n+1,'o',n+1); (n+1,'w',n+1); (n,'r',n); (n,'o',n)]
        | _ -> failwith("Unexpected string in input");;

let create_tuple_special (s:char)(n:int) = match s with
        | 'O' -> [ (n,'r',n); (n,'w',n); (n,'o',n+1)]
        | 'R' -> [ (n,'o',n); (n,'w',n); (n,'r',n+1)]
        | 'W' -> [ (n,'r',n); (n,'o',n); (n,'w',n+1)]
        | _ -> failwith("Unexpected string in input");;

let generate_transition str =  let p_list = explode str in 
            let rec aux list_char n acc =
                match list_char with
                    | [] -> acc 
                    | [hd] -> ((create_tuple_special hd n) @ acc ) 
                    | h::(k::d as t) -> if (k = 'a') then aux d (n-1) acc 
                                    else aux t n ((create_tuple_transition k n) @ acc )
                        in aux p_list 1 [];;

(* Interprete *) 
let rec eval expr env (eta:string) (dfa_list:dfa list) =
  match expr with 
  | CstI (n)-> (Int(n), env, eta, dfa_list)
  | CstB (n)-> if n then (Int(1), env, eta, dfa_list) else (Int(0), env, eta, dfa_list) 
  | CstString s -> (String(s), env, eta, dfa_list)
  | Var (x) -> ((lookup env x), env, eta, dfa_list)
  | Prim(op,e1,e2) -> 
      let v1, env, eta_new, dfa_list = eval e1 env eta dfa_list in
        let v2, env, eta_new2, dfa_list = eval e2 env eta_new dfa_list in
          begin 
            match (op, v1, v2) with
            | ("*", Int i1, Int i2) -> (Int (i1 * i2), env, eta_new2, dfa_list)
            | ("+", Int i1, Int i2) -> (Int (i1 + i2), env, eta_new2, dfa_list)
            | ("-", Int i1, Int i2) -> (Int (i1 - i2), env, eta_new2, dfa_list)
            | ("=", Int i1, Int i2) -> (Int (if i1 = i2 then 1 else 0), env, eta_new2, dfa_list)
            | ("<", Int i1, Int i2) -> (Int (if i1 < i2 then 1 else 0), env, eta_new2, dfa_list)          
            | (_,_,_) -> failwith("unexpected")
          end
  | If(e1, e2, e3) -> let (xval, env, eta_new, dfa_list) = eval e1 env eta dfa_list in
     begin
     match xval with 
     | Int 0 -> eval e3 env eta_new dfa_list
     | Int _ -> eval e2 env eta_new dfa_list
     | _     -> failwith "eval If"
     end

  | Let(s,e1,e2) -> let (xval, env, eta_new, dfa_list) = 
                      eval e1 env eta dfa_list in
                        let env_new = (s,xval)::env in
                          eval e2 env_new eta_new dfa_list
  | Fun(s,expr) -> (Closure (s, expr, env), env, eta, dfa_list)
  | FunR(f, i, fBody) -> (RecClosure (f,i,fBody,env), env, eta, dfa_list)
  | Letrec(f, i, fBody, letBody) ->
    let (rval,a1,eta_new, dfa_list)= eval (FunR(f, i, fBody)) env eta dfa_list in
      let benv =(f,rval)::env
        in eval letBody benv eta_new dfa_list 
  | Seq(e1, e2) -> let (xval, env, eta_new, dfa_list) = eval e1 env eta dfa_list in
      eval e2 env eta_new dfa_list
  | Call(eFun, eArg) -> let (fClosure, _, _, _) = eval eFun env eta dfa_list in 
      begin match fClosure with
        | Closure (x, fBody, fDeclEnv) ->
          let (xVal, env, eta_new, dfa_list) = eval eArg env eta dfa_list in
            let env_new = (x, xVal) :: fDeclEnv
              in eval fBody env_new eta_new dfa_list
        | RecClosure(f, p, e3, fdecEnv) ->
          let (aVal,a2,eta_new, dfa_list) = eval eArg env eta dfa_list in
            let rEnv =(f,fClosure)::fdecEnv in 
              let aenv =(p,aVal)::rEnv in 
                eval e3 aenv eta_new dfa_list
        | _ -> failwith("errore non e' una closure")
      end
  | Read(s) -> let eta_new = eta^"r" in
      if (checkAcceptsAll eta_new dfa_list) then (Int(0), env, eta_new, dfa_list) 
      else raise (Denied "Read non permessa")
  | Write(s) -> let eta_new = eta^"w" in 
      if (checkAcceptsAll eta_new dfa_list) then (Int(1), env, eta_new, dfa_list)
      else raise (Denied "Write non permessa")
  | Open(s) -> let eta_new = eta^"o" in 
      if (checkAcceptsAll eta_new dfa_list) then (Int(2), env, eta_new, dfa_list)
      else raise (Denied "Open non permessa")
  | Phi(dfa, e) -> eval e env eta (dfa::dfa_list) 
  | UserPolicy(p,e) -> let trans = (generate_transition p) in 
    let new_policy =
				{
				states = [0; 1; 2];
				sigma = ['r';'w';'o'];
				start = 0;
				transitions = trans;
				accepting = [0;1]
				} in eval e env eta (new_policy::dfa_list) (* valuto poi l'espressione con la pila delle politiche aggiornata *)
  | _ -> failwith ("unexpected error")
;;

let rec pval (p : proc) env (eta:string) (dfa_list:dfa list) = match p with
    | Proc(e_list) -> match e_list with
        | [hd] -> let (v1, _, _, _) = eval hd env eta dfa_list in v1::[]
        | head::tail -> let (v1, _, hist, _) = eval head env eta dfa_list in v1::(pval (Proc(tail)) env hist dfa_list)
        | _ -> failwith("unexpected")
    ;;

(* Reverse Chinese Wall *)
let noWaR:dfa =
  { states = [0;1;2];
    sigma = ['r';'w';'o'];
    start = 0;
    transitions = [
      (0,'w',0);
      (0,'o',0);
      (0,'r',1);
      (1,'r',1);
      (1,'o',1);
      (1,'w',2);
      (2,'w',2);
      (2,'o',2);
      (2,'r',2)
    ];
    accepting = [0;1]
  };;
(* No open after write *)
let noOaW:dfa =
  { states = [0;1;2];
    sigma = ['r';'w';'o'];
    start = 0;
    transitions = [
      (0,'o',0);
      (0,'r',0);
      (0,'w',1);
      (1,'w',1);
      (1,'r',1);
      (1,'o',2);
      (2,'o',2);
      (2,'r',2);
      (2,'w',2)
    ];
    accepting = [0;1]
  };;
  (* No Read after Open*)
let noRaO:dfa =
  { states = [0;1;2];
    sigma = ['r';'w';'o'];
    start = 0;
    transitions = [
      (0,'r',0);
      (0,'w',0);
      (0,'o',1);
      (1,'o',1);
      (1,'w',1);
      (1,'r',2);
      (2,'r',2);
      (2,'w',2);
      (2,'o',2)
    ];
    accepting = [0;1]
  };;
(* Void policy *)
let void_policy:dfa =
  { states = [0];
    sigma = ['r';'w';'o'];
    start = 0;
    transitions = [
      (0,'r',0);
      (0,'w',0);
      (0,'o',0);
    ];
    accepting = [0]
  };;

(* test 1*)

let first_test : proc = Proc([Phi(noOaW, Let("x", Write("file"), Open("file")))]);;  (* la politica e' NO OPEN AFTER WRITE *)

pval first_test [] "" [];;

(* test 2.1
let second_test_1 : proc = Proc([Let("x", Read("file"), Read("file")); 
Phi(void_policy, Let("x", Read("file"), Open("file"))); Phi(noWaR, Seq(CstI(0), Phi(noRaO, Let("x", Read("file"), Write("file")))))]);; 
 
pval second_test_1 [] "" [];;*)

(* test 2.2
let second_test_2 : proc = Proc([Let("x", Read("file"), Read("file")); 
Phi(void_policy, Let("x", Read("file"), Open("file"))); Phi(noWaR, Seq(CstI(0), Phi(noRaO, Let("x", Write("file"), Read("file")))))]);;

pval second_test_2 [] "" [];;*)

(* test 3 
let third_test : proc = Proc([Phi(noWaR, Let("x", Write("file"), Read("file")));  (* la politica e' NO WRITE AFTER READ *)
Phi(void_policy, Write("file")); Letrec("fact", "n",
If(Prim("=",Var("n"),CstI(0)),CstI(1),Prim("*",Var("n"),Call(Var("fact"),Prim("-",Var("n"),CstI(1))))),Call(Var("fact"),CstI(6)));]);; 

pval third_test [] "" [];;*)

(*test 4 
let fourth_test : proc = Proc([ Open("file"); UserPolicy("nRaO",Seq(Let("x", Write("file"), Write("file")), If(Prim("=",Write("file"),CstI(1)), Read("file"), Write("file") )))]);;  

pval fourth_test [] "" [];;*)

(*test 5
let fourth_test : proc = Proc([UserPolicy("nOaR",If(Prim("=",Read("file"),CstI(1)), Read("file"), Open("file") ))]);;

pval fourth_test [] "" [];;*)