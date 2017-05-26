(* Evaluation of lambda terms using abstract machines with
   split environments.

   Author: Beniamino Accattoli and Bruno Barras *)

module Env = Map.Make(struct type t=string let compare=compare end)
let one (x, v) = Env.add x v Env.empty
  
(* Definition of terms: de Bruijn indices *)
    
type term = 
     Var of string          (* Variable occurrences*)
  |  App of term * term     (* Appications *)
  |  Lam of string * term   (* Abstractions *)
 
(* Split-env Abstract Machines *)

      
(* local env: mapping from dB to pointers *)
type env = ptr Env.t
(* pointer: mutable cell holding a value (implements the global env) *)
and ptr = value ref
(* cell content *)
and value = Box | Clos of (term * env) | Neutr of atom * stack
(* stack of pending arguments *)
and stack = (term * env) list
(* type of atoms: the machines are polymorphic w.r.t. this type *)
and atom = term * env

(* call-by-name *)

let rec spam0 (st:term*env) : value =
  match st with
  (* commutative step *)
  | App(u,v), e ->
     (match spam0(u,e) with
     | Clos(Lam(x,t),e') -> spam0(t,Env.add x (ref(Clos(v,e)))e')
     | Clos _ -> assert false
     | Neutr(a,stk) -> Neutr(a,stk@[v,e])
     | Box -> assert false)
  (* exponential step *)
  | Var x, e ->
     (match !(Env.find x e) with
     | Clos(t,e') -> spam0(t,e')
     | v -> v)
  (* final states *)
  | (Lam _ as t, e) -> Clos(t,e)

type state = term * env * stack

let rec spam (st:state) : value =
  match st with
  (* commutative step *)
  | App(u,v), e, stk -> spam (u,e,(v,e)::stk)
  (* multiplicative step *)
  | Lam(x, u), e, (v::stk) ->
     spam(u,Env.add x (ref (Clos v)) e,stk)
  (* exponential step *)
  | Var x, e, stk ->
     (match !(Env.find x e) with
     | Clos(t,e') -> spam(t,e',stk)
     (* free var *)
     | Neutr(a,stk') -> Neutr(a,stk'@stk)
     | Box -> assert false)
  (* final states *)
  | (Lam _ as t, e, []) -> Clos(t,e)

(* call-by-need *)

(* Non tail-recursive version of the machine.
   Very close to call-by-name. *)
let rec splmad0 (st:state) : value =
  match st with
  | App(u,v), e, stk -> splmad0 (u,e,(v,e)::stk)
  | Lam(x,u), e, (v::stk) ->
     splmad0 (u,Env.add x (ref(Clos v)) e, stk)
  | Var x, e, stk ->
     let v =
       let p = Env.find x e in
       match !p with
       | Clos(t,e') ->
	  p:=Box;
  	  let v = splmad0 (t,e',[]) in
	  assert (!p=Box);
	  p:=v;
	  v
       | v -> v in
     (match v with
     | Clos(t,e') -> splmad0(t,e',stk)
     | Neutr(a,stk') -> Neutr(a,stk'@stk)
     | Box -> assert false)
  | (Lam _ as t, e, []) -> Clos(t,e)

type dump = (ptr * stack) list
type dstate = term * env * stack * dump

let rec splmad (st:dstate) : value =
  match st with
  | App(u,v), e, stk, d -> splmad (u,e,(v,e)::stk,d)
  | Var x, e, stk, d ->
     let p = Env.find x e in 
     (match !p with
     | Clos(t,e') ->
	 p:=Box;
         splmad (t,e',[],(p,stk)::d)
     | Neutr(a,stk') ->
	let m = Neutr(a,stk'@stk) in
	(match d with
	| (p'',stk'')::d' -> p'':=m; splmad(Var "x",one ("x",p''),stk'',d')
	| [] -> m)
     | _ -> assert false)
  | Lam(x,u), e, (v::stk), d ->
     splmad (u,Env.add x (ref(Clos v)) e, stk, d)
  | Lam _ as t, e, [], (p,stk)::d ->
     assert (!p=Box);
     p := Clos(t,e);
     splmad(t,e,stk,d)
  | (Lam _ as t, e, [], []) -> Clos(t,e)

(* Examples *)
type lam = term
let lam x (f:lam->lam) : lam =
  Lam(x, f (Var x))
let app (u:lam) (v:lam list) : lam =
  List.fold_left (fun h a -> App(h,a)) u v
    
let ze = lam"x"(fun x->lam"y"(fun y-> x))
let su n = lam"x"(fun x->lam"y"(fun y-> app y [app n [x;y]]))
let plus m n = app m [n;lam "n"su]
let mult m n = app m [ze;lam "h"(fun h -> plus n h)]

let run_spam0 t e = spam0(t,e)
let run_spam t e = spam(t,e,[])
let run_splmad0 t e = splmad0(t,e,[])
let run_splmad t e = splmad(t,e,[],[])

let run = ref run_splmad

let eval_num (t:lam) =
  let fv x = ref(Neutr((Var x,Env.empty),[])) in
  let env = Env.add "0"(fv"0")(Env.add "S"(fv "S") Env.empty) in
  let rec dec acc v =
    match v with
    | Neutr((Var "0",_),[]) -> acc
    | Neutr((Var "S",_),[n,e]) -> dec (acc+1) (!run n e)
    | _ -> failwith "ill-typed" in
  dec 0 (!run (App(App(t,Var "0"),Var "S")) env)

(*let _ = run := run_spam*)
let _ = eval_num(plus (su(su ze)) (su ze))
let _ = eval_num(mult (su ze) (su ze))
let _ = eval_num(mult (su(su(su ze))) (su(su ze)))

