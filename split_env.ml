(* Evaluation of lambda terms using abstract machines with
   split environments.

   Author: Beniamino Accattoli and Bruno Barras *)

(* Local env operations *)
module type LocalEnv =
sig
  type 'a t
  val empty : 'a t
  val push : 'a -> 'a t -> 'a t
  val access : int -> 'a t -> 'a
end

(* Local env implemented by lists *)
module LE : LocalEnv = struct
  type 'a t = 'a list
  let empty = []
  let push c e = c::e
  let access n e = List.nth e n
end

(* Local env implemented by Okasaki's random access lists *)
module FL : LocalEnv = struct
  type 'a tr = Leaf of 'a | Node of 'a * 'a tr * 'a tr
  type 'a t = (int * 'a tr) list
  let empty = []
  let push c e =
    match e with
    | (n1,t1)::(n2,t2)::e' when n1=n2 ->
	 (1+2*n1,Node(c,t1,t2))::e'
    | _ -> (1,Leaf c)::e
  let rec acc_tr n sz t =
    match t with
    | Leaf x -> x
    | Node (x,t1,t2) ->
    if n=0 then x else
      let sz' = sz/2 in
      if n <= sz'
      then acc_tr (n-1) sz' t1
      else acc_tr (n-sz'-1) sz' t2
  let rec access n e =
    match e with
    | (n1,t1)::e' when n<n1 -> acc_tr n n1 t1
    | (n1,_)::e' -> access (n-n1) e'
    | [] -> raise Not_found
end

module Env = FL
let one v = Env.push v Env.empty
  
(* Definition of terms: de Bruijn indices *)
    
type term = 
     Var of int             (* Variable occurrences*)
  |  App of term * term     (* Appications *)
  |  Lam of string * term   (* Abstractions *)
 
(* Split-env Abstract Machines *)

      
(* local env: mapping from dB to pointers *)
type 'a env = 'a ptr Env.t
(* pointer: mutable cell holding a value (implements the global env) *)
and 'a ptr = 'a value ref
(* cell content *)
and 'a value = Box | Clos of (term * 'a env) | Neutr of 'a * 'a stack
(* stack of pending arguments *)
and 'a stack = (term * 'a env) list

(* call-by-name *)
  
let rec spam0 (st:term*'a env) : 'a value =
  match st with
  (* commutative step *)
  | App(u,v), e ->
     (match spam0(u,e) with
     | Clos(Lam(_,t),e') -> spam0(t,Env.push(ref(Clos(v,e)))e')
     | Clos _ -> assert false
     | Neutr(a,stk) -> Neutr(a,stk@[v,e])
     | Box -> assert false)
  (* exponential step *)
  | Var n, e ->
     (match !(Env.access n e) with
     | Clos(t,e') -> spam0(t,e')
     | v -> v)
  (* final states *)
  | (Lam _ as t, e) -> Clos(t,e)

type 'a state = term * 'a env * 'a stack

let rec spam (st:'a state) : 'a value =
  match st with
  (* commutative step *)
  | App(u,v), e, stk -> spam (u,e,(v,e)::stk)
  (* multiplicative step *)
  | Lam(_, u), e, (v::stk) ->
     spam(u,Env.push (ref (Clos v)) e,stk)
  (* exponential step *)
  | Var n, e, stk ->
     (match !(Env.access n e) with
     | Clos(t,e') -> spam(t,e',stk)
     (* free var *)
     | Neutr(a,stk') -> Neutr(a,stk'@stk)
     | Box -> assert false)
  (* final states *)
  | (Lam _ as t, e, []) -> Clos(t,e)
     
(* call-by-need *)

(* Non tail-recursive version of the machine.
   Very close to call-by-name. *)
let rec splmad0 (st:'a state) : 'a value =
  match st with
  | App(u,v), e, stk -> splmad0 (u,e,(v,e)::stk)
  | Lam(_,u), e, (v::stk) ->
     splmad0 (u,Env.push(ref(Clos v)) e, stk)
  | Var n, e, stk ->
     let v =
       let p = Env.access n e in
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

type 'a dump = ('a ptr * 'a stack) list
type 'a dstate = term * 'a env * 'a stack * 'a dump

let rec splmad (st:'a dstate) : 'a value =
  match st with
  | App(u,v), e, stk, d -> splmad (u,e,(v,e)::stk,d)
  | Var n, e, stk, d ->
     let p = Env.access n e in 
     (match !p with
     | Clos(t,e') ->
	 p:=Box;
         splmad (t,e',[],(p,stk)::d)
     | Neutr(a,astk) ->
	let astk' =
          List.fold_left
            (fun astk (p',stk') -> p':=Neutr(a,astk); astk@stk')
            (astk@stk) d in
	Neutr(a,astk')
     | Box -> assert false)
  | Lam(_,u), e, (v::stk), d ->
     splmad (u,Env.push(ref(Clos v)) e, stk, d)
  | Lam _ as t, e, [], (p,stk)::d ->
     assert (!p=Box);
     p := Clos(t,e);
     splmad(t,e,stk,d)
  | (Lam _ as t, e, [], []) -> Clos(t,e)


(* Variation: identify values -> generate less updates *)

module SeparationThunkValue = struct

(* local env: mapping from dB to pointers *)
type 'a env = 'a ptr Env.t
(* pointer: mutable cell holding a value (implements the global env) *)
and 'a ptr = 'a thunk ref
(* cell content *)
and 'a thunk = Box | Clos of (term * 'a env) | Val of 'a value
and 'a value = Fun of string * term * 'a env | Neutr of 'a * 'a stack
(* stack of pending arguments *)
and 'a stack = (term * 'a env) list

(* call-by-name *)

type 'a state = term * 'a env * 'a stack

let rec spam (st:'a state) : 'a value =
  match st with
  (* commutative step *)
  | App(u,v), e, stk -> spam (u,e,(v,e)::stk)
  (* multiplicative step *)
  | Lam(_, u), e, (v::stk) ->
     spam(u,Env.push (ref (Clos v)) e,stk)
  (* exponential step *)
  | Var n, e, stk ->
     (match !(Env.access n e) with
     | Clos(t,e') -> spam(t,e',stk)
     | Val(Fun(x,u,e')) -> spam(Lam(x,u),e',stk)
     (* free var *)
     | Val(Neutr(a,stk')) -> Neutr(a,stk'@stk)
     | Box -> assert false)
  (* final states *)
  | (Lam(x,u), e, []) -> Fun(x,u,e)

type 'a dump = ('a ptr * 'a stack) list
type 'a dstate = term * 'a env * 'a stack * 'a dump

let rec splmad (st:'a dstate) : 'a value =
  match st with
  | App(u,v), e, stk, d -> splmad (u,e,(v,e)::stk,d)
  | Var n, e, stk, d ->
     let p = Env.access n e in 
     (match !p with
     | Clos(t,e') ->
	 p:=Box;
         splmad (t,e',[],(p,stk)::d)
     | Val(Fun(x,t,e')) -> splmad (Lam(x,t),e',stk,d)
     | Val(Neutr(a,astk)) ->
	let astk' =
          List.fold_left
            (fun astk (p',stk') -> p':=Val(Neutr(a,astk)); astk@stk')
            (astk@stk) d in
	Neutr(a,astk')
     | Box -> assert false)
  | Lam(_,u), e, (v::stk), d ->
     splmad (u,Env.push(ref(Clos v)) e, stk, d)
  | Lam _ as t, e, [], (p,stk)::d ->
     assert (!p=Box);
     p := Clos(t,e);
     splmad(t,e,stk,d)
  | (Lam(x,u), e, [], []) -> Fun(x,u,e)

end

(* Examples *)
type lam = int -> term
let lam x (f:lam->lam) : lam =
  fun k -> Lam(x, f (fun k' -> Var (k'-k-1)) (k+1))
let app (u:lam) (v:lam list) : lam =
  fun k -> List.fold_left (fun h a -> App(h,a k)) (u k) v
    
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
  let fv n = ref(Neutr(n,[])) in
  let env = Env.push (fv 0) (Env.push (fv 1) Env.empty) in
  let rec dec acc v =
    match v with
    | Neutr(0,[]) -> acc
    | Neutr(1,[n,e]) -> dec (acc+1) (!run n e)
    | _ -> failwith "ill-typed" in
  dec 0 (!run (App(App(t 0,Var 0),Var 1)) env)

(*let _ = run := run_spam0*)
let _ = eval_num(plus (su(su ze)) (su ze))
let _ = eval_num(mult (su ze) (su ze))
let _ = eval_num(mult (su(su(su ze))) (su(su ze)))

