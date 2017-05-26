(*	Sketch of a graph-based evaluation of lambda terms

	Author: Beniamino Accattoli and Bruno Barras *)

let verb = ref false
  
let gensym =
  let n = ref 0 in
  fun x -> let y = x^"_"^string_of_int !n in incr n; y

(* Definition of terms *)

type term = 
     Var of var 		(* Variable Occurrences*)
  |  App of term * term        	(* Appications *)
  |  Lam of var * term		(* Abstractions *)
and var = {name:string; mutable subs:subs}
and subs = Subs of term | Copy of var | NotSub
(* boolean is true exclusively for graph operation substitutions *)

let alloc = ref 0
let beta = ref 0
let reset () = alloc:=0; beta:=0
let with_stats f x =
  reset();
  let v = f x in
  Printf.printf "alloc: %d; beta: %d\n" !alloc !beta;
  v

let mkvar x = incr alloc; {name=gensym x; subs=NotSub}
let release_var v =
  if !verb then prerr_endline ("release: "^v.name);
  v.subs <- NotSub
let subs_var v t =
  if !verb then prerr_endline ("subs_var: "^v.name);
  assert (v.subs = NotSub);
  incr beta;
  v.subs <- Subs t
let copy_var v x =
  if !verb then prerr_endline ("copy_var: "^v.name^" --> "^x.name);
  assert (v.subs = NotSub);
  v.subs <- Copy x

(* Graph copy of a term *)
(* No need to copy arguments, that will go through the stack and env,
   and will be copyied when taken out of env. *)
let copy_args = ref false
let rec copy hd t =
  match t with
  | App(u,v) -> App(copy hd u, copy !copy_args v)
  | Lam(x,u) ->
     if hd then begin
       (* create new cell with fresh name *)
       let y = mkvar x.name in
       (* substitute it for the old var *)
       copy_var x y;
       (* copy recursively *)
       let uy = copy hd u in
       (* restore old variable *)
       release_var x;
       Lam(y,uy)
     end else
       Lam(x,copy hd u)
  | Var{subs=Copy v} -> Var v
  | Var _ -> t
let copy_lin = copy true
     
let rec copy1 rnm t =
  match t with
  | App(u,v) -> App(copy1 rnm u, copy1 rnm v)
  | Lam(x,u) ->
     let y = mkvar x.name in
     let uy = copy1 ((x,y)::rnm) u in
     Lam(y,uy)
  | Var x ->
     (try Var (List.assq x rnm)
      with Not_found -> t)
let copy_nsqr = copy1 []

module Ren = Map.Make(struct type t=var let compare=compare end)
let rec copy2 rnm t =
  match t with
  | App(u,v) -> App(copy2 rnm u, copy2 rnm v)
  | Lam(x,u) ->
     let y = mkvar x.name in
     let uy = copy2 (Ren.add x y rnm) u in
     Lam(y,uy)
  | Var x ->
     (try Var (Ren.find x rnm)
      with Not_found -> t)
let copy_nlogn = copy2 Ren.empty

let copy = copy_lin
  
(* Milner Abstract Machine *)
     
type state = term * term list
       
let rec mam (st:state) : state =
  match st with
  (* commutative step *)
  | App(u,v),          stk -> mam (u,v::stk)
  (* exponential step *)
  | Var{subs=Subs t0}, stk -> mam (copy t0,stk)
  (* multiplicative step *)
  | Lam(x, u), (v::stk) ->
     subs_var x v;
    mam (u,stk)
  (* final states *)
  | Var{subs=Copy _},_ -> assert false
  | (Lam _, [] | Var _, _) -> st



(* Examples *)
let lam x f =
  let var = mkvar x in
  Lam(var,f (Var var))
let app x l = List.fold_left (fun h a -> App(h,a)) x l

let t =
    let z = Var(mkvar"z") in
    lam"x"(fun x -> app x [lam"y"(fun y -> app z[y;x])])

let ze = lam"x"(fun x->lam"y"(fun y->x))
let su n = lam"x"(fun x->lam"y"(fun y->app y [app n [x;y]]))
let plus m n = app m [n;lam "n"su]
let mult m n = app m [ze;lam "h"(fun h -> plus n h)]

let eval_num t =
  let z = mkvar "0" in
  let s = mkvar "S" in
  let rec dec acc st =
    match st with
    | (Var v,[]) when v==z -> acc
    | (Var v,[n]) when v==s -> dec (acc+1) (mam(copy n,[]))
    | _ -> failwith "ill-typed" in
  with_stats
    (dec 0) (mam(copy t,[Var z;Var s]))

let _ = eval_num(plus (su(su ze)) (su ze))
let _ = eval_num(mult (su ze) (su ze))
let _ = eval_num(mult (su(su(su ze))) (su(su ze)))
