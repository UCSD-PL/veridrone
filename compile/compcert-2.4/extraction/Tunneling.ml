open AST
open Datatypes
open LTL
open List0
open Maps
open UnionFind

module U = UF(PTree)

(** val record_goto : U.t -> node -> bblock -> U.t **)

let record_goto uf pc = function
| [] -> uf
| i :: l ->
  (match i with
   | Lbranch s -> U.union uf pc s
   | _ -> uf)

(** val record_gotos : coq_function -> U.t **)

let record_gotos f =
  PTree.fold record_goto f.fn_code U.empty

(** val tunnel_instr : U.t -> instruction -> instruction **)

let tunnel_instr uf i = match i with
| Lbranch s -> Lbranch (U.repr uf s)
| Lcond (cond, args, s1, s2) ->
  Lcond (cond, args, (U.repr uf s1), (U.repr uf s2))
| Ljumptable (arg, tbl) -> Ljumptable (arg, (map (U.repr uf) tbl))
| _ -> i

(** val tunnel_block : U.t -> bblock -> bblock **)

let tunnel_block uf b =
  map (tunnel_instr uf) b

(** val tunnel_function : coq_function -> coq_function **)

let tunnel_function f =
  let uf = record_gotos f in
  { fn_sig = f.fn_sig; fn_stacksize = f.fn_stacksize; fn_code =
  (PTree.map1 (tunnel_block uf) f.fn_code); fn_entrypoint =
  (U.repr uf f.fn_entrypoint) }

(** val tunnel_fundef : fundef -> fundef **)

let tunnel_fundef f =
  transf_fundef tunnel_function f

(** val tunnel_program : program -> program **)

let tunnel_program p =
  transform_program tunnel_fundef p

