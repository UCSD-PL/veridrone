open AST
open BinNums
open BinPos
open Datatypes
open List0
open Maps
open Op
open Registers

type node = positive

type instruction =
| Inop of node
| Iop of operation * reg list * reg * node
| Iload of memory_chunk * addressing * reg list * reg * node
| Istore of memory_chunk * addressing * reg list * reg * node
| Icall of signature * (reg, ident) sum * reg list * reg * node
| Itailcall of signature * (reg, ident) sum * reg list
| Ibuiltin of external_function * reg list * reg * node
| Icond of condition * reg list * node * node
| Ijumptable of reg * node list
| Ireturn of reg option

type code = instruction PTree.t

type coq_function = { fn_sig : signature; fn_params : reg list;
                      fn_stacksize : coq_Z; fn_code : code;
                      fn_entrypoint : node }

(** val fn_sig : coq_function -> signature **)

let fn_sig x = x.fn_sig

(** val fn_params : coq_function -> reg list **)

let fn_params x = x.fn_params

(** val fn_stacksize : coq_function -> coq_Z **)

let fn_stacksize x = x.fn_stacksize

(** val fn_code : coq_function -> code **)

let fn_code x = x.fn_code

(** val fn_entrypoint : coq_function -> node **)

let fn_entrypoint x = x.fn_entrypoint

type fundef = coq_function AST.fundef

type program = (fundef, unit) AST.program

(** val transf_function :
    (node -> instruction -> instruction) -> coq_function -> coq_function **)

let transf_function transf f =
  { fn_sig = f.fn_sig; fn_params = f.fn_params; fn_stacksize =
    f.fn_stacksize; fn_code = (PTree.map transf f.fn_code); fn_entrypoint =
    f.fn_entrypoint }

(** val successors_instr : instruction -> node list **)

let successors_instr = function
| Inop s -> s :: []
| Iop (op, args, res, s) -> s :: []
| Iload (chunk, addr, args, dst, s) -> s :: []
| Istore (chunk, addr, args, src, s) -> s :: []
| Icall (sig0, ros, args, res, s) -> s :: []
| Ibuiltin (ef, args, res, s) -> s :: []
| Icond (cond, args, ifso, ifnot) -> ifso :: (ifnot :: [])
| Ijumptable (arg, tbl) -> tbl
| _ -> []

(** val successors_map : coq_function -> node list PTree.t **)

let successors_map f =
  PTree.map1 successors_instr f.fn_code

(** val instr_uses : instruction -> reg list **)

let instr_uses = function
| Inop s -> []
| Iop (op, args, res, s) -> args
| Iload (chunk, addr, args, dst, s) -> args
| Istore (chunk, addr, args, src, s) -> src :: args
| Icall (sig0, s0, args, res, s) ->
  (match s0 with
   | Coq_inl r -> r :: args
   | Coq_inr id -> args)
| Itailcall (sig0, s, args) ->
  (match s with
   | Coq_inl r -> r :: args
   | Coq_inr id -> args)
| Ibuiltin (ef, args, res, s) -> args
| Icond (cond, args, ifso, ifnot) -> args
| Ijumptable (arg, tbl) -> arg :: []
| Ireturn o ->
  (match o with
   | Some arg -> arg :: []
   | None -> [])

(** val instr_defs : instruction -> reg option **)

let instr_defs = function
| Iop (op, args, res, s) -> Some res
| Iload (chunk, addr, args, dst, s) -> Some dst
| Icall (sig0, ros, args, res, s) -> Some res
| Ibuiltin (ef, args, res, s) -> Some res
| _ -> None

(** val max_pc_function : coq_function -> positive **)

let max_pc_function f =
  PTree.fold (fun m pc i -> Pos.max m pc) f.fn_code Coq_xH

(** val max_reg_instr : positive -> node -> instruction -> positive **)

let max_reg_instr m pc = function
| Inop s -> m
| Iop (op, args, res, s) -> fold_left Pos.max args (Pos.max res m)
| Iload (chunk, addr, args, dst, s) -> fold_left Pos.max args (Pos.max dst m)
| Istore (chunk, addr, args, src, s) ->
  fold_left Pos.max args (Pos.max src m)
| Icall (sig0, s0, args, res, s) ->
  (match s0 with
   | Coq_inl r -> fold_left Pos.max args (Pos.max r (Pos.max res m))
   | Coq_inr id -> fold_left Pos.max args (Pos.max res m))
| Itailcall (sig0, s, args) ->
  (match s with
   | Coq_inl r -> fold_left Pos.max args (Pos.max r m)
   | Coq_inr id -> fold_left Pos.max args m)
| Ibuiltin (ef, args, res, s) -> fold_left Pos.max args (Pos.max res m)
| Icond (cond, args, ifso, ifnot) -> fold_left Pos.max args m
| Ijumptable (arg, tbl) -> Pos.max arg m
| Ireturn o ->
  (match o with
   | Some arg -> Pos.max arg m
   | None -> m)

(** val max_reg_function : coq_function -> positive **)

let max_reg_function f =
  Pos.max (PTree.fold max_reg_instr f.fn_code Coq_xH)
    (fold_left Pos.max f.fn_params Coq_xH)

