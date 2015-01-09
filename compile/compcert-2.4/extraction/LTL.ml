open AST
open BinNums
open Datatypes
open Locations
open Machregs
open Maps
open Op

type node = positive

type instruction =
| Lop of operation * mreg list * mreg
| Lload of memory_chunk * addressing * mreg list * mreg
| Lgetstack of slot * coq_Z * typ * mreg
| Lsetstack of mreg * slot * coq_Z * typ
| Lstore of memory_chunk * addressing * mreg list * mreg
| Lcall of signature * (mreg, ident) sum
| Ltailcall of signature * (mreg, ident) sum
| Lbuiltin of external_function * mreg list * mreg list
| Lannot of external_function * loc list
| Lbranch of node
| Lcond of condition * mreg list * node * node
| Ljumptable of mreg * node list
| Lreturn

type bblock = instruction list

type code = bblock PTree.t

type coq_function = { fn_sig : signature; fn_stacksize : coq_Z;
                      fn_code : code; fn_entrypoint : node }

(** val fn_sig : coq_function -> signature **)

let fn_sig x = x.fn_sig

(** val fn_stacksize : coq_function -> coq_Z **)

let fn_stacksize x = x.fn_stacksize

(** val fn_code : coq_function -> code **)

let fn_code x = x.fn_code

(** val fn_entrypoint : coq_function -> node **)

let fn_entrypoint x = x.fn_entrypoint

type fundef = coq_function AST.fundef

type program = (fundef, unit) AST.program

(** val destroyed_by_getstack : slot -> mreg list **)

let destroyed_by_getstack = function
| Incoming -> temp_for_parent_frame :: []
| _ -> []

(** val successors_block : bblock -> node list **)

let rec successors_block = function
| [] -> []
| instr :: b' ->
  (match instr with
   | Ltailcall (sg, ros) -> []
   | Lbranch s -> s :: []
   | Lcond (cond, args, s1, s2) -> s1 :: (s2 :: [])
   | Ljumptable (arg, tbl) -> tbl
   | Lreturn -> []
   | _ -> successors_block b')

