open AST
open BinNums
open Datatypes
open Locations
open Machregs
open Op

type label = positive

type instruction =
| Lgetstack of slot * coq_Z * typ * mreg
| Lsetstack of mreg * slot * coq_Z * typ
| Lop of operation * mreg list * mreg
| Lload of memory_chunk * addressing * mreg list * mreg
| Lstore of memory_chunk * addressing * mreg list * mreg
| Lcall of signature * (mreg, ident) sum
| Ltailcall of signature * (mreg, ident) sum
| Lbuiltin of external_function * mreg list * mreg list
| Lannot of external_function * loc list
| Llabel of label
| Lgoto of label
| Lcond of condition * mreg list * label
| Ljumptable of mreg * label list
| Lreturn

type code = instruction list

type coq_function = { fn_sig : signature; fn_stacksize : coq_Z;
                      fn_code : code }

(** val fn_sig : coq_function -> signature **)

let fn_sig x = x.fn_sig

(** val fn_stacksize : coq_function -> coq_Z **)

let fn_stacksize x = x.fn_stacksize

(** val fn_code : coq_function -> code **)

let fn_code x = x.fn_code

type fundef = coq_function AST.fundef

type program = (fundef, unit) AST.program

