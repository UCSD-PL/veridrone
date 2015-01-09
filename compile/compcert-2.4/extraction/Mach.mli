open AST
open BinNums
open Datatypes
open Integers
open Machregs
open Op

type label = positive

type instruction =
| Mgetstack of Int.int * typ * mreg
| Msetstack of mreg * Int.int * typ
| Mgetparam of Int.int * typ * mreg
| Mop of operation * mreg list * mreg
| Mload of memory_chunk * addressing * mreg list * mreg
| Mstore of memory_chunk * addressing * mreg list * mreg
| Mcall of signature * (mreg, ident) sum
| Mtailcall of signature * (mreg, ident) sum
| Mbuiltin of external_function * mreg list * mreg list
| Mannot of external_function * annot_param list
| Mlabel of label
| Mgoto of label
| Mcond of condition * mreg list * label
| Mjumptable of mreg * label list
| Mreturn
and annot_param =
| APreg of mreg
| APstack of memory_chunk * coq_Z

type code = instruction list

type coq_function = { fn_sig : signature; fn_code : code;
                      fn_stacksize : coq_Z; fn_link_ofs : Int.int;
                      fn_retaddr_ofs : Int.int }

val fn_sig : coq_function -> signature

val fn_code : coq_function -> code

val fn_stacksize : coq_function -> coq_Z

val fn_link_ofs : coq_function -> Int.int

val fn_retaddr_ofs : coq_function -> Int.int

type fundef = coq_function AST.fundef

type program = (fundef, unit) AST.program

