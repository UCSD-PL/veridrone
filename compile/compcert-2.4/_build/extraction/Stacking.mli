open AST
open BinInt
open BinNums
open Bounds
open Conventions1
open Coqlib
open Datatypes
open Errors
open Integers
open Linear
open Lineartyping
open List0
open Locations
open Mach
open Machregs
open Op
open Stacklayout

type frame_index =
| FI_link
| FI_retaddr
| FI_local of coq_Z * typ
| FI_arg of coq_Z * typ
| FI_saved_int of coq_Z
| FI_saved_float of coq_Z

val offset_of_index : frame_env -> frame_index -> coq_Z

val save_callee_save_reg :
  (frame_env -> coq_Z) -> (mreg -> coq_Z) -> (coq_Z -> frame_index) -> typ ->
  frame_env -> mreg -> code -> instruction list

val save_callee_save_regs :
  (frame_env -> coq_Z) -> (mreg -> coq_Z) -> (coq_Z -> frame_index) -> typ ->
  frame_env -> mreg list -> code -> code

val save_callee_save_int : frame_env -> code -> code

val save_callee_save_float : frame_env -> code -> code

val save_callee_save : frame_env -> code -> code

val restore_callee_save_reg :
  (frame_env -> coq_Z) -> (mreg -> coq_Z) -> (coq_Z -> frame_index) -> typ ->
  frame_env -> mreg -> code -> instruction list

val restore_callee_save_regs :
  (frame_env -> coq_Z) -> (mreg -> coq_Z) -> (coq_Z -> frame_index) -> typ ->
  frame_env -> mreg list -> code -> code

val restore_callee_save_int : frame_env -> code -> code

val restore_callee_save_float : frame_env -> code -> code

val restore_callee_save : frame_env -> code -> code

val transl_op : frame_env -> operation -> operation

val transl_addr : frame_env -> addressing -> addressing

val transl_annot_param : frame_env -> loc -> annot_param

val transl_instr : frame_env -> Linear.instruction -> code -> code

val transl_code : frame_env -> Linear.instruction list -> code

val transl_body : Linear.coq_function -> frame_env -> code

val transf_function : Linear.coq_function -> coq_function res

val transf_fundef : Linear.fundef -> fundef res

val transf_program : Linear.program -> program res

