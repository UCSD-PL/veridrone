open AST
open BinInt
open BinNums
open Datatypes
open Locations
open Machregs

val int_caller_save_regs : mreg list

val float_caller_save_regs : mreg list

val int_callee_save_regs : mreg list

val float_callee_save_regs : mreg list

val destroyed_at_call : mreg list

val dummy_int_reg : mreg

val dummy_float_reg : mreg

val index_int_callee_save : mreg -> coq_Z

val index_float_callee_save : mreg -> coq_Z

val loc_result : signature -> mreg list

val loc_arguments_rec : typ list -> coq_Z -> loc list

val loc_arguments : signature -> loc list

val size_arguments_rec : typ list -> coq_Z -> coq_Z

val size_arguments : signature -> coq_Z

