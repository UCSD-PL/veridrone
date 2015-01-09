open AST
open BinInt
open BinNums
open Conventions1
open Datatypes
open Linear
open List0
open Locations
open Machregs

type bounds = { bound_local : coq_Z; bound_int_callee_save : coq_Z;
                bound_float_callee_save : coq_Z; bound_outgoing : coq_Z;
                bound_stack_data : coq_Z }

val bound_local : bounds -> coq_Z

val bound_int_callee_save : bounds -> coq_Z

val bound_float_callee_save : bounds -> coq_Z

val bound_outgoing : bounds -> coq_Z

val bound_stack_data : bounds -> coq_Z

val regs_of_instr : instruction -> mreg list

val slots_of_locs : loc list -> ((slot * coq_Z) * typ) list

val slots_of_instr : instruction -> ((slot * coq_Z) * typ) list

val max_over_list : ('a1 -> coq_Z) -> 'a1 list -> coq_Z

val max_over_instrs : coq_function -> (instruction -> coq_Z) -> coq_Z

val max_over_regs_of_instr : (mreg -> coq_Z) -> instruction -> coq_Z

val max_over_slots_of_instr :
  (((slot * coq_Z) * typ) -> coq_Z) -> instruction -> coq_Z

val max_over_regs_of_funct : coq_function -> (mreg -> coq_Z) -> coq_Z

val max_over_slots_of_funct :
  coq_function -> (((slot * coq_Z) * typ) -> coq_Z) -> coq_Z

val int_callee_save : mreg -> coq_Z

val float_callee_save : mreg -> coq_Z

val local_slot : ((slot * coq_Z) * typ) -> coq_Z

val outgoing_slot : ((slot * coq_Z) * typ) -> coq_Z

val outgoing_space : instruction -> coq_Z

val function_bounds : coq_function -> bounds

