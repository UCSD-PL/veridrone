open AST
open BinNums
open Coqlib
open Op

type mreg =
| AX
| BX
| CX
| DX
| SI
| DI
| BP
| X0
| X1
| X2
| X3
| X4
| X5
| X6
| X7
| FP0

val mreg_eq : mreg -> mreg -> bool

val mreg_type : mreg -> typ

module IndexedMreg : 
 sig 
  type t = mreg
  
  val eq : mreg -> mreg -> bool
  
  val index : mreg -> positive
 end

val is_stack_reg : mreg -> bool

val destroyed_by_op : operation -> mreg list

val destroyed_by_load : memory_chunk -> addressing -> mreg list

val destroyed_by_store : memory_chunk -> addressing -> mreg list

val destroyed_by_cond : condition -> mreg list

val destroyed_by_jumptable : mreg list

val builtin_write16_reversed : ident

val builtin_write32_reversed : ident

val destroyed_by_builtin : external_function -> mreg list

val destroyed_at_function_entry : mreg list

val destroyed_by_setstack : typ -> mreg list

val temp_for_parent_frame : mreg

val mregs_for_operation : operation -> mreg option list * mreg option

val builtin_negl : ident

val builtin_addl : ident

val builtin_subl : ident

val builtin_mull : ident

val mregs_for_builtin :
  external_function -> mreg option list * mreg option list

val two_address_op : operation -> bool

