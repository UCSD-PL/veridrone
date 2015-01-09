open AST
open BinNums
open Floats
open Integers
open Op
open Registers
open ValueDomain

type cond_strength_reduction_cases =
| Coq_cond_strength_reduction_case1 of comparison * reg * reg * Int.int
   * aval
| Coq_cond_strength_reduction_case2 of comparison * reg * reg * aval
   * Int.int
| Coq_cond_strength_reduction_case3 of comparison * reg * reg * Int.int
   * aval
| Coq_cond_strength_reduction_case4 of comparison * reg * reg * aval
   * Int.int
| Coq_cond_strength_reduction_default of condition * reg list * aval list

val cond_strength_reduction_match :
  condition -> reg list -> aval list -> cond_strength_reduction_cases

val cond_strength_reduction :
  condition -> reg list -> aval list -> condition * reg list

val make_cmp_base :
  condition -> reg list -> aval list -> operation * reg list

type make_cmp_cases =
| Coq_make_cmp_case1 of Int.int * reg * aval
| Coq_make_cmp_case2 of Int.int * reg * aval
| Coq_make_cmp_default of condition * reg list * aval list

val make_cmp_match : condition -> reg list -> aval list -> make_cmp_cases

val make_cmp : condition -> reg list -> aval list -> operation * reg list

type addr_strength_reduction_cases =
| Coq_addr_strength_reduction_case1 of Int.int * reg * ident * Int.int
| Coq_addr_strength_reduction_case2 of Int.int * reg * Int.int
| Coq_addr_strength_reduction_case3 of Int.int * reg * reg * ident * 
   Int.int * Int.int
| Coq_addr_strength_reduction_case4 of Int.int * reg * reg * Int.int * 
   ident * Int.int
| Coq_addr_strength_reduction_case5 of Int.int * reg * reg * Int.int
   * Int.int
| Coq_addr_strength_reduction_case6 of Int.int * reg * reg * Int.int
   * Int.int
| Coq_addr_strength_reduction_case7 of Int.int * reg * reg * ident * 
   Int.int * aval
| Coq_addr_strength_reduction_case8 of Int.int * reg * reg * aval * ident
   * Int.int
| Coq_addr_strength_reduction_case9 of Int.int * reg * reg * Int.int * aval
| Coq_addr_strength_reduction_case10 of Int.int * reg * reg * aval * Int.int
| Coq_addr_strength_reduction_case11 of Int.int * Int.int * reg * reg * 
   ident * Int.int * Int.int
| Coq_addr_strength_reduction_case12 of Int.int * Int.int * reg * reg * 
   ident * Int.int * aval
| Coq_addr_strength_reduction_case13 of Int.int * Int.int * reg * reg * 
   aval * Int.int
| Coq_addr_strength_reduction_case14 of ident * Int.int * reg * Int.int
| Coq_addr_strength_reduction_case15 of Int.int * ident * Int.int * reg
   * Int.int
| Coq_addr_strength_reduction_default of addressing * reg list * aval list

val addr_strength_reduction_match :
  addressing -> reg list -> aval list -> addr_strength_reduction_cases

val addr_strength_reduction :
  addressing -> reg list -> aval list -> addressing * reg list

val make_addimm : Int.int -> reg -> operation * reg list

val make_shlimm : Int.int -> reg -> reg -> operation * reg list

val make_shrimm : Int.int -> reg -> reg -> operation * reg list

val make_shruimm : Int.int -> reg -> reg -> operation * reg list

val make_mulimm : Int.int -> reg -> operation * reg list

val make_andimm : Int.int -> reg -> aval -> operation * reg list

val make_orimm : Int.int -> reg -> operation * reg list

val make_xorimm : Int.int -> reg -> operation * reg list

val make_divimm : Int.int -> reg -> reg -> operation * reg list

val make_divuimm : Int.int -> reg -> reg -> operation * reg list

val make_moduimm : Int.int -> reg -> reg -> operation * reg list

val make_mulfimm : float -> reg -> reg -> reg -> operation * reg list

val make_mulfsimm : float32 -> reg -> reg -> reg -> operation * reg list

val make_cast8signed : reg -> aval -> operation * reg list

val make_cast8unsigned : reg -> aval -> operation * reg list

val make_cast16signed : reg -> aval -> operation * reg list

val make_cast16unsigned : reg -> aval -> operation * reg list

type op_strength_reduction_cases =
| Coq_op_strength_reduction_case1 of reg * aval
| Coq_op_strength_reduction_case2 of reg * aval
| Coq_op_strength_reduction_case3 of reg * aval
| Coq_op_strength_reduction_case4 of reg * aval
| Coq_op_strength_reduction_case5 of reg * reg * aval * Int.int
| Coq_op_strength_reduction_case6 of reg * reg * Int.int * aval
| Coq_op_strength_reduction_case7 of reg * reg * aval * Int.int
| Coq_op_strength_reduction_case8 of reg * reg * aval * Int.int
| Coq_op_strength_reduction_case9 of reg * reg * aval * Int.int
| Coq_op_strength_reduction_case10 of reg * reg * aval * Int.int
| Coq_op_strength_reduction_case11 of reg * reg * Int.int * aval
| Coq_op_strength_reduction_case12 of reg * reg * aval * Int.int
| Coq_op_strength_reduction_case13 of Int.int * reg * aval
| Coq_op_strength_reduction_case14 of reg * reg * Int.int * aval
| Coq_op_strength_reduction_case15 of reg * reg * aval * Int.int
| Coq_op_strength_reduction_case16 of reg * reg * Int.int * aval
| Coq_op_strength_reduction_case17 of reg * reg * aval * Int.int
| Coq_op_strength_reduction_case18 of reg * reg * aval * Int.int
| Coq_op_strength_reduction_case19 of reg * reg * aval * Int.int
| Coq_op_strength_reduction_case20 of reg * reg * aval * Int.int
| Coq_op_strength_reduction_case21 of addressing * reg list * aval list
| Coq_op_strength_reduction_case22 of condition * reg list * aval list
| Coq_op_strength_reduction_case23 of reg * reg * aval * float
| Coq_op_strength_reduction_case24 of reg * reg * float * aval
| Coq_op_strength_reduction_case25 of reg * reg * aval * float32
| Coq_op_strength_reduction_case26 of reg * reg * float32 * aval
| Coq_op_strength_reduction_default of operation * reg list * aval list

val op_strength_reduction_match :
  operation -> reg list -> aval list -> op_strength_reduction_cases

val op_strength_reduction :
  operation -> reg list -> aval list -> operation * reg list

