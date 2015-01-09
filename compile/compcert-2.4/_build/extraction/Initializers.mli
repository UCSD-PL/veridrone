open AST
open BinInt
open BinNums
open Cop
open Coqlib
open Csyntax
open Ctypes
open Datatypes
open Errors
open Integers
open Memory
open Values

val do_cast : coq_val -> coq_type -> coq_type -> coq_val res

val constval : expr -> coq_val res

type coq_initializer =
| Init_single of expr
| Init_array of initializer_list
| Init_struct of initializer_list
| Init_union of ident * coq_initializer
and initializer_list =
| Init_nil
| Init_cons of coq_initializer * initializer_list

val transl_init_single : coq_type -> expr -> init_data res

val padding : coq_Z -> coq_Z -> init_data list

val transl_init : coq_type -> coq_initializer -> init_data list res

val transl_init_array :
  coq_type -> initializer_list -> coq_Z -> init_data list res

val transl_init_struct :
  ident -> coq_type -> fieldlist -> initializer_list -> coq_Z -> init_data
  list res

