open AST
open BinNums
open Clight
open Cminor
open Cop
open Csharpminor
open Ctypes
open Datatypes
open Errors
open Floats
open Integers
open List0

val make_intconst : Int.int -> expr

val make_longconst : Int64.int -> expr

val make_floatconst : float -> expr

val make_singleconst : float32 -> expr

val make_singleoffloat : expr -> expr

val make_floatofsingle : expr -> expr

val make_floatofint : expr -> signedness -> expr

val make_singleofint : expr -> signedness -> expr

val make_intoffloat : expr -> signedness -> expr

val make_intofsingle : expr -> signedness -> expr

val make_longofint : expr -> signedness -> expr

val make_floatoflong : expr -> signedness -> expr

val make_singleoflong : expr -> signedness -> expr

val make_longoffloat : expr -> signedness -> expr

val make_longofsingle : expr -> signedness -> expr

val make_cmp_ne_zero : expr -> expr

val make_cast_int : expr -> intsize -> signedness -> expr

val make_cast : coq_type -> coq_type -> expr -> expr res

val make_boolean : expr -> coq_type -> expr

val make_notbool : expr -> coq_type -> expr res

val make_neg : expr -> coq_type -> expr res

val make_absfloat : expr -> coq_type -> expr res

val make_notint : expr -> coq_type -> expr res

val make_binarith :
  binary_operation -> binary_operation -> binary_operation ->
  binary_operation -> binary_operation -> binary_operation -> expr ->
  coq_type -> expr -> coq_type -> expr res

val make_add : expr -> coq_type -> expr -> coq_type -> expr res

val make_sub : expr -> coq_type -> expr -> coq_type -> expr res

val make_mul : expr -> coq_type -> expr -> coq_type -> expr res

val make_div : expr -> coq_type -> expr -> coq_type -> expr res

val make_binarith_int :
  binary_operation -> binary_operation -> binary_operation ->
  binary_operation -> expr -> coq_type -> expr -> coq_type -> expr res

val make_mod : expr -> coq_type -> expr -> coq_type -> expr res

val make_and : expr -> coq_type -> expr -> coq_type -> expr res

val make_or : expr -> coq_type -> expr -> coq_type -> expr res

val make_xor : expr -> coq_type -> expr -> coq_type -> expr res

val make_shl : expr -> coq_type -> expr -> coq_type -> expr res

val make_shr : expr -> coq_type -> expr -> coq_type -> expr res

val make_cmp : comparison -> expr -> coq_type -> expr -> coq_type -> expr res

val make_load : expr -> coq_type -> expr res

val make_memcpy : expr -> expr -> coq_type -> stmt

val make_store : expr -> coq_type -> expr -> stmt res

val transl_unop : Cop.unary_operation -> expr -> coq_type -> expr res

val transl_binop :
  Cop.binary_operation -> expr -> coq_type -> expr -> coq_type -> expr res

val transl_expr : Clight.expr -> expr res

val transl_lvalue : Clight.expr -> expr res

val transl_arglist : Clight.expr list -> typelist -> expr list res

val typlist_of_arglist : Clight.expr list -> typelist -> typ list

val transl_statement : coq_type -> nat -> nat -> statement -> stmt res

val transl_lbl_stmt :
  coq_type -> nat -> nat -> labeled_statements -> lbl_stmt res

val transl_var : (ident * coq_type) -> ident * coq_Z

val signature_of_function : Clight.coq_function -> signature

val transl_function : Clight.coq_function -> coq_function res

val transl_fundef : Clight.fundef -> fundef res

val transl_globvar : coq_type -> unit res

val transl_program : Clight.program -> program res

