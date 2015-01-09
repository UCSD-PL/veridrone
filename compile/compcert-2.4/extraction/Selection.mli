open AST
open BinNums
open Cminor
open CminorSel
open Datatypes
open Errors
open Globalenvs
open Integers
open Op
open SelectDiv
open SelectLong
open SelectOp
open Switch

val condexpr_of_expr : expr -> condexpr

val load : memory_chunk -> expr -> expr

val store : memory_chunk -> expr -> expr -> stmt

val sel_constant : constant -> expr

val sel_unop : helper_functions -> unary_operation -> expr -> expr

val sel_binop : helper_functions -> binary_operation -> expr -> expr -> expr

val sel_expr : helper_functions -> Cminor.expr -> expr

val sel_exprlist : helper_functions -> Cminor.expr list -> exprlist

type call_kind =
| Call_default
| Call_imm of ident
| Call_builtin of external_function

val expr_is_addrof_ident : Cminor.expr -> ident option

val classify_call : genv -> Cminor.expr -> call_kind

val compile_switch : coq_Z -> nat -> table -> comptree

val sel_switch :
  (expr -> coq_Z -> expr) -> (expr -> coq_Z -> expr) -> (expr -> coq_Z ->
  expr) -> (expr -> expr) -> nat -> comptree -> exitexpr

val sel_switch_int : nat -> comptree -> exitexpr

val sel_switch_long : helper_functions -> nat -> comptree -> exitexpr

val sel_stmt : helper_functions -> genv -> Cminor.stmt -> stmt res

val sel_function :
  helper_functions -> genv -> Cminor.coq_function -> coq_function res

val sel_fundef : helper_functions -> genv -> Cminor.fundef -> fundef res

val sel_program : Cminor.program -> program res

