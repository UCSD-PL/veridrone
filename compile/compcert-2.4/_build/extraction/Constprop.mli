open AST
open Compopts
open ConstpropOp
open Coqlib
open Datatypes
open Integers
open Maps
open Op
open RTL
open Registers
open ValueAOp
open ValueAnalysis
open ValueDomain

val transf_ros : AE.t -> (reg, ident) sum -> (reg, ident) sum

val const_for_result : aval -> operation option

val successor_rec : nat -> coq_function -> AE.t -> node -> node

val num_iter : nat

val successor : coq_function -> AE.t -> node -> node

val annot_strength_reduction :
  AE.t -> annot_arg list -> reg list -> annot_arg list * reg list

val builtin_strength_reduction :
  AE.t -> external_function -> reg list -> external_function * reg list

val transf_instr :
  coq_function -> VA.t PMap.t -> romem -> node -> instruction -> instruction

val transf_function : romem -> coq_function -> coq_function

val transf_fundef : romem -> fundef -> fundef

val transf_program : program -> program

