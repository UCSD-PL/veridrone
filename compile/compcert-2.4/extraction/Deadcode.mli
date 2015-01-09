open AST
open BinNums
open Datatypes
open Errors
open Integers
open Kildall
open Lattice
open Maps
open Memdata
open NeedDomain
open NeedOp
open Op
open RTL
open Registers
open ValueAnalysis
open ValueDomain

val add_need_all : reg -> nenv -> nenv

val add_need : reg -> nval -> nenv -> nenv

val add_needs_all : reg list -> nenv -> nenv

val add_needs : reg list -> nval list -> nenv -> nenv

val add_ros_need_all : (reg, ident) sum -> nenv -> nenv

val add_opt_need_all : reg option -> nenv -> nenv

val kill : reg -> nenv -> nenv

val is_dead : nval -> bool

val is_int_zero : nval -> bool

val transfer_builtin :
  VA.t -> external_function -> reg list -> reg -> NE.t -> nmem -> NA.t

val transfer : coq_function -> VA.t PMap.t -> node -> NA.t -> NA.t

module DS : 
 sig 
  module L : 
   SEMILATTICE
  
  val fixpoint :
    'a1 PTree.t -> ('a1 -> positive list) -> (positive -> L.t -> L.t) -> L.t
    PMap.t option
  
  val fixpoint_allnodes :
    'a1 PTree.t -> ('a1 -> positive list) -> (positive -> L.t -> L.t) -> L.t
    PMap.t option
 end

val analyze : VA.t PMap.t -> coq_function -> NA.t PMap.t option

val transf_instr :
  VA.t PMap.t -> NA.t PMap.t -> node -> instruction -> instruction

val vanalyze : romem -> coq_function -> VA.t PMap.t

val transf_function : romem -> coq_function -> coq_function res

val transf_fundef : romem -> fundef -> fundef res

val transf_program : program -> program res

