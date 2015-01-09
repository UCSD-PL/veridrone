open AST
open BinInt
open BinNums
open BinPos
open Coqlib
open Datatypes
open Integers
open List0
open Maps
open Memory
open Memtype
open Values

val store_zeros : Mem.mem -> block -> coq_Z -> coq_Z -> Mem.mem option

module Genv : 
 sig 
  type ('f, 'v) t = { genv_symb : block PTree.t; genv_funs : 'f PTree.t;
                      genv_vars : 'v globvar PTree.t; genv_next : block }
  
  val genv_symb : ('a1, 'a2) t -> block PTree.t
  
  val genv_funs : ('a1, 'a2) t -> 'a1 PTree.t
  
  val genv_vars : ('a1, 'a2) t -> 'a2 globvar PTree.t
  
  val genv_next : ('a1, 'a2) t -> block
  
  val find_symbol : ('a1, 'a2) t -> ident -> block option
  
  val symbol_address : ('a1, 'a2) t -> ident -> Int.int -> coq_val
  
  val find_funct_ptr : ('a1, 'a2) t -> block -> 'a1 option
  
  val find_funct : ('a1, 'a2) t -> coq_val -> 'a1 option
  
  val invert_symbol : ('a1, 'a2) t -> block -> ident option
  
  val find_var_info : ('a1, 'a2) t -> block -> 'a2 globvar option
  
  val add_global :
    ('a1, 'a2) t -> (ident * ('a1, 'a2) globdef) -> ('a1, 'a2) t
  
  val add_globals :
    ('a1, 'a2) t -> (ident * ('a1, 'a2) globdef) list -> ('a1, 'a2) t
  
  val empty_genv : ('a1, 'a2) t
  
  val globalenv : ('a1, 'a2) program -> ('a1, 'a2) t
  
  val advance_next :
    (ident * ('a1, 'a2) globdef) list -> positive -> positive
  
  val init_data_size : init_data -> coq_Z
  
  val store_init_data :
    ('a1, 'a2) t -> Mem.mem -> block -> coq_Z -> init_data -> Mem.mem option
  
  val store_init_data_list :
    ('a1, 'a2) t -> Mem.mem -> block -> coq_Z -> init_data list -> Mem.mem
    option
  
  val init_data_list_size : init_data list -> coq_Z
  
  val perm_globvar : 'a1 globvar -> permission
  
  val alloc_global :
    ('a1, 'a2) t -> Mem.mem -> (ident * ('a1, 'a2) globdef) -> Mem.mem option
  
  val alloc_globals :
    ('a1, 'a2) t -> Mem.mem -> (ident * ('a1, 'a2) globdef) list -> Mem.mem
    option
  
  val init_mem : ('a1, 'a2) program -> Mem.mem option
 end

