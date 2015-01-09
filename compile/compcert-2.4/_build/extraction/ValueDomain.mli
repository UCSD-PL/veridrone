open AST
open BinInt
open BinNums
open Bool
open Compopts
open Coqlib
open Datatypes
open Floats
open Integers
open Lattice
open Maps
open Memdata
open Registers
open Zpower

type abool =
| Bnone
| Just of bool
| Maybe of bool
| Btop

val club : abool -> abool -> abool

val cnot : abool -> abool

type aptr =
| Pbot
| Gl of ident * Int.int
| Glo of ident
| Glob
| Stk of Int.int
| Stack
| Nonstack
| Ptop

val eq_aptr : aptr -> aptr -> bool

val plub : aptr -> aptr -> aptr

val pincl : aptr -> aptr -> bool

val padd : aptr -> Int.int -> aptr

val psub : aptr -> Int.int -> aptr

val poffset : aptr -> aptr

val cmp_different_blocks : comparison -> abool

val pcmp : comparison -> aptr -> aptr -> abool

val pdisjoint : aptr -> coq_Z -> aptr -> coq_Z -> bool

type aval =
| Vbot
| I of Int.int
| Uns of coq_Z
| Sgn of coq_Z
| L of Int64.int
| F of float
| FS of float32
| Ptr of aptr
| Ifptr of aptr

val eq_aval : aval -> aval -> bool

val coq_Vtop : aval

val itop : aval

val ftop : aval

val ltop : aval

val usize : Int.int -> coq_Z

val ssize : Int.int -> coq_Z

val uns : coq_Z -> aval

val sgn : coq_Z -> aval

val vlub : aval -> aval -> aval

val aptr_of_aval : aval -> aptr

val vplub : aval -> aptr -> aptr

val vpincl : aval -> aptr -> bool

val vincl : aval -> aval -> bool

val unop_int : (Int.int -> Int.int) -> aval -> aval

val binop_int : (Int.int -> Int.int -> Int.int) -> aval -> aval -> aval

val unop_float : (float -> float) -> aval -> aval

val binop_float : (float -> float -> float) -> aval -> aval -> aval

val unop_single : (float32 -> float32) -> aval -> aval

val binop_single : (float32 -> float32 -> float32) -> aval -> aval -> aval

val shl : aval -> aval -> aval

val shru : aval -> aval -> aval

val shr : aval -> aval -> aval

val coq_and : aval -> aval -> aval

val coq_or : aval -> aval -> aval

val xor : aval -> aval -> aval

val notint : aval -> aval

val ror : aval -> aval -> aval

val neg : aval -> aval

val add : aval -> aval -> aval

val sub : aval -> aval -> aval

val mul : aval -> aval -> aval

val mulhs : aval -> aval -> aval

val mulhu : aval -> aval -> aval

val divs : aval -> aval -> aval

val divu : aval -> aval -> aval

val mods : aval -> aval -> aval

val modu : aval -> aval -> aval

val shrx : aval -> aval -> aval

val negf : aval -> aval

val absf : aval -> aval

val addf : aval -> aval -> aval

val subf : aval -> aval -> aval

val mulf : aval -> aval -> aval

val divf : aval -> aval -> aval

val negfs : aval -> aval

val absfs : aval -> aval

val addfs : aval -> aval -> aval

val subfs : aval -> aval -> aval

val mulfs : aval -> aval -> aval

val divfs : aval -> aval -> aval

val zero_ext : coq_Z -> aval -> aval

val sign_ext : coq_Z -> aval -> aval

val singleoffloat : aval -> aval

val floatofsingle : aval -> aval

val intoffloat : aval -> aval

val floatofint : aval -> aval

val intofsingle : aval -> aval

val singleofint : aval -> aval

val longofwords : aval -> aval -> aval

val loword : aval -> aval

val hiword : aval -> aval

val cmp_intv : comparison -> (coq_Z * coq_Z) -> coq_Z -> abool

val uintv : aval -> coq_Z * coq_Z

val sintv : aval -> coq_Z * coq_Z

val cmpu_bool : comparison -> aval -> aval -> abool

val cmp_bool : comparison -> aval -> aval -> abool

val cmpf_bool : comparison -> aval -> aval -> abool

val cmpfs_bool : comparison -> aval -> aval -> abool

val maskzero : aval -> Int.int -> abool

val of_optbool : abool -> aval

val resolve_branch : abool -> bool option

val vnormalize : memory_chunk -> aval -> aval

type acontent =
| ACany
| ACval of memory_chunk * aval

val eq_acontent : acontent -> acontent -> bool

type ablock = { ab_contents : acontent ZMap.t; ab_summary : aptr }

val ab_contents : ablock -> acontent ZMap.t

val ab_summary : ablock -> aptr

val ablock_init : aptr -> ablock

val chunk_compat : memory_chunk -> memory_chunk -> bool

val ablock_load : memory_chunk -> ablock -> coq_Z -> aval

val ablock_load_anywhere : memory_chunk -> ablock -> aval

val inval_after : coq_Z -> coq_Z -> acontent ZMap.t -> acontent ZMap.t

val inval_if : coq_Z -> coq_Z -> acontent ZMap.t -> acontent ZMap.t

val inval_before : coq_Z -> coq_Z -> acontent ZMap.t -> acontent ZMap.t

val ablock_store : memory_chunk -> ablock -> coq_Z -> aval -> ablock

val ablock_store_anywhere : memory_chunk -> ablock -> aval -> ablock

val ablock_loadbytes : ablock -> aptr

val ablock_storebytes : ablock -> aptr -> coq_Z -> coq_Z -> ablock

val ablock_storebytes_anywhere : ablock -> aptr -> ablock

val bbeq : ablock -> ablock -> bool

val combine_acontents_opt :
  acontent option -> acontent option -> acontent option

val combine_contentmaps :
  acontent ZMap.t -> acontent ZMap.t -> acontent ZMap.t

val blub : ablock -> ablock -> ablock

type romem = ablock PTree.t

type amem = { am_stack : ablock; am_glob : ablock PTree.t;
              am_nonstack : aptr; am_top : aptr }

val am_stack : amem -> ablock

val am_glob : amem -> ablock PTree.t

val am_nonstack : amem -> aptr

val am_top : amem -> aptr

val minit : aptr -> amem

val mtop : amem

val load : memory_chunk -> romem -> amem -> aptr -> aval

val loadv : memory_chunk -> romem -> amem -> aval -> aval

val store : memory_chunk -> amem -> aptr -> aval -> amem

val storev : memory_chunk -> amem -> aval -> aval -> amem

val loadbytes : amem -> romem -> aptr -> aptr

val storebytes : amem -> aptr -> coq_Z -> aptr -> amem

val mbeq : amem -> amem -> bool

val combine_ablock : ablock option -> ablock option -> ablock option

val mlub : amem -> amem -> amem

module AVal : 
 sig 
  type t = aval
  
  val beq : t -> t -> bool
  
  val bot : t
  
  val top : t
  
  val lub : aval -> aval -> aval
 end

module AE : 
 sig 
  type t' =
  | Bot
  | Top_except of AVal.t PTree.t
  
  type t = t'
  
  val get : positive -> t -> AVal.t
  
  val set : positive -> AVal.t -> t -> t
  
  val beq : t -> t -> bool
  
  val bot : t'
  
  val top : t'
  
  module LM : 
   sig 
    type t = AVal.t PTree.t
    
    val get : positive -> t -> AVal.t
    
    val set : positive -> AVal.t -> t -> t
    
    val beq : t -> t -> bool
    
    val bot : t
    
    val opt_beq : AVal.t option -> AVal.t option -> bool
    
    type changed =
    | Unchanged
    | Changed of AVal.t PTree.t
    
    val combine_l :
      (AVal.t option -> AVal.t option -> AVal.t option) -> AVal.t PTree.t ->
      changed
    
    val combine_r :
      (AVal.t option -> AVal.t option -> AVal.t option) -> AVal.t PTree.t ->
      changed
    
    type changed2 =
    | Same
    | Same1
    | Same2
    | CC of AVal.t PTree.t
    
    val xcombine :
      (AVal.t option -> AVal.t option -> AVal.t option) -> AVal.t PTree.t ->
      AVal.t PTree.t -> changed2
    
    val combine :
      (AVal.t option -> AVal.t option -> AVal.t option) -> AVal.t PTree.t ->
      AVal.t PTree.t -> AVal.t PTree.t
    
    val lub : t -> t -> t
   end
  
  val opt_lub : AVal.t -> AVal.t -> AVal.t option
  
  val lub : t -> t -> t
 end

type aenv = AE.t

val einit_regs : reg list -> aenv

val eforget : reg list -> aenv -> aenv

module VA : 
 sig 
  type t' =
  | Bot
  | State of aenv * amem
  
  val t'_rect : 'a1 -> (aenv -> amem -> 'a1) -> t' -> 'a1
  
  val t'_rec : 'a1 -> (aenv -> amem -> 'a1) -> t' -> 'a1
  
  type t = t'
  
  val beq : t -> t -> bool
  
  val bot : t
  
  val lub : t -> t -> t
 end

