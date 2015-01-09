open AST
open BinInt
open BinNums
open Cop
open Coqlib
open Csem
open Csyntax
open Ctypes
open Datatypes
open Determinism
open Errors
open Events
open Globalenvs
open Integers
open List0
open Maps
open Memory
open Values

val is_val : expr -> (coq_val * coq_type) option

val is_loc : expr -> ((block * Int.int) * coq_type) option

val is_val_list : exprlist -> (coq_val * coq_type) list option

val is_skip : statement -> bool

val eventval_of_val : genv -> coq_val -> typ -> eventval option

val list_eventval_of_val :
  genv -> coq_val list -> typ list -> eventval list option

val val_of_eventval : genv -> eventval -> typ -> coq_val option

val do_volatile_load :
  genv -> world -> memory_chunk -> Mem.mem -> block -> Int.int ->
  ((world * trace) * coq_val) option

val do_volatile_store :
  genv -> world -> memory_chunk -> Mem.mem -> block -> Int.int -> coq_val ->
  ((world * trace) * Mem.mem) option

val do_deref_loc :
  genv -> world -> coq_type -> Mem.mem -> block -> Int.int ->
  ((world * trace) * coq_val) option

val check_assign_copy :
  coq_type -> block -> Int.int -> block -> Int.int -> bool

val do_assign_loc :
  genv -> world -> coq_type -> Mem.mem -> block -> Int.int -> coq_val ->
  ((world * trace) * Mem.mem) option

val do_ef_volatile_load :
  genv -> memory_chunk -> world -> coq_val list -> Mem.mem ->
  (((world * trace) * coq_val) * Mem.mem) option

val do_ef_volatile_store :
  genv -> memory_chunk -> world -> coq_val list -> Mem.mem ->
  (((world * trace) * coq_val) * Mem.mem) option

val do_ef_volatile_load_global :
  genv -> memory_chunk -> ident -> Int.int -> world -> coq_val list ->
  Mem.mem -> (((world * trace) * coq_val) * Mem.mem) option

val do_ef_volatile_store_global :
  genv -> memory_chunk -> ident -> Int.int -> world -> coq_val list ->
  Mem.mem -> (((world * trace) * coq_val) * Mem.mem) option

val do_ef_malloc :
  world -> coq_val list -> Mem.mem -> (((world * trace) * coq_val) * Mem.mem)
  option

val do_ef_free :
  world -> coq_val list -> Mem.mem -> (((world * trace) * coq_val) * Mem.mem)
  option

val memcpy_check_args :
  coq_Z -> coq_Z -> block -> coq_Z -> block -> coq_Z -> bool

val do_ef_memcpy :
  coq_Z -> coq_Z -> world -> coq_val list -> Mem.mem ->
  (((world * trace) * coq_val) * Mem.mem) option

val do_ef_annot :
  genv -> ident -> annot_arg list -> world -> coq_val list -> Mem.mem ->
  (((world * trace) * coq_val) * Mem.mem) option

val do_ef_annot_val :
  genv -> ident -> typ -> world -> coq_val list -> Mem.mem ->
  (((world * trace) * coq_val) * Mem.mem) option

val do_external :
  genv -> (ident -> signature -> genv -> world -> coq_val list -> Mem.mem ->
  (((world * trace) * coq_val) * Mem.mem) option) -> (ident -> genv -> world
  -> coq_val list -> Mem.mem -> (((world * trace) * coq_val) * Mem.mem)
  option) -> external_function -> world -> coq_val list -> Mem.mem ->
  (((world * trace) * coq_val) * Mem.mem) option

type reduction =
| Lred of expr * Mem.mem
| Rred of expr * Mem.mem * trace
| Callred of fundef * coq_val list * coq_type * Mem.mem
| Stuckred

val sem_cast_arguments :
  (coq_val * coq_type) list -> typelist -> coq_val list option

type 'a reducts = ((expr -> 'a) * reduction) list

val topred : reduction -> expr reducts

val stuck : expr reducts

val incontext : ('a1 -> 'a2) -> 'a1 reducts -> 'a2 reducts

val incontext2 :
  ('a1 -> 'a3) -> 'a1 reducts -> ('a2 -> 'a3) -> 'a2 reducts -> 'a3 reducts

val step_expr :
  genv -> (ident -> signature -> genv -> world -> coq_val list -> Mem.mem ->
  (((world * trace) * coq_val) * Mem.mem) option) -> (ident -> genv -> world
  -> coq_val list -> Mem.mem -> (((world * trace) * coq_val) * Mem.mem)
  option) -> env -> world -> kind -> expr -> Mem.mem -> expr reducts

val do_alloc_variables :
  env -> Mem.mem -> (ident * coq_type) list -> env * Mem.mem

val sem_bind_parameters :
  genv -> world -> env -> Mem.mem -> (ident * coq_type) list -> coq_val list
  -> Mem.mem option

val expr_final_state :
  coq_function -> cont -> env -> ((expr -> expr) * reduction) ->
  trace * state

val ret : state -> (trace * state) list

val do_step :
  genv -> (ident -> signature -> genv -> world -> coq_val list -> Mem.mem ->
  (((world * trace) * coq_val) * Mem.mem) option) -> (ident -> genv -> world
  -> coq_val list -> Mem.mem -> (((world * trace) * coq_val) * Mem.mem)
  option) -> world -> state -> (trace * state) list

val do_initial_state : program -> (genv * state) option

val at_final_state : state -> Int.int option

