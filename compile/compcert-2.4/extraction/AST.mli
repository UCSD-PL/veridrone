open BinNums
open Bool
open Coqlib
open Errors
open Floats
open Integers
open List0

type ident = positive

val ident_eq : positive -> positive -> bool

val ident_of_string : char list -> ident

type typ =
| Tint
| Tfloat
| Tlong
| Tsingle
| Tany32
| Tany64

val typ_eq : typ -> typ -> bool

val opt_typ_eq : typ option -> typ option -> bool

val list_typ_eq : typ list -> typ list -> bool

val subtype : typ -> typ -> bool

val subtype_list : typ list -> typ list -> bool

type calling_convention = { cc_vararg : bool; cc_structret : bool }

val cc_default : calling_convention

type signature = { sig_args : typ list; sig_res : typ option;
                   sig_cc : calling_convention }

val sig_args : signature -> typ list

val sig_res : signature -> typ option

val proj_sig_res : signature -> typ

val signature_eq : signature -> signature -> bool

val signature_main : signature

type memory_chunk =
| Mint8signed
| Mint8unsigned
| Mint16signed
| Mint16unsigned
| Mint32
| Mint64
| Mfloat32
| Mfloat64
| Many32
| Many64

val chunk_eq : memory_chunk -> memory_chunk -> bool

val type_of_chunk : memory_chunk -> typ

val chunk_of_type : typ -> memory_chunk

type init_data =
| Init_int8 of Int.int
| Init_int16 of Int.int
| Init_int32 of Int.int
| Init_int64 of Int64.int
| Init_float32 of float32
| Init_float64 of float
| Init_space of coq_Z
| Init_addrof of ident * Int.int

type 'v globvar = { gvar_info : 'v; gvar_init : init_data list;
                    gvar_readonly : bool; gvar_volatile : bool }

val gvar_info : 'a1 globvar -> 'a1

val gvar_init : 'a1 globvar -> init_data list

val gvar_readonly : 'a1 globvar -> bool

val gvar_volatile : 'a1 globvar -> bool

type ('f, 'v) globdef =
| Gfun of 'f
| Gvar of 'v globvar

type ('f, 'v) program = { prog_defs : (ident * ('f, 'v) globdef) list;
                          prog_main : ident }

val prog_defs : ('a1, 'a2) program -> (ident * ('a1, 'a2) globdef) list

val prog_main : ('a1, 'a2) program -> ident

val transform_program_globdef :
  ('a1 -> 'a2) -> (ident * ('a1, 'a3) globdef) -> ident * ('a2, 'a3) globdef

val transform_program :
  ('a1 -> 'a2) -> ('a1, 'a3) program -> ('a2, 'a3) program

val transf_globvar : ('a1 -> 'a2 res) -> 'a1 globvar -> 'a2 globvar res

val transf_globdefs :
  ('a1 -> 'a2 res) -> ('a3 -> 'a4 res) -> (ident * ('a1, 'a3) globdef) list
  -> (ident * ('a2, 'a4) globdef) list res

val transform_partial_program2 :
  ('a1 -> 'a2 res) -> ('a3 -> 'a4 res) -> ('a1, 'a3) program -> ('a2, 'a4)
  program res

val transform_partial_program :
  ('a1 -> 'a2 res) -> ('a1, 'a3) program -> ('a2, 'a3) program res

type external_function =
| EF_external of ident * signature
| EF_builtin of ident * signature
| EF_vload of memory_chunk
| EF_vstore of memory_chunk
| EF_vload_global of memory_chunk * ident * Int.int
| EF_vstore_global of memory_chunk * ident * Int.int
| EF_malloc
| EF_free
| EF_memcpy of coq_Z * coq_Z
| EF_annot of ident * annot_arg list
| EF_annot_val of ident * typ
| EF_inline_asm of ident
and annot_arg =
| AA_arg of typ
| AA_int of Int.int
| AA_float of float

val annot_args_typ : annot_arg list -> typ list

val ef_sig : external_function -> signature

val ef_inline : external_function -> bool

val external_function_eq : external_function -> external_function -> bool

type 'f fundef =
| Internal of 'f
| External of external_function

val transf_fundef : ('a1 -> 'a2) -> 'a1 fundef -> 'a2 fundef

val transf_partial_fundef : ('a1 -> 'a2 res) -> 'a1 fundef -> 'a2 fundef res

