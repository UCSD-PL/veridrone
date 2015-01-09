open AST
open BinInt
open BinNat
open BinNums
open Bool
open Coqlib
open Errors
open Zpower

type signedness =
| Signed
| Unsigned

type intsize =
| I8
| I16
| I32
| IBool

type floatsize =
| F32
| F64

type attr = { attr_volatile : bool; attr_alignas : coq_N option }

val attr_volatile : attr -> bool

val attr_alignas : attr -> coq_N option

val noattr : attr

type coq_type =
| Tvoid
| Tint of intsize * signedness * attr
| Tlong of signedness * attr
| Tfloat of floatsize * attr
| Tpointer of coq_type * attr
| Tarray of coq_type * coq_Z * attr
| Tfunction of typelist * coq_type * calling_convention
| Tstruct of ident * fieldlist * attr
| Tunion of ident * fieldlist * attr
| Tcomp_ptr of ident * attr
and typelist =
| Tnil
| Tcons of coq_type * typelist
and fieldlist =
| Fnil
| Fcons of ident * coq_type * fieldlist

val type_eq : coq_type -> coq_type -> bool

val typelist_eq : typelist -> typelist -> bool

val fieldlist_eq : fieldlist -> fieldlist -> bool

val attr_of_type : coq_type -> attr

val change_attributes : (attr -> attr) -> coq_type -> coq_type

val remove_attributes : coq_type -> coq_type

val attr_union : attr -> attr -> attr

val merge_attributes : coq_type -> attr -> coq_type

val type_int32s : coq_type

val type_bool : coq_type

val typeconv : coq_type -> coq_type

val default_argument_conversion : coq_type -> coq_type

val alignof : coq_type -> coq_Z

val alignof_fields : fieldlist -> coq_Z

val sizeof : coq_type -> coq_Z

val sizeof_struct : fieldlist -> coq_Z -> coq_Z

val sizeof_union : fieldlist -> coq_Z

val field_offset_rec : ident -> fieldlist -> coq_Z -> coq_Z res

val field_offset : ident -> fieldlist -> coq_Z res

val field_type : ident -> fieldlist -> coq_type res

type mode =
| By_value of memory_chunk
| By_reference
| By_copy
| By_nothing

val access_mode : coq_type -> mode

val type_is_volatile : coq_type -> bool

val alignof_blockcopy : coq_type -> coq_Z

val type_of_params : (ident * coq_type) list -> typelist

val typ_of_type : coq_type -> typ

val opttyp_of_type : coq_type -> typ option

val typlist_of_typelist : typelist -> typ list

val signature_of_type :
  typelist -> coq_type -> calling_convention -> signature

