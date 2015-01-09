open AST
open Coqlib
open Floats
open Integers

type condition =
| Ccomp of comparison
| Ccompu of comparison
| Ccompimm of comparison * Int.int
| Ccompuimm of comparison * Int.int
| Ccompf of comparison
| Cnotcompf of comparison
| Ccompfs of comparison
| Cnotcompfs of comparison
| Cmaskzero of Int.int
| Cmasknotzero of Int.int

type addressing =
| Aindexed of Int.int
| Aindexed2 of Int.int
| Ascaled of Int.int * Int.int
| Aindexed2scaled of Int.int * Int.int
| Aglobal of ident * Int.int
| Abased of ident * Int.int
| Abasedscaled of Int.int * ident * Int.int
| Ainstack of Int.int

type operation =
| Omove
| Ointconst of Int.int
| Ofloatconst of float
| Osingleconst of float32
| Oindirectsymbol of ident
| Ocast8signed
| Ocast8unsigned
| Ocast16signed
| Ocast16unsigned
| Oneg
| Osub
| Omul
| Omulimm of Int.int
| Omulhs
| Omulhu
| Odiv
| Odivu
| Omod
| Omodu
| Oand
| Oandimm of Int.int
| Oor
| Oorimm of Int.int
| Oxor
| Oxorimm of Int.int
| Onot
| Oshl
| Oshlimm of Int.int
| Oshr
| Oshrimm of Int.int
| Oshrximm of Int.int
| Oshru
| Oshruimm of Int.int
| Ororimm of Int.int
| Oshldimm of Int.int
| Olea of addressing
| Onegf
| Oabsf
| Oaddf
| Osubf
| Omulf
| Odivf
| Onegfs
| Oabsfs
| Oaddfs
| Osubfs
| Omulfs
| Odivfs
| Osingleoffloat
| Ofloatofsingle
| Ointoffloat
| Ofloatofint
| Ointofsingle
| Osingleofint
| Omakelong
| Olowlong
| Ohighlong
| Ocmp of condition

val coq_Oaddrsymbol : ident -> Int.int -> operation

val coq_Oaddrstack : Int.int -> operation

val eq_condition : condition -> condition -> bool

val eq_addressing : addressing -> addressing -> bool

val eq_operation : operation -> operation -> bool

val type_of_condition : condition -> typ list

val type_of_addressing : addressing -> typ list

val type_of_operation : operation -> typ list * typ

val is_move_operation : operation -> 'a1 list -> 'a1 option

val negate_condition : condition -> condition

val shift_stack_addressing : Int.int -> addressing -> addressing

val shift_stack_operation : Int.int -> operation -> operation

val offset_addressing_total : addressing -> Int.int -> addressing

val offset_addressing : addressing -> Int.int -> addressing option

val is_trivial_op : operation -> bool

val op_depends_on_memory : operation -> bool

