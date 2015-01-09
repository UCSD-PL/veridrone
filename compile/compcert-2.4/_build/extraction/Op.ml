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

(** val coq_Oaddrsymbol : ident -> Int.int -> operation **)

let coq_Oaddrsymbol id ofs =
  Olea (Aglobal (id, ofs))

(** val coq_Oaddrstack : Int.int -> operation **)

let coq_Oaddrstack ofs =
  Olea (Ainstack ofs)

(** val eq_condition : condition -> condition -> bool **)

let eq_condition x y =
  let h0 = fun x0 y0 ->
    match x0 with
    | Ceq ->
      (match y0 with
       | Ceq -> true
       | _ -> false)
    | Cne ->
      (match y0 with
       | Cne -> true
       | _ -> false)
    | Clt ->
      (match y0 with
       | Clt -> true
       | _ -> false)
    | Cle ->
      (match y0 with
       | Cle -> true
       | _ -> false)
    | Cgt ->
      (match y0 with
       | Cgt -> true
       | _ -> false)
    | Cge ->
      (match y0 with
       | Cge -> true
       | _ -> false)
  in
  (match x with
   | Ccomp x0 ->
     (match y with
      | Ccomp c0 -> h0 x0 c0
      | _ -> false)
   | Ccompu x0 ->
     (match y with
      | Ccompu c0 -> h0 x0 c0
      | _ -> false)
   | Ccompimm (x0, x1) ->
     (match y with
      | Ccompimm (c0, i0) -> if h0 x0 c0 then Int.eq_dec x1 i0 else false
      | _ -> false)
   | Ccompuimm (x0, x1) ->
     (match y with
      | Ccompuimm (c0, i0) -> if h0 x0 c0 then Int.eq_dec x1 i0 else false
      | _ -> false)
   | Ccompf x0 ->
     (match y with
      | Ccompf c0 -> h0 x0 c0
      | _ -> false)
   | Cnotcompf x0 ->
     (match y with
      | Cnotcompf c0 -> h0 x0 c0
      | _ -> false)
   | Ccompfs x0 ->
     (match y with
      | Ccompfs c0 -> h0 x0 c0
      | _ -> false)
   | Cnotcompfs x0 ->
     (match y with
      | Cnotcompfs c0 -> h0 x0 c0
      | _ -> false)
   | Cmaskzero x0 ->
     (match y with
      | Cmaskzero i0 -> Int.eq_dec x0 i0
      | _ -> false)
   | Cmasknotzero x0 ->
     (match y with
      | Cmasknotzero i0 -> Int.eq_dec x0 i0
      | _ -> false))

(** val eq_addressing : addressing -> addressing -> bool **)

let eq_addressing x y =
  match x with
  | Aindexed x0 ->
    (match y with
     | Aindexed i0 -> Int.eq_dec x0 i0
     | _ -> false)
  | Aindexed2 x0 ->
    (match y with
     | Aindexed2 i0 -> Int.eq_dec x0 i0
     | _ -> false)
  | Ascaled (x0, x1) ->
    (match y with
     | Ascaled (i1, i2) ->
       if Int.eq_dec x0 i1 then Int.eq_dec x1 i2 else false
     | _ -> false)
  | Aindexed2scaled (x0, x1) ->
    (match y with
     | Aindexed2scaled (i1, i2) ->
       if Int.eq_dec x0 i1 then Int.eq_dec x1 i2 else false
     | _ -> false)
  | Aglobal (x0, x1) ->
    (match y with
     | Aglobal (i1, i2) -> if peq x0 i1 then Int.eq_dec x1 i2 else false
     | _ -> false)
  | Abased (x0, x1) ->
    (match y with
     | Abased (i1, i2) -> if peq x0 i1 then Int.eq_dec x1 i2 else false
     | _ -> false)
  | Abasedscaled (x0, x1, x2) ->
    (match y with
     | Abasedscaled (i2, i3, i4) ->
       if Int.eq_dec x0 i2
       then if peq x1 i3 then Int.eq_dec x2 i4 else false
       else false
     | _ -> false)
  | Ainstack x0 ->
    (match y with
     | Ainstack i0 -> Int.eq_dec x0 i0
     | _ -> false)

(** val eq_operation : operation -> operation -> bool **)

let eq_operation x y =
  match x with
  | Omove ->
    (match y with
     | Omove -> true
     | _ -> false)
  | Ointconst x0 ->
    (match y with
     | Ointconst i0 -> Int.eq_dec x0 i0
     | _ -> false)
  | Ofloatconst x0 ->
    (match y with
     | Ofloatconst f0 -> Float.eq_dec x0 f0
     | _ -> false)
  | Osingleconst x0 ->
    (match y with
     | Osingleconst f0 -> Float32.eq_dec x0 f0
     | _ -> false)
  | Oindirectsymbol x0 ->
    (match y with
     | Oindirectsymbol i0 -> peq x0 i0
     | _ -> false)
  | Ocast8signed ->
    (match y with
     | Ocast8signed -> true
     | _ -> false)
  | Ocast8unsigned ->
    (match y with
     | Ocast8unsigned -> true
     | _ -> false)
  | Ocast16signed ->
    (match y with
     | Ocast16signed -> true
     | _ -> false)
  | Ocast16unsigned ->
    (match y with
     | Ocast16unsigned -> true
     | _ -> false)
  | Oneg ->
    (match y with
     | Oneg -> true
     | _ -> false)
  | Osub ->
    (match y with
     | Osub -> true
     | _ -> false)
  | Omul ->
    (match y with
     | Omul -> true
     | _ -> false)
  | Omulimm x0 ->
    (match y with
     | Omulimm i0 -> Int.eq_dec x0 i0
     | _ -> false)
  | Omulhs ->
    (match y with
     | Omulhs -> true
     | _ -> false)
  | Omulhu ->
    (match y with
     | Omulhu -> true
     | _ -> false)
  | Odiv ->
    (match y with
     | Odiv -> true
     | _ -> false)
  | Odivu ->
    (match y with
     | Odivu -> true
     | _ -> false)
  | Omod ->
    (match y with
     | Omod -> true
     | _ -> false)
  | Omodu ->
    (match y with
     | Omodu -> true
     | _ -> false)
  | Oand ->
    (match y with
     | Oand -> true
     | _ -> false)
  | Oandimm x0 ->
    (match y with
     | Oandimm i0 -> Int.eq_dec x0 i0
     | _ -> false)
  | Oor ->
    (match y with
     | Oor -> true
     | _ -> false)
  | Oorimm x0 ->
    (match y with
     | Oorimm i0 -> Int.eq_dec x0 i0
     | _ -> false)
  | Oxor ->
    (match y with
     | Oxor -> true
     | _ -> false)
  | Oxorimm x0 ->
    (match y with
     | Oxorimm i0 -> Int.eq_dec x0 i0
     | _ -> false)
  | Onot ->
    (match y with
     | Onot -> true
     | _ -> false)
  | Oshl ->
    (match y with
     | Oshl -> true
     | _ -> false)
  | Oshlimm x0 ->
    (match y with
     | Oshlimm i0 -> Int.eq_dec x0 i0
     | _ -> false)
  | Oshr ->
    (match y with
     | Oshr -> true
     | _ -> false)
  | Oshrimm x0 ->
    (match y with
     | Oshrimm i0 -> Int.eq_dec x0 i0
     | _ -> false)
  | Oshrximm x0 ->
    (match y with
     | Oshrximm i0 -> Int.eq_dec x0 i0
     | _ -> false)
  | Oshru ->
    (match y with
     | Oshru -> true
     | _ -> false)
  | Oshruimm x0 ->
    (match y with
     | Oshruimm i0 -> Int.eq_dec x0 i0
     | _ -> false)
  | Ororimm x0 ->
    (match y with
     | Ororimm i0 -> Int.eq_dec x0 i0
     | _ -> false)
  | Oshldimm x0 ->
    (match y with
     | Oshldimm i0 -> Int.eq_dec x0 i0
     | _ -> false)
  | Olea x0 ->
    (match y with
     | Olea a0 -> eq_addressing x0 a0
     | _ -> false)
  | Onegf ->
    (match y with
     | Onegf -> true
     | _ -> false)
  | Oabsf ->
    (match y with
     | Oabsf -> true
     | _ -> false)
  | Oaddf ->
    (match y with
     | Oaddf -> true
     | _ -> false)
  | Osubf ->
    (match y with
     | Osubf -> true
     | _ -> false)
  | Omulf ->
    (match y with
     | Omulf -> true
     | _ -> false)
  | Odivf ->
    (match y with
     | Odivf -> true
     | _ -> false)
  | Onegfs ->
    (match y with
     | Onegfs -> true
     | _ -> false)
  | Oabsfs ->
    (match y with
     | Oabsfs -> true
     | _ -> false)
  | Oaddfs ->
    (match y with
     | Oaddfs -> true
     | _ -> false)
  | Osubfs ->
    (match y with
     | Osubfs -> true
     | _ -> false)
  | Omulfs ->
    (match y with
     | Omulfs -> true
     | _ -> false)
  | Odivfs ->
    (match y with
     | Odivfs -> true
     | _ -> false)
  | Osingleoffloat ->
    (match y with
     | Osingleoffloat -> true
     | _ -> false)
  | Ofloatofsingle ->
    (match y with
     | Ofloatofsingle -> true
     | _ -> false)
  | Ointoffloat ->
    (match y with
     | Ointoffloat -> true
     | _ -> false)
  | Ofloatofint ->
    (match y with
     | Ofloatofint -> true
     | _ -> false)
  | Ointofsingle ->
    (match y with
     | Ointofsingle -> true
     | _ -> false)
  | Osingleofint ->
    (match y with
     | Osingleofint -> true
     | _ -> false)
  | Omakelong ->
    (match y with
     | Omakelong -> true
     | _ -> false)
  | Olowlong ->
    (match y with
     | Olowlong -> true
     | _ -> false)
  | Ohighlong ->
    (match y with
     | Ohighlong -> true
     | _ -> false)
  | Ocmp x0 ->
    (match y with
     | Ocmp c0 -> eq_condition x0 c0
     | _ -> false)

(** val type_of_condition : condition -> typ list **)

let type_of_condition = function
| Ccomp c0 -> Tint :: (Tint :: [])
| Ccompu c0 -> Tint :: (Tint :: [])
| Ccompf c0 -> Tfloat :: (Tfloat :: [])
| Cnotcompf c0 -> Tfloat :: (Tfloat :: [])
| Ccompfs c0 -> Tsingle :: (Tsingle :: [])
| Cnotcompfs c0 -> Tsingle :: (Tsingle :: [])
| _ -> Tint :: []

(** val type_of_addressing : addressing -> typ list **)

let type_of_addressing = function
| Aindexed2 i -> Tint :: (Tint :: [])
| Aindexed2scaled (i, i0) -> Tint :: (Tint :: [])
| Aglobal (i, i0) -> []
| Ainstack i -> []
| _ -> Tint :: []

(** val type_of_operation : operation -> typ list * typ **)

let type_of_operation = function
| Omove -> ([], Tint)
| Ointconst i -> ([], Tint)
| Ofloatconst f -> ([], Tfloat)
| Osingleconst f -> ([], Tsingle)
| Oindirectsymbol i -> ([], Tint)
| Ocast8signed -> ((Tint :: []), Tint)
| Ocast8unsigned -> ((Tint :: []), Tint)
| Ocast16signed -> ((Tint :: []), Tint)
| Ocast16unsigned -> ((Tint :: []), Tint)
| Oneg -> ((Tint :: []), Tint)
| Omulimm i -> ((Tint :: []), Tint)
| Oandimm i -> ((Tint :: []), Tint)
| Oorimm i -> ((Tint :: []), Tint)
| Oxorimm i -> ((Tint :: []), Tint)
| Onot -> ((Tint :: []), Tint)
| Oshlimm i -> ((Tint :: []), Tint)
| Oshrimm i -> ((Tint :: []), Tint)
| Oshrximm i -> ((Tint :: []), Tint)
| Oshruimm i -> ((Tint :: []), Tint)
| Ororimm i -> ((Tint :: []), Tint)
| Olea addr -> ((type_of_addressing addr), Tint)
| Onegf -> ((Tfloat :: []), Tfloat)
| Oabsf -> ((Tfloat :: []), Tfloat)
| Oaddf -> ((Tfloat :: (Tfloat :: [])), Tfloat)
| Osubf -> ((Tfloat :: (Tfloat :: [])), Tfloat)
| Omulf -> ((Tfloat :: (Tfloat :: [])), Tfloat)
| Odivf -> ((Tfloat :: (Tfloat :: [])), Tfloat)
| Onegfs -> ((Tsingle :: []), Tsingle)
| Oabsfs -> ((Tsingle :: []), Tsingle)
| Oaddfs -> ((Tsingle :: (Tsingle :: [])), Tsingle)
| Osubfs -> ((Tsingle :: (Tsingle :: [])), Tsingle)
| Omulfs -> ((Tsingle :: (Tsingle :: [])), Tsingle)
| Odivfs -> ((Tsingle :: (Tsingle :: [])), Tsingle)
| Osingleoffloat -> ((Tfloat :: []), Tsingle)
| Ofloatofsingle -> ((Tsingle :: []), Tfloat)
| Ointoffloat -> ((Tfloat :: []), Tint)
| Ofloatofint -> ((Tint :: []), Tfloat)
| Ointofsingle -> ((Tsingle :: []), Tint)
| Osingleofint -> ((Tint :: []), Tsingle)
| Omakelong -> ((Tint :: (Tint :: [])), Tlong)
| Olowlong -> ((Tlong :: []), Tint)
| Ohighlong -> ((Tlong :: []), Tint)
| Ocmp c -> ((type_of_condition c), Tint)
| _ -> ((Tint :: (Tint :: [])), Tint)

(** val is_move_operation : operation -> 'a1 list -> 'a1 option **)

let is_move_operation op args =
  match op with
  | Omove ->
    (match args with
     | [] -> None
     | arg :: l ->
       (match l with
        | [] -> Some arg
        | a :: l0 -> None))
  | _ -> None

(** val negate_condition : condition -> condition **)

let negate_condition = function
| Ccomp c -> Ccomp (negate_comparison c)
| Ccompu c -> Ccompu (negate_comparison c)
| Ccompimm (c, n) -> Ccompimm ((negate_comparison c), n)
| Ccompuimm (c, n) -> Ccompuimm ((negate_comparison c), n)
| Ccompf c -> Cnotcompf c
| Cnotcompf c -> Ccompf c
| Ccompfs c -> Cnotcompfs c
| Cnotcompfs c -> Ccompfs c
| Cmaskzero n -> Cmasknotzero n
| Cmasknotzero n -> Cmaskzero n

(** val shift_stack_addressing : Int.int -> addressing -> addressing **)

let shift_stack_addressing delta addr = match addr with
| Ainstack ofs -> Ainstack (Int.add delta ofs)
| _ -> addr

(** val shift_stack_operation : Int.int -> operation -> operation **)

let shift_stack_operation delta op = match op with
| Olea addr -> Olea (shift_stack_addressing delta addr)
| _ -> op

(** val offset_addressing_total : addressing -> Int.int -> addressing **)

let offset_addressing_total addr delta =
  match addr with
  | Aindexed n -> Aindexed (Int.add n delta)
  | Aindexed2 n -> Aindexed2 (Int.add n delta)
  | Ascaled (sc, n) -> Ascaled (sc, (Int.add n delta))
  | Aindexed2scaled (sc, n) -> Aindexed2scaled (sc, (Int.add n delta))
  | Aglobal (s, n) -> Aglobal (s, (Int.add n delta))
  | Abased (s, n) -> Abased (s, (Int.add n delta))
  | Abasedscaled (sc, s, n) -> Abasedscaled (sc, s, (Int.add n delta))
  | Ainstack n -> Ainstack (Int.add n delta)

(** val offset_addressing : addressing -> Int.int -> addressing option **)

let offset_addressing addr delta =
  Some (offset_addressing_total addr delta)

(** val is_trivial_op : operation -> bool **)

let is_trivial_op = function
| Omove -> true
| Ointconst i -> true
| Olea a ->
  (match a with
   | Aglobal (i, i0) -> true
   | Ainstack i -> true
   | _ -> false)
| _ -> false

(** val op_depends_on_memory : operation -> bool **)

let op_depends_on_memory = function
| Ocmp c ->
  (match c with
   | Ccompu c0 -> true
   | _ -> false)
| _ -> false

