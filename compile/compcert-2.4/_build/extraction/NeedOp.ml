open BinNums
open NeedDomain
open Op

(** val op1 : nval -> nval list **)

let op1 nv =
  nv :: []

(** val op2 : nval -> nval list **)

let op2 nv =
  nv :: (nv :: [])

(** val needs_of_condition : condition -> nval list **)

let needs_of_condition = function
| Cmaskzero n -> op1 (maskzero n)
| Cmasknotzero n -> op1 (maskzero n)
| _ -> []

(** val needs_of_addressing : addressing -> nval -> nval list **)

let needs_of_addressing addr nv =
  match addr with
  | Aindexed n -> op1 (modarith nv)
  | Aindexed2 n -> op2 (modarith nv)
  | Aindexed2scaled (sc, ofs) -> op2 (modarith nv)
  | Aglobal (s, ofs) -> []
  | Abased (s, ofs) -> op1 (modarith nv)
  | Ainstack ofs -> []
  | _ -> op1 (modarith (modarith nv))

(** val needs_of_operation : operation -> nval -> nval list **)

let needs_of_operation op nv =
  match op with
  | Omove -> op1 nv
  | Ointconst n -> []
  | Ofloatconst n -> []
  | Osingleconst n -> []
  | Oindirectsymbol id -> []
  | Ocast8signed ->
    op1 (sign_ext (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) nv)
  | Ocast8unsigned ->
    op1 (zero_ext (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) nv)
  | Ocast16signed ->
    op1 (sign_ext (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) nv)
  | Ocast16unsigned ->
    op1 (zero_ext (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) nv)
  | Oneg -> op1 (modarith nv)
  | Omul -> op2 (modarith nv)
  | Omulimm n -> op1 (modarith nv)
  | Oand -> op2 (bitwise nv)
  | Oandimm n -> op1 (andimm nv n)
  | Oor -> op2 (bitwise nv)
  | Oorimm n -> op1 (orimm nv n)
  | Oxor -> op2 (bitwise nv)
  | Oxorimm n -> op1 (bitwise nv)
  | Onot -> op1 (bitwise nv)
  | Oshlimm n -> op1 (shlimm nv n)
  | Oshrimm n -> op1 (shrimm nv n)
  | Oshrximm n -> op1 (default nv)
  | Oshruimm n -> op1 (shruimm nv n)
  | Ororimm n -> op1 (ror nv n)
  | Oshldimm n -> op1 (default nv)
  | Olea addr -> needs_of_addressing addr nv
  | Onegf -> op1 (default nv)
  | Oabsf -> op1 (default nv)
  | Onegfs -> op1 (default nv)
  | Oabsfs -> op1 (default nv)
  | Osingleoffloat -> op1 (default nv)
  | Ofloatofsingle -> op1 (default nv)
  | Ointoffloat -> op1 (default nv)
  | Ofloatofint -> op1 (default nv)
  | Ointofsingle -> op1 (default nv)
  | Osingleofint -> op1 (default nv)
  | Olowlong -> op1 (default nv)
  | Ohighlong -> op1 (default nv)
  | Ocmp c -> needs_of_condition c
  | _ -> op2 (default nv)

(** val operation_is_redundant : operation -> nval -> bool **)

let operation_is_redundant op nv =
  match op with
  | Ocast8signed ->
    sign_ext_redundant (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) nv
  | Ocast8unsigned ->
    zero_ext_redundant (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) nv
  | Ocast16signed ->
    sign_ext_redundant (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) nv
  | Ocast16unsigned ->
    zero_ext_redundant (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) nv
  | Oandimm n -> andimm_redundant nv n
  | Oorimm n -> orimm_redundant nv n
  | _ -> false

