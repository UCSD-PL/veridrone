open BinNums
open Compopts
open Integers
open Op
open ValueDomain

(** val eval_static_condition : condition -> aval list -> abool **)

let eval_static_condition cond vl =
  match cond with
  | Ccomp c ->
    (match vl with
     | [] -> Bnone
     | v1 :: l ->
       (match l with
        | [] -> Bnone
        | v2 :: l0 ->
          (match l0 with
           | [] -> cmp_bool c v1 v2
           | a :: l1 -> Bnone)))
  | Ccompu c ->
    (match vl with
     | [] -> Bnone
     | v1 :: l ->
       (match l with
        | [] -> Bnone
        | v2 :: l0 ->
          (match l0 with
           | [] -> cmpu_bool c v1 v2
           | a :: l1 -> Bnone)))
  | Ccompimm (c, n) ->
    (match vl with
     | [] -> Bnone
     | v1 :: l ->
       (match l with
        | [] -> cmp_bool c v1 (I n)
        | a :: l0 -> Bnone))
  | Ccompuimm (c, n) ->
    (match vl with
     | [] -> Bnone
     | v1 :: l ->
       (match l with
        | [] -> cmpu_bool c v1 (I n)
        | a :: l0 -> Bnone))
  | Ccompf c ->
    (match vl with
     | [] -> Bnone
     | v1 :: l ->
       (match l with
        | [] -> Bnone
        | v2 :: l0 ->
          (match l0 with
           | [] -> cmpf_bool c v1 v2
           | a :: l1 -> Bnone)))
  | Cnotcompf c ->
    (match vl with
     | [] -> Bnone
     | v1 :: l ->
       (match l with
        | [] -> Bnone
        | v2 :: l0 ->
          (match l0 with
           | [] -> cnot (cmpf_bool c v1 v2)
           | a :: l1 -> Bnone)))
  | Ccompfs c ->
    (match vl with
     | [] -> Bnone
     | v1 :: l ->
       (match l with
        | [] -> Bnone
        | v2 :: l0 ->
          (match l0 with
           | [] -> cmpfs_bool c v1 v2
           | a :: l1 -> Bnone)))
  | Cnotcompfs c ->
    (match vl with
     | [] -> Bnone
     | v1 :: l ->
       (match l with
        | [] -> Bnone
        | v2 :: l0 ->
          (match l0 with
           | [] -> cnot (cmpfs_bool c v1 v2)
           | a :: l1 -> Bnone)))
  | Cmaskzero n ->
    (match vl with
     | [] -> Bnone
     | v1 :: l ->
       (match l with
        | [] -> maskzero v1 n
        | a :: l0 -> Bnone))
  | Cmasknotzero n ->
    (match vl with
     | [] -> Bnone
     | v1 :: l ->
       (match l with
        | [] -> cnot (maskzero v1 n)
        | a :: l0 -> Bnone))

(** val eval_static_addressing : addressing -> aval list -> aval **)

let eval_static_addressing addr vl =
  match addr with
  | Aindexed n ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> add v1 (I n)
        | a :: l0 -> Vbot))
  | Aindexed2 n ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> add (add v1 v2) (I n)
           | a :: l1 -> Vbot)))
  | Ascaled (sc, ofs) ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> add (mul v1 (I sc)) (I ofs)
        | a :: l0 -> Vbot))
  | Aindexed2scaled (sc, ofs) ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> add v1 (add (mul v2 (I sc)) (I ofs))
           | a :: l1 -> Vbot)))
  | Aglobal (s, ofs) ->
    (match vl with
     | [] -> Ptr (Gl (s, ofs))
     | a :: l -> Vbot)
  | Abased (s, ofs) ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> add (Ptr (Gl (s, ofs))) v1
        | a :: l0 -> Vbot))
  | Abasedscaled (sc, s, ofs) ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> add (Ptr (Gl (s, ofs))) (mul v1 (I sc))
        | a :: l0 -> Vbot))
  | Ainstack ofs ->
    (match vl with
     | [] -> Ptr (Stk ofs)
     | a :: l -> Vbot)

(** val eval_static_operation : operation -> aval list -> aval **)

let eval_static_operation op vl =
  match op with
  | Omove ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> v1
        | a :: l0 -> Vbot))
  | Ointconst n ->
    (match vl with
     | [] -> I n
     | a :: l -> Vbot)
  | Ofloatconst n ->
    (match vl with
     | [] -> if propagate_float_constants () then F n else ftop
     | a :: l -> Vbot)
  | Osingleconst n ->
    (match vl with
     | [] -> if propagate_float_constants () then FS n else ftop
     | a :: l -> Vbot)
  | Oindirectsymbol id ->
    (match vl with
     | [] -> Ptr (Gl (id, Int.zero))
     | a :: l -> Vbot)
  | Ocast8signed ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> sign_ext (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) v1
        | a :: l0 -> Vbot))
  | Ocast8unsigned ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> zero_ext (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) v1
        | a :: l0 -> Vbot))
  | Ocast16signed ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> sign_ext (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) v1
        | a :: l0 -> Vbot))
  | Ocast16unsigned ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> zero_ext (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) v1
        | a :: l0 -> Vbot))
  | Oneg ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> neg v1
        | a :: l0 -> Vbot))
  | Osub ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> sub v1 v2
           | a :: l1 -> Vbot)))
  | Omul ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> mul v1 v2
           | a :: l1 -> Vbot)))
  | Omulimm n ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> mul v1 (I n)
        | a :: l0 -> Vbot))
  | Omulhs ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> mulhs v1 v2
           | a :: l1 -> Vbot)))
  | Omulhu ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> mulhu v1 v2
           | a :: l1 -> Vbot)))
  | Odiv ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> divs v1 v2
           | a :: l1 -> Vbot)))
  | Odivu ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> divu v1 v2
           | a :: l1 -> Vbot)))
  | Omod ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> mods v1 v2
           | a :: l1 -> Vbot)))
  | Omodu ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> modu v1 v2
           | a :: l1 -> Vbot)))
  | Oand ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> coq_and v1 v2
           | a :: l1 -> Vbot)))
  | Oandimm n ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> coq_and v1 (I n)
        | a :: l0 -> Vbot))
  | Oor ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> coq_or v1 v2
           | a :: l1 -> Vbot)))
  | Oorimm n ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> coq_or v1 (I n)
        | a :: l0 -> Vbot))
  | Oxor ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> xor v1 v2
           | a :: l1 -> Vbot)))
  | Oxorimm n ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> xor v1 (I n)
        | a :: l0 -> Vbot))
  | Onot ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> notint v1
        | a :: l0 -> Vbot))
  | Oshl ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> shl v1 v2
           | a :: l1 -> Vbot)))
  | Oshlimm n ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> shl v1 (I n)
        | a :: l0 -> Vbot))
  | Oshr ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> shr v1 v2
           | a :: l1 -> Vbot)))
  | Oshrimm n ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> shr v1 (I n)
        | a :: l0 -> Vbot))
  | Oshrximm n ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> shrx v1 (I n)
        | a :: l0 -> Vbot))
  | Oshru ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> shru v1 v2
           | a :: l1 -> Vbot)))
  | Oshruimm n ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> shru v1 (I n)
        | a :: l0 -> Vbot))
  | Ororimm n ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> ror v1 (I n)
        | a :: l0 -> Vbot))
  | Oshldimm n ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] ->
             coq_or (shl v1 (I n)) (shru v2 (I (Int.sub Int.iwordsize n)))
           | a :: l1 -> Vbot)))
  | Olea addr -> eval_static_addressing addr vl
  | Onegf ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> negf v1
        | a :: l0 -> Vbot))
  | Oabsf ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> absf v1
        | a :: l0 -> Vbot))
  | Oaddf ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> addf v1 v2
           | a :: l1 -> Vbot)))
  | Osubf ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> subf v1 v2
           | a :: l1 -> Vbot)))
  | Omulf ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> mulf v1 v2
           | a :: l1 -> Vbot)))
  | Odivf ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> divf v1 v2
           | a :: l1 -> Vbot)))
  | Onegfs ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> negfs v1
        | a :: l0 -> Vbot))
  | Oabsfs ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> absfs v1
        | a :: l0 -> Vbot))
  | Oaddfs ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> addfs v1 v2
           | a :: l1 -> Vbot)))
  | Osubfs ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> subfs v1 v2
           | a :: l1 -> Vbot)))
  | Omulfs ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> mulfs v1 v2
           | a :: l1 -> Vbot)))
  | Odivfs ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> divfs v1 v2
           | a :: l1 -> Vbot)))
  | Osingleoffloat ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> singleoffloat v1
        | a :: l0 -> Vbot))
  | Ofloatofsingle ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> floatofsingle v1
        | a :: l0 -> Vbot))
  | Ointoffloat ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> intoffloat v1
        | a :: l0 -> Vbot))
  | Ofloatofint ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> floatofint v1
        | a :: l0 -> Vbot))
  | Ointofsingle ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> intofsingle v1
        | a :: l0 -> Vbot))
  | Osingleofint ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> singleofint v1
        | a :: l0 -> Vbot))
  | Omakelong ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> Vbot
        | v2 :: l0 ->
          (match l0 with
           | [] -> longofwords v1 v2
           | a :: l1 -> Vbot)))
  | Olowlong ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> loword v1
        | a :: l0 -> Vbot))
  | Ohighlong ->
    (match vl with
     | [] -> Vbot
     | v1 :: l ->
       (match l with
        | [] -> hiword v1
        | a :: l0 -> Vbot))
  | Ocmp c -> of_optbool (eval_static_condition c vl)

