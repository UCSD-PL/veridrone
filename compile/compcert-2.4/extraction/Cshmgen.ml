open AST
open BinNums
open Clight
open Cminor
open Cop
open Csharpminor
open Ctypes
open Datatypes
open Errors
open Floats
open Integers
open List0

(** val make_intconst : Int.int -> expr **)

let make_intconst n =
  Econst (Ointconst n)

(** val make_longconst : Int64.int -> expr **)

let make_longconst f =
  Econst (Olongconst f)

(** val make_floatconst : float -> expr **)

let make_floatconst f =
  Econst (Ofloatconst f)

(** val make_singleconst : float32 -> expr **)

let make_singleconst f =
  Econst (Osingleconst f)

(** val make_singleoffloat : expr -> expr **)

let make_singleoffloat e =
  Eunop (Osingleoffloat, e)

(** val make_floatofsingle : expr -> expr **)

let make_floatofsingle e =
  Eunop (Ofloatofsingle, e)

(** val make_floatofint : expr -> signedness -> expr **)

let make_floatofint e = function
| Signed -> Eunop (Ofloatofint, e)
| Unsigned -> Eunop (Ofloatofintu, e)

(** val make_singleofint : expr -> signedness -> expr **)

let make_singleofint e = function
| Signed -> Eunop (Osingleofint, e)
| Unsigned -> Eunop (Osingleofintu, e)

(** val make_intoffloat : expr -> signedness -> expr **)

let make_intoffloat e = function
| Signed -> Eunop (Ointoffloat, e)
| Unsigned -> Eunop (Ointuoffloat, e)

(** val make_intofsingle : expr -> signedness -> expr **)

let make_intofsingle e = function
| Signed -> Eunop (Ointofsingle, e)
| Unsigned -> Eunop (Ointuofsingle, e)

(** val make_longofint : expr -> signedness -> expr **)

let make_longofint e = function
| Signed -> Eunop (Olongofint, e)
| Unsigned -> Eunop (Olongofintu, e)

(** val make_floatoflong : expr -> signedness -> expr **)

let make_floatoflong e = function
| Signed -> Eunop (Ofloatoflong, e)
| Unsigned -> Eunop (Ofloatoflongu, e)

(** val make_singleoflong : expr -> signedness -> expr **)

let make_singleoflong e = function
| Signed -> Eunop (Osingleoflong, e)
| Unsigned -> Eunop (Osingleoflongu, e)

(** val make_longoffloat : expr -> signedness -> expr **)

let make_longoffloat e = function
| Signed -> Eunop (Olongoffloat, e)
| Unsigned -> Eunop (Olonguoffloat, e)

(** val make_longofsingle : expr -> signedness -> expr **)

let make_longofsingle e = function
| Signed -> Eunop (Olongofsingle, e)
| Unsigned -> Eunop (Olonguofsingle, e)

(** val make_cmp_ne_zero : expr -> expr **)

let make_cmp_ne_zero e = match e with
| Ebinop (b, e1, e2) ->
  (match b with
   | Ocmp c -> e
   | Ocmpu c -> e
   | Ocmpf c -> e
   | Ocmpfs c -> e
   | Ocmpl c -> e
   | Ocmplu c -> e
   | _ -> Ebinop ((Ocmp Cne), e, (make_intconst Int.zero)))
| _ -> Ebinop ((Ocmp Cne), e, (make_intconst Int.zero))

(** val make_cast_int : expr -> intsize -> signedness -> expr **)

let make_cast_int e sz si =
  match sz with
  | I8 ->
    (match si with
     | Signed -> Eunop (Ocast8signed, e)
     | Unsigned -> Eunop (Ocast8unsigned, e))
  | I16 ->
    (match si with
     | Signed -> Eunop (Ocast16signed, e)
     | Unsigned -> Eunop (Ocast16unsigned, e))
  | I32 -> e
  | IBool -> make_cmp_ne_zero e

(** val make_cast : coq_type -> coq_type -> expr -> expr res **)

let make_cast from to0 e =
  match classify_cast from to0 with
  | Coq_cast_case_i2i (sz2, si2) -> OK (make_cast_int e sz2 si2)
  | Coq_cast_case_f2s -> OK (make_singleoffloat e)
  | Coq_cast_case_s2f -> OK (make_floatofsingle e)
  | Coq_cast_case_i2f si1 -> OK (make_floatofint e si1)
  | Coq_cast_case_i2s si1 -> OK (make_singleofint e si1)
  | Coq_cast_case_f2i (sz2, si2) ->
    OK (make_cast_int (make_intoffloat e si2) sz2 si2)
  | Coq_cast_case_s2i (sz2, si2) ->
    OK (make_cast_int (make_intofsingle e si2) sz2 si2)
  | Coq_cast_case_i2l si1 -> OK (make_longofint e si1)
  | Coq_cast_case_l2i (sz2, si2) ->
    OK (make_cast_int (Eunop (Ointoflong, e)) sz2 si2)
  | Coq_cast_case_l2f si1 -> OK (make_floatoflong e si1)
  | Coq_cast_case_l2s si1 -> OK (make_singleoflong e si1)
  | Coq_cast_case_f2l si2 -> OK (make_longoffloat e si2)
  | Coq_cast_case_s2l si2 -> OK (make_longofsingle e si2)
  | Coq_cast_case_f2bool ->
    OK (Ebinop ((Ocmpf Cne), e, (make_floatconst Float.zero)))
  | Coq_cast_case_s2bool ->
    OK (Ebinop ((Ocmpfs Cne), e, (make_singleconst Float32.zero)))
  | Coq_cast_case_l2bool ->
    OK (Ebinop ((Ocmpl Cne), e, (make_longconst Int64.zero)))
  | Coq_cast_case_p2bool ->
    OK (Ebinop ((Ocmpu Cne), e, (make_intconst Int.zero)))
  | Coq_cast_case_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('c'::('a'::('s'::('t'::[]))))))))))))))))))
  | _ -> OK e

(** val make_boolean : expr -> coq_type -> expr **)

let make_boolean e ty =
  match classify_bool ty with
  | Coq_bool_case_i -> make_cmp_ne_zero e
  | Coq_bool_case_f -> Ebinop ((Ocmpf Cne), e, (make_floatconst Float.zero))
  | Coq_bool_case_s ->
    Ebinop ((Ocmpfs Cne), e, (make_singleconst Float32.zero))
  | Coq_bool_case_p -> Ebinop ((Ocmpu Cne), e, (make_intconst Int.zero))
  | Coq_bool_case_l -> Ebinop ((Ocmpl Cne), e, (make_longconst Int64.zero))
  | Coq_bool_default -> e

(** val make_notbool : expr -> coq_type -> expr res **)

let make_notbool e ty =
  match classify_bool ty with
  | Coq_bool_case_i -> OK (Ebinop ((Ocmp Ceq), e, (make_intconst Int.zero)))
  | Coq_bool_case_f ->
    OK (Ebinop ((Ocmpf Ceq), e, (make_floatconst Float.zero)))
  | Coq_bool_case_s ->
    OK (Ebinop ((Ocmpfs Ceq), e, (make_singleconst Float32.zero)))
  | Coq_bool_case_p -> OK (Ebinop ((Ocmpu Ceq), e, (make_intconst Int.zero)))
  | Coq_bool_case_l ->
    OK (Ebinop ((Ocmpl Ceq), e, (make_longconst Int64.zero)))
  | Coq_bool_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('n'::('o'::('t'::('b'::('o'::('o'::('l'::[])))))))))))))))))))))

(** val make_neg : expr -> coq_type -> expr res **)

let make_neg e ty =
  match classify_neg ty with
  | Coq_neg_case_i s -> OK (Eunop (Onegint, e))
  | Coq_neg_case_f -> OK (Eunop (Onegf, e))
  | Coq_neg_case_s -> OK (Eunop (Onegfs, e))
  | Coq_neg_case_l s -> OK (Eunop (Onegl, e))
  | Coq_neg_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('n'::('e'::('g'::[])))))))))))))))))

(** val make_absfloat : expr -> coq_type -> expr res **)

let make_absfloat e ty =
  match classify_neg ty with
  | Coq_neg_case_i sg -> OK (Eunop (Oabsf, (make_floatofint e sg)))
  | Coq_neg_case_f -> OK (Eunop (Oabsf, e))
  | Coq_neg_case_s -> OK (Eunop (Oabsf, (make_floatofsingle e)))
  | Coq_neg_case_l sg -> OK (Eunop (Oabsf, (make_floatoflong e sg)))
  | Coq_neg_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('a'::('b'::('s'::('f'::('l'::('o'::('a'::('t'::[]))))))))))))))))))))))

(** val make_notint : expr -> coq_type -> expr res **)

let make_notint e ty =
  match classify_notint ty with
  | Coq_notint_case_i s -> OK (Eunop (Cminor.Onotint, e))
  | Coq_notint_case_l s -> OK (Eunop (Onotl, e))
  | Coq_notint_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('n'::('o'::('t'::('i'::('n'::('t'::[]))))))))))))))))))))

(** val make_binarith :
    binary_operation -> binary_operation -> binary_operation ->
    binary_operation -> binary_operation -> binary_operation -> expr ->
    coq_type -> expr -> coq_type -> expr res **)

let make_binarith iop iopu fop sop lop lopu e1 ty1 e2 ty2 =
  let c = classify_binarith ty1 ty2 in
  let ty = binarith_type c in
  (match make_cast ty1 ty e1 with
   | OK x ->
     (match make_cast ty2 ty e2 with
      | OK x0 ->
        (match c with
         | Coq_bin_case_i s ->
           (match s with
            | Signed -> OK (Ebinop (iop, x, x0))
            | Unsigned -> OK (Ebinop (iopu, x, x0)))
         | Coq_bin_case_l s ->
           (match s with
            | Signed -> OK (Ebinop (lop, x, x0))
            | Unsigned -> OK (Ebinop (lopu, x, x0)))
         | Coq_bin_case_f -> OK (Ebinop (fop, x, x0))
         | Coq_bin_case_s -> OK (Ebinop (sop, x, x0))
         | Coq_bin_default ->
           Error
             (msg
               ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('b'::('i'::('n'::('a'::('r'::('i'::('t'::('h'::[])))))))))))))))))))))))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)

(** val make_add : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_add e1 ty1 e2 ty2 =
  match classify_add ty1 ty2 with
  | Coq_add_case_pi ty ->
    let n = make_intconst (Int.repr (sizeof ty)) in
    OK (Ebinop (Cminor.Oadd, e1, (Ebinop (Cminor.Omul, n, e2))))
  | Coq_add_case_ip ty ->
    let n = make_intconst (Int.repr (sizeof ty)) in
    OK (Ebinop (Cminor.Oadd, e2, (Ebinop (Cminor.Omul, n, e1))))
  | Coq_add_case_pl ty ->
    let n = make_intconst (Int.repr (sizeof ty)) in
    OK (Ebinop (Cminor.Oadd, e1, (Ebinop (Cminor.Omul, n, (Eunop (Ointoflong,
    e2))))))
  | Coq_add_case_lp ty ->
    let n = make_intconst (Int.repr (sizeof ty)) in
    OK (Ebinop (Cminor.Oadd, e2, (Ebinop (Cminor.Omul, n, (Eunop (Ointoflong,
    e1))))))
  | Coq_add_default ->
    make_binarith Cminor.Oadd Cminor.Oadd Oaddf Oaddfs Oaddl Oaddl e1 ty1 e2
      ty2

(** val make_sub : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_sub e1 ty1 e2 ty2 =
  match classify_sub ty1 ty2 with
  | Coq_sub_case_pi ty ->
    let n = make_intconst (Int.repr (sizeof ty)) in
    OK (Ebinop (Cminor.Osub, e1, (Ebinop (Cminor.Omul, n, e2))))
  | Coq_sub_case_pp ty ->
    let n = make_intconst (Int.repr (sizeof ty)) in
    OK (Ebinop (Odivu, (Ebinop (Cminor.Osub, e1, e2)), n))
  | Coq_sub_case_pl ty ->
    let n = make_intconst (Int.repr (sizeof ty)) in
    OK (Ebinop (Cminor.Osub, e1, (Ebinop (Cminor.Omul, n, (Eunop (Ointoflong,
    e2))))))
  | Coq_sub_default ->
    make_binarith Cminor.Osub Cminor.Osub Osubf Osubfs Osubl Osubl e1 ty1 e2
      ty2

(** val make_mul : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_mul e1 ty1 e2 ty2 =
  make_binarith Cminor.Omul Cminor.Omul Omulf Omulfs Omull Omull e1 ty1 e2
    ty2

(** val make_div : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_div e1 ty1 e2 ty2 =
  make_binarith Cminor.Odiv Odivu Odivf Odivfs Odivl Odivlu e1 ty1 e2 ty2

(** val make_binarith_int :
    binary_operation -> binary_operation -> binary_operation ->
    binary_operation -> expr -> coq_type -> expr -> coq_type -> expr res **)

let make_binarith_int iop iopu lop lopu e1 ty1 e2 ty2 =
  let c = classify_binarith ty1 ty2 in
  let ty = binarith_type c in
  (match make_cast ty1 ty e1 with
   | OK x ->
     (match make_cast ty2 ty e2 with
      | OK x0 ->
        (match c with
         | Coq_bin_case_i s ->
           (match s with
            | Signed -> OK (Ebinop (iop, x, x0))
            | Unsigned -> OK (Ebinop (iopu, x, x0)))
         | Coq_bin_case_l s ->
           (match s with
            | Signed -> OK (Ebinop (lop, x, x0))
            | Unsigned -> OK (Ebinop (lopu, x, x0)))
         | _ ->
           Error
             (msg
               ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('b'::('i'::('n'::('a'::('r'::('i'::('t'::('h'::('_'::('i'::('n'::('t'::[])))))))))))))))))))))))))))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)

(** val make_mod : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_mod e1 ty1 e2 ty2 =
  make_binarith_int Cminor.Omod Omodu Omodl Omodlu e1 ty1 e2 ty2

(** val make_and : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_and e1 ty1 e2 ty2 =
  make_binarith_int Cminor.Oand Cminor.Oand Oandl Oandl e1 ty1 e2 ty2

(** val make_or : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_or e1 ty1 e2 ty2 =
  make_binarith_int Cminor.Oor Cminor.Oor Oorl Oorl e1 ty1 e2 ty2

(** val make_xor : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_xor e1 ty1 e2 ty2 =
  make_binarith_int Cminor.Oxor Cminor.Oxor Oxorl Oxorl e1 ty1 e2 ty2

(** val make_shl : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_shl e1 ty1 e2 ty2 =
  match classify_shift ty1 ty2 with
  | Coq_shift_case_ii s -> OK (Ebinop (Cminor.Oshl, e1, e2))
  | Coq_shift_case_ll s -> OK (Ebinop (Oshll, e1, (Eunop (Ointoflong, e2))))
  | Coq_shift_case_il s ->
    OK (Ebinop (Cminor.Oshl, e1, (Eunop (Ointoflong, e2))))
  | Coq_shift_case_li s -> OK (Ebinop (Oshll, e1, e2))
  | Coq_shift_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('s'::('h'::('l'::[])))))))))))))))))

(** val make_shr : expr -> coq_type -> expr -> coq_type -> expr res **)

let make_shr e1 ty1 e2 ty2 =
  match classify_shift ty1 ty2 with
  | Coq_shift_case_ii s ->
    (match s with
     | Signed -> OK (Ebinop (Cminor.Oshr, e1, e2))
     | Unsigned -> OK (Ebinop (Oshru, e1, e2)))
  | Coq_shift_case_ll s ->
    (match s with
     | Signed -> OK (Ebinop (Oshrl, e1, (Eunop (Ointoflong, e2))))
     | Unsigned -> OK (Ebinop (Oshrlu, e1, (Eunop (Ointoflong, e2)))))
  | Coq_shift_case_il s ->
    (match s with
     | Signed -> OK (Ebinop (Cminor.Oshr, e1, (Eunop (Ointoflong, e2))))
     | Unsigned -> OK (Ebinop (Oshru, e1, (Eunop (Ointoflong, e2)))))
  | Coq_shift_case_li s ->
    (match s with
     | Signed -> OK (Ebinop (Oshrl, e1, e2))
     | Unsigned -> OK (Ebinop (Oshrlu, e1, e2)))
  | Coq_shift_default ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('s'::('h'::('r'::[])))))))))))))))))

(** val make_cmp :
    comparison -> expr -> coq_type -> expr -> coq_type -> expr res **)

let make_cmp c e1 ty1 e2 ty2 =
  match classify_cmp ty1 ty2 with
  | Coq_cmp_case_pp -> OK (Ebinop ((Ocmpu c), e1, e2))
  | Coq_cmp_case_pl -> OK (Ebinop ((Ocmpu c), e1, (Eunop (Ointoflong, e2))))
  | Coq_cmp_case_lp -> OK (Ebinop ((Ocmpu c), (Eunop (Ointoflong, e1)), e2))
  | Coq_cmp_default ->
    make_binarith (Ocmp c) (Ocmpu c) (Ocmpf c) (Ocmpfs c) (Ocmpl c) (Ocmplu
      c) e1 ty1 e2 ty2

(** val make_load : expr -> coq_type -> expr res **)

let make_load addr ty_res =
  match access_mode ty_res with
  | By_value chunk -> OK (Eload (chunk, addr))
  | By_nothing ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('l'::('o'::('a'::('d'::[]))))))))))))))))))
  | _ -> OK addr

(** val make_memcpy : expr -> expr -> coq_type -> stmt **)

let make_memcpy dst src ty =
  Sbuiltin (None, (EF_memcpy ((sizeof ty), (alignof_blockcopy ty))),
    (dst :: (src :: [])))

(** val make_store : expr -> coq_type -> expr -> stmt res **)

let make_store addr ty rhs =
  match access_mode ty with
  | By_value chunk -> OK (Sstore (chunk, addr, rhs))
  | By_copy -> OK (make_memcpy addr rhs ty)
  | _ ->
    Error
      (msg
        ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('m'::('a'::('k'::('e'::('_'::('s'::('t'::('o'::('r'::('e'::[])))))))))))))))))))

(** val transl_unop : Cop.unary_operation -> expr -> coq_type -> expr res **)

let transl_unop op a ta =
  match op with
  | Onotbool -> make_notbool a ta
  | Onotint -> make_notint a ta
  | Oneg -> make_neg a ta
  | Oabsfloat -> make_absfloat a ta

(** val transl_binop :
    Cop.binary_operation -> expr -> coq_type -> expr -> coq_type -> expr res **)

let transl_binop op a ta b tb =
  match op with
  | Oadd -> make_add a ta b tb
  | Osub -> make_sub a ta b tb
  | Omul -> make_mul a ta b tb
  | Odiv -> make_div a ta b tb
  | Omod -> make_mod a ta b tb
  | Oand -> make_and a ta b tb
  | Oor -> make_or a ta b tb
  | Oxor -> make_xor a ta b tb
  | Oshl -> make_shl a ta b tb
  | Oshr -> make_shr a ta b tb
  | Oeq -> make_cmp Ceq a ta b tb
  | One -> make_cmp Cne a ta b tb
  | Olt -> make_cmp Clt a ta b tb
  | Ogt -> make_cmp Cgt a ta b tb
  | Ole -> make_cmp Cle a ta b tb
  | Oge -> make_cmp Cge a ta b tb

(** val transl_expr : Clight.expr -> expr res **)

let rec transl_expr = function
| Econst_int (n, t) -> OK (make_intconst n)
| Econst_float (n, t) -> OK (make_floatconst n)
| Econst_single (n, t) -> OK (make_singleconst n)
| Econst_long (n, t) -> OK (make_longconst n)
| Clight.Evar (id, ty) -> make_load (Eaddrof id) ty
| Etempvar (id, ty) -> OK (Evar id)
| Ederef (b, ty) ->
  (match transl_expr b with
   | OK x -> make_load x ty
   | Error msg0 -> Error msg0)
| Clight.Eaddrof (b, t) -> transl_lvalue b
| Clight.Eunop (op, b, t) ->
  (match transl_expr b with
   | OK x -> transl_unop op x (typeof b)
   | Error msg0 -> Error msg0)
| Clight.Ebinop (op, b, c, t) ->
  (match transl_expr b with
   | OK x ->
     (match transl_expr c with
      | OK x0 -> transl_binop op x (typeof b) x0 (typeof c)
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Ecast (b, ty) ->
  (match transl_expr b with
   | OK x -> make_cast (typeof b) ty x
   | Error msg0 -> Error msg0)
| Efield (b, i, ty) ->
  (match typeof b with
   | Tstruct (i0, fld, a0) ->
     (match transl_expr b with
      | OK x ->
        (match field_offset i fld with
         | OK x0 ->
           make_load (Ebinop (Cminor.Oadd, x, (make_intconst (Int.repr x0))))
             ty
         | Error msg0 -> Error msg0)
      | Error msg0 -> Error msg0)
   | Tunion (i0, fld, a0) ->
     (match transl_expr b with
      | OK x -> make_load x ty
      | Error msg0 -> Error msg0)
   | _ ->
     Error
       (msg
         ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('e'::('x'::('p'::('r'::('('::('f'::('i'::('e'::('l'::('d'::(')'::[]))))))))))))))))))))))))))))

(** val transl_lvalue : Clight.expr -> expr res **)

and transl_lvalue = function
| Clight.Evar (id, t) -> OK (Eaddrof id)
| Ederef (b, t) -> transl_expr b
| Efield (b, i, ty) ->
  (match typeof b with
   | Tstruct (i0, fld, a0) ->
     (match transl_expr b with
      | OK x ->
        (match field_offset i fld with
         | OK x0 ->
           OK (Ebinop (Cminor.Oadd, x, (make_intconst (Int.repr x0))))
         | Error msg0 -> Error msg0)
      | Error msg0 -> Error msg0)
   | Tunion (i0, fld, a0) -> transl_expr b
   | _ ->
     Error
       (msg
         ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('l'::('v'::('a'::('l'::('u'::('e'::('('::('f'::('i'::('e'::('l'::('d'::(')'::[]))))))))))))))))))))))))))))))
| _ ->
  Error
    (msg
      ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('l'::('v'::('a'::('l'::('u'::('e'::[]))))))))))))))))))))))

(** val transl_arglist : Clight.expr list -> typelist -> expr list res **)

let rec transl_arglist al tyl =
  match al with
  | [] ->
    (match tyl with
     | Tnil -> OK []
     | Tcons (t, t0) ->
       Error
         (msg
           ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('a'::('r'::('g'::('l'::('i'::('s'::('t'::(':'::(' '::('a'::('r'::('i'::('t'::('y'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::[]))))))))))))))))))))))))))))))))))))))))
  | a1 :: a2 ->
    (match tyl with
     | Tnil ->
       (match transl_expr a1 with
        | OK x ->
          (match make_cast (typeof a1)
                   (default_argument_conversion (typeof a1)) x with
           | OK x0 ->
             (match transl_arglist a2 Tnil with
              | OK x1 -> OK (x0 :: x1)
              | Error msg0 -> Error msg0)
           | Error msg0 -> Error msg0)
        | Error msg0 -> Error msg0)
     | Tcons (ty1, ty2) ->
       (match transl_expr a1 with
        | OK x ->
          (match make_cast (typeof a1) ty1 x with
           | OK x0 ->
             (match transl_arglist a2 ty2 with
              | OK x1 -> OK (x0 :: x1)
              | Error msg0 -> Error msg0)
           | Error msg0 -> Error msg0)
        | Error msg0 -> Error msg0))

(** val typlist_of_arglist : Clight.expr list -> typelist -> typ list **)

let rec typlist_of_arglist al tyl =
  match al with
  | [] -> []
  | a1 :: a2 ->
    (match tyl with
     | Tnil ->
       (typ_of_type (default_argument_conversion (typeof a1))) :: (typlist_of_arglist
                                                                    a2 Tnil)
     | Tcons (ty1, ty2) -> (typ_of_type ty1) :: (typlist_of_arglist a2 ty2))

(** val transl_statement :
    coq_type -> nat -> nat -> statement -> stmt res **)

let rec transl_statement tyret nbrk ncnt = function
| Clight.Sskip -> OK Sskip
| Clight.Sassign (b, c) ->
  (match transl_lvalue b with
   | OK x ->
     (match transl_expr c with
      | OK x0 ->
        (match make_cast (typeof c) (typeof b) x0 with
         | OK x1 -> make_store x (typeof b) x1
         | Error msg0 -> Error msg0)
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Clight.Sset (x, b) ->
  (match transl_expr b with
   | OK x0 -> OK (Sset (x, x0))
   | Error msg0 -> Error msg0)
| Clight.Scall (x, b, cl) ->
  (match classify_fun (typeof b) with
   | Coq_fun_case_f (args, res0, cconv) ->
     (match transl_expr b with
      | OK x0 ->
        (match transl_arglist cl args with
         | OK x1 ->
           OK (Scall (x, { sig_args = (typlist_of_arglist cl args); sig_res =
             (opttyp_of_type res0); sig_cc = cconv }, x0, x1))
         | Error msg0 -> Error msg0)
      | Error msg0 -> Error msg0)
   | Coq_fun_default ->
     Error
       (msg
         ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('s'::('t'::('m'::('t'::('('::('c'::('a'::('l'::('l'::(')'::[])))))))))))))))))))))))))))
| Clight.Sbuiltin (x, ef, tyargs, bl) ->
  (match transl_arglist bl tyargs with
   | OK x0 -> OK (Sbuiltin (x, ef, x0))
   | Error msg0 -> Error msg0)
| Ssequence (s1, s2) ->
  (match transl_statement tyret nbrk ncnt s1 with
   | OK x ->
     (match transl_statement tyret nbrk ncnt s2 with
      | OK x0 -> OK (Sseq (x, x0))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Clight.Sifthenelse (e, s1, s2) ->
  (match transl_expr e with
   | OK x ->
     (match transl_statement tyret nbrk ncnt s1 with
      | OK x0 ->
        (match transl_statement tyret nbrk ncnt s2 with
         | OK x1 -> OK (Sifthenelse ((make_boolean x (typeof e)), x0, x1))
         | Error msg0 -> Error msg0)
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Clight.Sloop (s1, s2) ->
  (match transl_statement tyret (S O) O s1 with
   | OK x ->
     (match transl_statement tyret O (S ncnt) s2 with
      | OK x0 -> OK (Sblock (Sloop (Sseq ((Sblock x), x0))))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Sbreak -> OK (Sexit nbrk)
| Scontinue -> OK (Sexit ncnt)
| Clight.Sreturn o ->
  (match o with
   | Some e ->
     (match transl_expr e with
      | OK x ->
        (match make_cast (typeof e) tyret x with
         | OK x0 -> OK (Sreturn (Some x0))
         | Error msg0 -> Error msg0)
      | Error msg0 -> Error msg0)
   | None -> OK (Sreturn None))
| Clight.Sswitch (a, sl) ->
  (match transl_expr a with
   | OK x ->
     (match transl_lbl_stmt tyret O (S ncnt) sl with
      | OK x0 ->
        (match classify_switch (typeof a) with
         | Coq_switch_case_i -> OK (Sblock (Sswitch (false, x, x0)))
         | Coq_switch_case_l -> OK (Sblock (Sswitch (true, x, x0)))
         | Coq_switch_default ->
           Error
             (msg
               ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('s'::('t'::('m'::('t'::('('::('s'::('w'::('i'::('t'::('c'::('h'::(')'::[])))))))))))))))))))))))))))))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Clight.Slabel (lbl, s0) ->
  (match transl_statement tyret nbrk ncnt s0 with
   | OK x -> OK (Slabel (lbl, x))
   | Error msg0 -> Error msg0)
| Clight.Sgoto lbl -> OK (Sgoto lbl)

(** val transl_lbl_stmt :
    coq_type -> nat -> nat -> labeled_statements -> lbl_stmt res **)

and transl_lbl_stmt tyret nbrk ncnt = function
| Clight.LSnil -> OK LSnil
| Clight.LScons (n, s, sl') ->
  (match transl_statement tyret nbrk ncnt s with
   | OK x ->
     (match transl_lbl_stmt tyret nbrk ncnt sl' with
      | OK x0 -> OK (LScons (n, x, x0))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)

(** val transl_var : (ident * coq_type) -> ident * coq_Z **)

let transl_var v =
  ((fst v), (sizeof (snd v)))

(** val signature_of_function : Clight.coq_function -> signature **)

let signature_of_function f =
  { sig_args = (map typ_of_type (map snd f.Clight.fn_params)); sig_res =
    (opttyp_of_type f.fn_return); sig_cc = f.fn_callconv }

(** val transl_function : Clight.coq_function -> coq_function res **)

let transl_function f =
  match transl_statement f.fn_return (S O) O f.Clight.fn_body with
  | OK x ->
    OK { fn_sig = (signature_of_function f); fn_params =
      (map fst f.Clight.fn_params); fn_vars =
      (map transl_var f.Clight.fn_vars); fn_temps =
      (map fst f.Clight.fn_temps); fn_body = x }
  | Error msg0 -> Error msg0

(** val transl_fundef : Clight.fundef -> fundef res **)

let transl_fundef = function
| Internal g ->
  (match transl_function g with
   | OK x -> OK (AST.Internal x)
   | Error msg0 -> Error msg0)
| External (ef, args, res0, cconv) ->
  if signature_eq (ef_sig ef) (signature_of_type args res0 cconv)
  then OK (AST.External ef)
  else Error
         (msg
           ('C'::('s'::('h'::('m'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('f'::('u'::('n'::('d'::('e'::('f'::(':'::(' '::('w'::('r'::('o'::('n'::('g'::(' '::('e'::('x'::('t'::('e'::('r'::('n'::('a'::('l'::(' '::('s'::('i'::('g'::('n'::('a'::('t'::('u'::('r'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))))))

(** val transl_globvar : coq_type -> unit res **)

let transl_globvar ty =
  OK ()

(** val transl_program : Clight.program -> program res **)

let transl_program p =
  transform_partial_program2 transl_fundef transl_globvar p

