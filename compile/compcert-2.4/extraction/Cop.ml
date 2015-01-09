open AST
open BinNums
open Coqlib
open Ctypes
open Datatypes
open Floats
open Integers
open Memory
open Values

type unary_operation =
| Onotbool
| Onotint
| Oneg
| Oabsfloat

type binary_operation =
| Oadd
| Osub
| Omul
| Odiv
| Omod
| Oand
| Oor
| Oxor
| Oshl
| Oshr
| Oeq
| One
| Olt
| Ogt
| Ole
| Oge

type incr_or_decr =
| Incr
| Decr

type classify_cast_cases =
| Coq_cast_case_neutral
| Coq_cast_case_i2i of intsize * signedness
| Coq_cast_case_f2f
| Coq_cast_case_s2s
| Coq_cast_case_f2s
| Coq_cast_case_s2f
| Coq_cast_case_i2f of signedness
| Coq_cast_case_i2s of signedness
| Coq_cast_case_f2i of intsize * signedness
| Coq_cast_case_s2i of intsize * signedness
| Coq_cast_case_l2l
| Coq_cast_case_i2l of signedness
| Coq_cast_case_l2i of intsize * signedness
| Coq_cast_case_l2f of signedness
| Coq_cast_case_l2s of signedness
| Coq_cast_case_f2l of signedness
| Coq_cast_case_s2l of signedness
| Coq_cast_case_f2bool
| Coq_cast_case_s2bool
| Coq_cast_case_l2bool
| Coq_cast_case_p2bool
| Coq_cast_case_struct of ident * fieldlist * ident * fieldlist
| Coq_cast_case_union of ident * fieldlist * ident * fieldlist
| Coq_cast_case_void
| Coq_cast_case_default

(** val classify_cast : coq_type -> coq_type -> classify_cast_cases **)

let classify_cast tfrom = function
| Tvoid -> Coq_cast_case_void
| Tint (sz2, si2, a) ->
  (match sz2 with
   | I32 ->
     (match tfrom with
      | Tvoid -> Coq_cast_case_default
      | Tlong (s, a0) -> Coq_cast_case_l2i (sz2, si2)
      | Tfloat (f, a0) ->
        (match f with
         | F32 -> Coq_cast_case_s2i (sz2, si2)
         | F64 -> Coq_cast_case_f2i (sz2, si2))
      | Tstruct (i, f, a0) -> Coq_cast_case_default
      | Tunion (i, f, a0) -> Coq_cast_case_default
      | _ -> Coq_cast_case_neutral)
   | IBool ->
     (match tfrom with
      | Tvoid -> Coq_cast_case_default
      | Tint (sz1, si1, a0) -> Coq_cast_case_i2i (sz2, si2)
      | Tlong (s, a0) -> Coq_cast_case_l2bool
      | Tfloat (f, a0) ->
        (match f with
         | F32 -> Coq_cast_case_s2bool
         | F64 -> Coq_cast_case_f2bool)
      | Tstruct (i, f, a0) -> Coq_cast_case_default
      | Tunion (i, f, a0) -> Coq_cast_case_default
      | _ -> Coq_cast_case_p2bool)
   | _ ->
     (match tfrom with
      | Tint (sz1, si1, a0) -> Coq_cast_case_i2i (sz2, si2)
      | Tlong (s, a0) -> Coq_cast_case_l2i (sz2, si2)
      | Tfloat (f, a0) ->
        (match f with
         | F32 -> Coq_cast_case_s2i (sz2, si2)
         | F64 -> Coq_cast_case_f2i (sz2, si2))
      | _ -> Coq_cast_case_default))
| Tlong (si2, a) ->
  (match tfrom with
   | Tvoid -> Coq_cast_case_default
   | Tint (sz1, si1, a0) -> Coq_cast_case_i2l si1
   | Tlong (s, a0) -> Coq_cast_case_l2l
   | Tfloat (f, a0) ->
     (match f with
      | F32 -> Coq_cast_case_s2l si2
      | F64 -> Coq_cast_case_f2l si2)
   | Tstruct (i, f, a0) -> Coq_cast_case_default
   | Tunion (i, f, a0) -> Coq_cast_case_default
   | _ -> Coq_cast_case_i2l si2)
| Tfloat (f, a) ->
  (match f with
   | F32 ->
     (match tfrom with
      | Tint (sz1, si1, a0) -> Coq_cast_case_i2s si1
      | Tlong (si1, a0) -> Coq_cast_case_l2s si1
      | Tfloat (f0, a0) ->
        (match f0 with
         | F32 -> Coq_cast_case_s2s
         | F64 -> Coq_cast_case_f2s)
      | _ -> Coq_cast_case_default)
   | F64 ->
     (match tfrom with
      | Tint (sz1, si1, a0) -> Coq_cast_case_i2f si1
      | Tlong (si1, a0) -> Coq_cast_case_l2f si1
      | Tfloat (f0, a0) ->
        (match f0 with
         | F32 -> Coq_cast_case_s2f
         | F64 -> Coq_cast_case_f2f)
      | _ -> Coq_cast_case_default))
| Tpointer (t, a) ->
  (match tfrom with
   | Tvoid -> Coq_cast_case_default
   | Tlong (s, a0) -> Coq_cast_case_l2i (I32, Unsigned)
   | Tfloat (f, a0) -> Coq_cast_case_default
   | Tstruct (i, f, a0) -> Coq_cast_case_default
   | Tunion (i, f, a0) -> Coq_cast_case_default
   | _ -> Coq_cast_case_neutral)
| Tstruct (id2, fld2, a) ->
  (match tfrom with
   | Tstruct (id1, fld1, a0) -> Coq_cast_case_struct (id1, fld1, id2, fld2)
   | _ -> Coq_cast_case_default)
| Tunion (id2, fld2, a) ->
  (match tfrom with
   | Tunion (id1, fld1, a0) -> Coq_cast_case_union (id1, fld1, id2, fld2)
   | _ -> Coq_cast_case_default)
| Tcomp_ptr (i, a) ->
  (match tfrom with
   | Tvoid -> Coq_cast_case_default
   | Tlong (s, a0) -> Coq_cast_case_l2i (I32, Unsigned)
   | Tfloat (f, a0) -> Coq_cast_case_default
   | Tstruct (i0, f, a0) -> Coq_cast_case_default
   | Tunion (i0, f, a0) -> Coq_cast_case_default
   | _ -> Coq_cast_case_neutral)
| _ -> Coq_cast_case_default

(** val cast_int_int : intsize -> signedness -> Int.int -> Int.int **)

let cast_int_int sz sg i =
  match sz with
  | I8 ->
    (match sg with
     | Signed -> Int.sign_ext (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) i
     | Unsigned -> Int.zero_ext (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) i)
  | I16 ->
    (match sg with
     | Signed ->
       Int.sign_ext (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) i
     | Unsigned ->
       Int.zero_ext (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) i)
  | I32 -> i
  | IBool -> if Int.eq i Int.zero then Int.zero else Int.one

(** val cast_int_float : signedness -> Int.int -> float **)

let cast_int_float si i =
  match si with
  | Signed -> Float.of_int i
  | Unsigned -> Float.of_intu i

(** val cast_float_int : signedness -> float -> Int.int option **)

let cast_float_int si f =
  match si with
  | Signed -> Float.to_int f
  | Unsigned -> Float.to_intu f

(** val cast_int_single : signedness -> Int.int -> float32 **)

let cast_int_single si i =
  match si with
  | Signed -> Float32.of_int i
  | Unsigned -> Float32.of_intu i

(** val cast_single_int : signedness -> float32 -> Int.int option **)

let cast_single_int si f =
  match si with
  | Signed -> Float32.to_int f
  | Unsigned -> Float32.to_intu f

(** val cast_int_long : signedness -> Int.int -> Int64.int **)

let cast_int_long si i =
  match si with
  | Signed -> Int64.repr (Int.signed i)
  | Unsigned -> Int64.repr (Int.unsigned i)

(** val cast_long_float : signedness -> Int64.int -> float **)

let cast_long_float si i =
  match si with
  | Signed -> Float.of_long i
  | Unsigned -> Float.of_longu i

(** val cast_long_single : signedness -> Int64.int -> float32 **)

let cast_long_single si i =
  match si with
  | Signed -> Float32.of_long i
  | Unsigned -> Float32.of_longu i

(** val cast_float_long : signedness -> float -> Int64.int option **)

let cast_float_long si f =
  match si with
  | Signed -> Float.to_long f
  | Unsigned -> Float.to_longu f

(** val cast_single_long : signedness -> float32 -> Int64.int option **)

let cast_single_long si f =
  match si with
  | Signed -> Float32.to_long f
  | Unsigned -> Float32.to_longu f

(** val sem_cast : coq_val -> coq_type -> coq_type -> coq_val option **)

let sem_cast v t1 t2 =
  match classify_cast t1 t2 with
  | Coq_cast_case_neutral ->
    (match v with
     | Vint i -> Some v
     | Vptr (b, i) -> Some v
     | _ -> None)
  | Coq_cast_case_i2i (sz2, si2) ->
    (match v with
     | Vint i -> Some (Vint (cast_int_int sz2 si2 i))
     | _ -> None)
  | Coq_cast_case_f2f ->
    (match v with
     | Vfloat f -> Some (Vfloat f)
     | _ -> None)
  | Coq_cast_case_s2s ->
    (match v with
     | Vsingle f -> Some (Vsingle f)
     | _ -> None)
  | Coq_cast_case_f2s ->
    (match v with
     | Vfloat f -> Some (Vsingle (Float.to_single f))
     | _ -> None)
  | Coq_cast_case_s2f ->
    (match v with
     | Vsingle f -> Some (Vfloat (Float.of_single f))
     | _ -> None)
  | Coq_cast_case_i2f si1 ->
    (match v with
     | Vint i -> Some (Vfloat (cast_int_float si1 i))
     | _ -> None)
  | Coq_cast_case_i2s si1 ->
    (match v with
     | Vint i -> Some (Vsingle (cast_int_single si1 i))
     | _ -> None)
  | Coq_cast_case_f2i (sz2, si2) ->
    (match v with
     | Vfloat f ->
       (match cast_float_int si2 f with
        | Some i -> Some (Vint (cast_int_int sz2 si2 i))
        | None -> None)
     | _ -> None)
  | Coq_cast_case_s2i (sz2, si2) ->
    (match v with
     | Vsingle f ->
       (match cast_single_int si2 f with
        | Some i -> Some (Vint (cast_int_int sz2 si2 i))
        | None -> None)
     | _ -> None)
  | Coq_cast_case_l2l ->
    (match v with
     | Vlong n -> Some (Vlong n)
     | _ -> None)
  | Coq_cast_case_i2l si ->
    (match v with
     | Vint n -> Some (Vlong (cast_int_long si n))
     | _ -> None)
  | Coq_cast_case_l2i (sz, si) ->
    (match v with
     | Vlong n ->
       Some (Vint (cast_int_int sz si (Int.repr (Int64.unsigned n))))
     | _ -> None)
  | Coq_cast_case_l2f si1 ->
    (match v with
     | Vlong i -> Some (Vfloat (cast_long_float si1 i))
     | _ -> None)
  | Coq_cast_case_l2s si1 ->
    (match v with
     | Vlong i -> Some (Vsingle (cast_long_single si1 i))
     | _ -> None)
  | Coq_cast_case_f2l si2 ->
    (match v with
     | Vfloat f ->
       (match cast_float_long si2 f with
        | Some i -> Some (Vlong i)
        | None -> None)
     | _ -> None)
  | Coq_cast_case_s2l si2 ->
    (match v with
     | Vsingle f ->
       (match cast_single_long si2 f with
        | Some i -> Some (Vlong i)
        | None -> None)
     | _ -> None)
  | Coq_cast_case_f2bool ->
    (match v with
     | Vfloat f ->
       Some (Vint (if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
     | _ -> None)
  | Coq_cast_case_s2bool ->
    (match v with
     | Vsingle f ->
       Some (Vint
         (if Float32.cmp Ceq f Float32.zero then Int.zero else Int.one))
     | _ -> None)
  | Coq_cast_case_l2bool ->
    (match v with
     | Vlong n ->
       Some (Vint (if Int64.eq n Int64.zero then Int.zero else Int.one))
     | _ -> None)
  | Coq_cast_case_p2bool ->
    (match v with
     | Vint i -> Some (Vint (cast_int_int IBool Signed i))
     | Vptr (b, i) -> Some (Vint Int.one)
     | _ -> None)
  | Coq_cast_case_struct (id1, fld1, id2, fld2) ->
    (match v with
     | Vptr (b, ofs) ->
       if (&&) ((fun x -> x) (ident_eq id1 id2))
            ((fun x -> x) (fieldlist_eq fld1 fld2))
       then Some v
       else None
     | _ -> None)
  | Coq_cast_case_union (id1, fld1, id2, fld2) ->
    (match v with
     | Vptr (b, ofs) ->
       if (&&) ((fun x -> x) (ident_eq id1 id2))
            ((fun x -> x) (fieldlist_eq fld1 fld2))
       then Some v
       else None
     | _ -> None)
  | Coq_cast_case_void -> Some v
  | Coq_cast_case_default -> None

type classify_bool_cases =
| Coq_bool_case_i
| Coq_bool_case_f
| Coq_bool_case_s
| Coq_bool_case_p
| Coq_bool_case_l
| Coq_bool_default

(** val classify_bool : coq_type -> classify_bool_cases **)

let classify_bool ty =
  match typeconv ty with
  | Tint (i, s, a) -> Coq_bool_case_i
  | Tlong (s, a) -> Coq_bool_case_l
  | Tfloat (f, a) ->
    (match f with
     | F32 -> Coq_bool_case_s
     | F64 -> Coq_bool_case_f)
  | Tpointer (t, a) -> Coq_bool_case_p
  | Tcomp_ptr (i, a) -> Coq_bool_case_p
  | _ -> Coq_bool_default

(** val bool_val : coq_val -> coq_type -> bool option **)

let bool_val v t =
  match classify_bool t with
  | Coq_bool_case_i ->
    (match v with
     | Vint n -> Some (negb (Int.eq n Int.zero))
     | _ -> None)
  | Coq_bool_case_f ->
    (match v with
     | Vfloat f -> Some (negb (Float.cmp Ceq f Float.zero))
     | _ -> None)
  | Coq_bool_case_s ->
    (match v with
     | Vsingle f -> Some (negb (Float32.cmp Ceq f Float32.zero))
     | _ -> None)
  | Coq_bool_case_p ->
    (match v with
     | Vint n -> Some (negb (Int.eq n Int.zero))
     | Vptr (b, ofs) -> Some true
     | _ -> None)
  | Coq_bool_case_l ->
    (match v with
     | Vlong n -> Some (negb (Int64.eq n Int64.zero))
     | _ -> None)
  | Coq_bool_default -> None

(** val sem_notbool : coq_val -> coq_type -> coq_val option **)

let sem_notbool v ty =
  match classify_bool ty with
  | Coq_bool_case_i ->
    (match v with
     | Vint n -> Some (Val.of_bool (Int.eq n Int.zero))
     | _ -> None)
  | Coq_bool_case_f ->
    (match v with
     | Vfloat f -> Some (Val.of_bool (Float.cmp Ceq f Float.zero))
     | _ -> None)
  | Coq_bool_case_s ->
    (match v with
     | Vsingle f -> Some (Val.of_bool (Float32.cmp Ceq f Float32.zero))
     | _ -> None)
  | Coq_bool_case_p ->
    (match v with
     | Vint n -> Some (Val.of_bool (Int.eq n Int.zero))
     | Vptr (b, i) -> Some coq_Vfalse
     | _ -> None)
  | Coq_bool_case_l ->
    (match v with
     | Vlong n -> Some (Val.of_bool (Int64.eq n Int64.zero))
     | _ -> None)
  | Coq_bool_default -> None

type classify_neg_cases =
| Coq_neg_case_i of signedness
| Coq_neg_case_f
| Coq_neg_case_s
| Coq_neg_case_l of signedness
| Coq_neg_default

(** val classify_neg : coq_type -> classify_neg_cases **)

let classify_neg = function
| Tint (i, s, a) ->
  (match i with
   | I32 -> Coq_neg_case_i s
   | _ -> Coq_neg_case_i Signed)
| Tlong (si, a) -> Coq_neg_case_l si
| Tfloat (f, a) ->
  (match f with
   | F32 -> Coq_neg_case_s
   | F64 -> Coq_neg_case_f)
| _ -> Coq_neg_default

(** val sem_neg : coq_val -> coq_type -> coq_val option **)

let sem_neg v ty =
  match classify_neg ty with
  | Coq_neg_case_i sg ->
    (match v with
     | Vint n -> Some (Vint (Int.neg n))
     | _ -> None)
  | Coq_neg_case_f ->
    (match v with
     | Vfloat f -> Some (Vfloat (Float.neg f))
     | _ -> None)
  | Coq_neg_case_s ->
    (match v with
     | Vsingle f -> Some (Vsingle (Float32.neg f))
     | _ -> None)
  | Coq_neg_case_l sg ->
    (match v with
     | Vlong n -> Some (Vlong (Int64.neg n))
     | _ -> None)
  | Coq_neg_default -> None

(** val sem_absfloat : coq_val -> coq_type -> coq_val option **)

let sem_absfloat v ty =
  match classify_neg ty with
  | Coq_neg_case_i sg ->
    (match v with
     | Vint n -> Some (Vfloat (Float.abs (cast_int_float sg n)))
     | _ -> None)
  | Coq_neg_case_f ->
    (match v with
     | Vfloat f -> Some (Vfloat (Float.abs f))
     | _ -> None)
  | Coq_neg_case_s ->
    (match v with
     | Vsingle f -> Some (Vfloat (Float.abs (Float.of_single f)))
     | _ -> None)
  | Coq_neg_case_l sg ->
    (match v with
     | Vlong n -> Some (Vfloat (Float.abs (cast_long_float sg n)))
     | _ -> None)
  | Coq_neg_default -> None

type classify_notint_cases =
| Coq_notint_case_i of signedness
| Coq_notint_case_l of signedness
| Coq_notint_default

(** val classify_notint : coq_type -> classify_notint_cases **)

let classify_notint = function
| Tint (i, s, a) ->
  (match i with
   | I32 -> Coq_notint_case_i s
   | _ -> Coq_notint_case_i Signed)
| Tlong (si, a) -> Coq_notint_case_l si
| _ -> Coq_notint_default

(** val sem_notint : coq_val -> coq_type -> coq_val option **)

let sem_notint v ty =
  match classify_notint ty with
  | Coq_notint_case_i sg ->
    (match v with
     | Vint n -> Some (Vint (Int.not n))
     | _ -> None)
  | Coq_notint_case_l sg ->
    (match v with
     | Vlong n -> Some (Vlong (Int64.not n))
     | _ -> None)
  | Coq_notint_default -> None

type binarith_cases =
| Coq_bin_case_i of signedness
| Coq_bin_case_l of signedness
| Coq_bin_case_f
| Coq_bin_case_s
| Coq_bin_default

(** val classify_binarith : coq_type -> coq_type -> binarith_cases **)

let classify_binarith ty1 ty2 =
  match ty1 with
  | Tint (i, s, a) ->
    (match i with
     | I32 ->
       (match s with
        | Signed ->
          (match ty2 with
           | Tint (i0, s0, a0) ->
             (match i0 with
              | I32 -> Coq_bin_case_i s0
              | _ -> Coq_bin_case_i Signed)
           | Tlong (sg, a0) -> Coq_bin_case_l sg
           | Tfloat (f, a0) ->
             (match f with
              | F32 -> Coq_bin_case_s
              | F64 -> Coq_bin_case_f)
           | _ -> Coq_bin_default)
        | Unsigned ->
          (match ty2 with
           | Tint (i0, s0, a0) -> Coq_bin_case_i Unsigned
           | Tlong (sg, a0) -> Coq_bin_case_l sg
           | Tfloat (f, a0) ->
             (match f with
              | F32 -> Coq_bin_case_s
              | F64 -> Coq_bin_case_f)
           | _ -> Coq_bin_default))
     | _ ->
       (match ty2 with
        | Tint (i0, s0, a0) ->
          (match i0 with
           | I32 -> Coq_bin_case_i s0
           | _ -> Coq_bin_case_i Signed)
        | Tlong (sg, a0) -> Coq_bin_case_l sg
        | Tfloat (f, a0) ->
          (match f with
           | F32 -> Coq_bin_case_s
           | F64 -> Coq_bin_case_f)
        | _ -> Coq_bin_default))
  | Tlong (sg, a) ->
    (match sg with
     | Signed ->
       (match ty2 with
        | Tint (i, s, a0) -> Coq_bin_case_l sg
        | Tlong (s, a0) -> Coq_bin_case_l s
        | Tfloat (f, a0) ->
          (match f with
           | F32 -> Coq_bin_case_s
           | F64 -> Coq_bin_case_f)
        | _ -> Coq_bin_default)
     | Unsigned ->
       (match ty2 with
        | Tint (i, s, a0) -> Coq_bin_case_l sg
        | Tlong (s, a0) -> Coq_bin_case_l Unsigned
        | Tfloat (f, a0) ->
          (match f with
           | F32 -> Coq_bin_case_s
           | F64 -> Coq_bin_case_f)
        | _ -> Coq_bin_default))
  | Tfloat (f, a) ->
    (match f with
     | F32 ->
       (match ty2 with
        | Tint (i, s, a0) -> Coq_bin_case_s
        | Tlong (s, a0) -> Coq_bin_case_s
        | Tfloat (f0, a0) ->
          (match f0 with
           | F32 -> Coq_bin_case_s
           | F64 -> Coq_bin_case_f)
        | _ -> Coq_bin_default)
     | F64 ->
       (match ty2 with
        | Tint (i, s, a0) -> Coq_bin_case_f
        | Tlong (s, a0) -> Coq_bin_case_f
        | Tfloat (f0, a0) -> Coq_bin_case_f
        | _ -> Coq_bin_default))
  | _ -> Coq_bin_default

(** val binarith_type : binarith_cases -> coq_type **)

let binarith_type = function
| Coq_bin_case_i sg -> Tint (I32, sg, noattr)
| Coq_bin_case_l sg -> Tlong (sg, noattr)
| Coq_bin_case_f -> Tfloat (F64, noattr)
| Coq_bin_case_s -> Tfloat (F32, noattr)
| Coq_bin_default -> Tvoid

(** val sem_binarith :
    (signedness -> Int.int -> Int.int -> coq_val option) -> (signedness ->
    Int64.int -> Int64.int -> coq_val option) -> (float -> float -> coq_val
    option) -> (float32 -> float32 -> coq_val option) -> coq_val -> coq_type
    -> coq_val -> coq_type -> coq_val option **)

let sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 =
  let c = classify_binarith t1 t2 in
  let t = binarith_type c in
  (match sem_cast v1 t1 t with
   | Some v1' ->
     (match sem_cast v2 t2 t with
      | Some v2' ->
        (match c with
         | Coq_bin_case_i sg ->
           (match v1' with
            | Vint n1 ->
              (match v2' with
               | Vint n2 -> sem_int sg n1 n2
               | _ -> None)
            | _ -> None)
         | Coq_bin_case_l sg ->
           (match v1' with
            | Vlong n1 ->
              (match v2' with
               | Vlong n2 -> sem_long sg n1 n2
               | _ -> None)
            | _ -> None)
         | Coq_bin_case_f ->
           (match v1' with
            | Vfloat n1 ->
              (match v2' with
               | Vfloat n2 -> sem_float n1 n2
               | _ -> None)
            | _ -> None)
         | Coq_bin_case_s ->
           (match v1' with
            | Vsingle n1 ->
              (match v2' with
               | Vsingle n2 -> sem_single n1 n2
               | _ -> None)
            | _ -> None)
         | Coq_bin_default -> None)
      | None -> None)
   | None -> None)

type classify_add_cases =
| Coq_add_case_pi of coq_type
| Coq_add_case_ip of coq_type
| Coq_add_case_pl of coq_type
| Coq_add_case_lp of coq_type
| Coq_add_default

(** val classify_add : coq_type -> coq_type -> classify_add_cases **)

let classify_add ty1 ty2 =
  match typeconv ty1 with
  | Tint (i, s, a) ->
    (match typeconv ty2 with
     | Tpointer (ty, a0) -> Coq_add_case_ip ty
     | _ -> Coq_add_default)
  | Tlong (s, a) ->
    (match typeconv ty2 with
     | Tpointer (ty, a0) -> Coq_add_case_lp ty
     | _ -> Coq_add_default)
  | Tpointer (ty, a) ->
    (match typeconv ty2 with
     | Tint (i, s, a0) -> Coq_add_case_pi ty
     | Tlong (s, a0) -> Coq_add_case_pl ty
     | _ -> Coq_add_default)
  | _ -> Coq_add_default

(** val sem_add :
    coq_val -> coq_type -> coq_val -> coq_type -> coq_val option **)

let sem_add v1 t1 v2 t2 =
  match classify_add t1 t2 with
  | Coq_add_case_pi ty ->
    (match v1 with
     | Vptr (b1, ofs1) ->
       (match v2 with
        | Vint n2 ->
          Some (Vptr (b1,
            (Int.add ofs1 (Int.mul (Int.repr (sizeof ty)) n2))))
        | _ -> None)
     | _ -> None)
  | Coq_add_case_ip ty ->
    (match v1 with
     | Vint n1 ->
       (match v2 with
        | Vptr (b2, ofs2) ->
          Some (Vptr (b2,
            (Int.add ofs2 (Int.mul (Int.repr (sizeof ty)) n1))))
        | _ -> None)
     | _ -> None)
  | Coq_add_case_pl ty ->
    (match v1 with
     | Vptr (b1, ofs1) ->
       (match v2 with
        | Vlong n2 ->
          let n3 = Int.repr (Int64.unsigned n2) in
          Some (Vptr (b1,
          (Int.add ofs1 (Int.mul (Int.repr (sizeof ty)) n3))))
        | _ -> None)
     | _ -> None)
  | Coq_add_case_lp ty ->
    (match v1 with
     | Vlong n1 ->
       (match v2 with
        | Vptr (b2, ofs2) ->
          let n2 = Int.repr (Int64.unsigned n1) in
          Some (Vptr (b2,
          (Int.add ofs2 (Int.mul (Int.repr (sizeof ty)) n2))))
        | _ -> None)
     | _ -> None)
  | Coq_add_default ->
    sem_binarith (fun sg n1 n2 -> Some (Vint (Int.add n1 n2)))
      (fun sg n1 n2 -> Some (Vlong (Int64.add n1 n2))) (fun n1 n2 -> Some
      (Vfloat (Float.add n1 n2))) (fun n1 n2 -> Some (Vsingle
      (Float32.add n1 n2))) v1 t1 v2 t2

type classify_sub_cases =
| Coq_sub_case_pi of coq_type
| Coq_sub_case_pp of coq_type
| Coq_sub_case_pl of coq_type
| Coq_sub_default

(** val classify_sub : coq_type -> coq_type -> classify_sub_cases **)

let classify_sub ty1 ty2 =
  match typeconv ty1 with
  | Tpointer (ty, a) ->
    (match typeconv ty2 with
     | Tint (i, s, a0) -> Coq_sub_case_pi ty
     | Tlong (s, a0) -> Coq_sub_case_pl ty
     | Tpointer (t, a0) -> Coq_sub_case_pp ty
     | _ -> Coq_sub_default)
  | _ -> Coq_sub_default

(** val sem_sub :
    coq_val -> coq_type -> coq_val -> coq_type -> coq_val option **)

let sem_sub v1 t1 v2 t2 =
  match classify_sub t1 t2 with
  | Coq_sub_case_pi ty ->
    (match v1 with
     | Vptr (b1, ofs1) ->
       (match v2 with
        | Vint n2 ->
          Some (Vptr (b1,
            (Int.sub ofs1 (Int.mul (Int.repr (sizeof ty)) n2))))
        | _ -> None)
     | _ -> None)
  | Coq_sub_case_pp ty ->
    (match v1 with
     | Vptr (b1, ofs1) ->
       (match v2 with
        | Vptr (b2, ofs2) ->
          if eq_block b1 b2
          then if Int.eq (Int.repr (sizeof ty)) Int.zero
               then None
               else Some (Vint
                      (Int.divu (Int.sub ofs1 ofs2) (Int.repr (sizeof ty))))
          else None
        | _ -> None)
     | _ -> None)
  | Coq_sub_case_pl ty ->
    (match v1 with
     | Vptr (b1, ofs1) ->
       (match v2 with
        | Vlong n2 ->
          let n3 = Int.repr (Int64.unsigned n2) in
          Some (Vptr (b1,
          (Int.sub ofs1 (Int.mul (Int.repr (sizeof ty)) n3))))
        | _ -> None)
     | _ -> None)
  | Coq_sub_default ->
    sem_binarith (fun sg n1 n2 -> Some (Vint (Int.sub n1 n2)))
      (fun sg n1 n2 -> Some (Vlong (Int64.sub n1 n2))) (fun n1 n2 -> Some
      (Vfloat (Float.sub n1 n2))) (fun n1 n2 -> Some (Vsingle
      (Float32.sub n1 n2))) v1 t1 v2 t2

(** val sem_mul :
    coq_val -> coq_type -> coq_val -> coq_type -> coq_val option **)

let sem_mul v1 t1 v2 t2 =
  sem_binarith (fun sg n1 n2 -> Some (Vint (Int.mul n1 n2))) (fun sg n1 n2 ->
    Some (Vlong (Int64.mul n1 n2))) (fun n1 n2 -> Some (Vfloat
    (Float.mul n1 n2))) (fun n1 n2 -> Some (Vsingle (Float32.mul n1 n2))) v1
    t1 v2 t2

(** val sem_div :
    coq_val -> coq_type -> coq_val -> coq_type -> coq_val option **)

let sem_div v1 t1 v2 t2 =
  sem_binarith (fun sg n1 n2 ->
    match sg with
    | Signed ->
      if (||) (Int.eq n2 Int.zero)
           ((&&) (Int.eq n1 (Int.repr Int.min_signed)) (Int.eq n2 Int.mone))
      then None
      else Some (Vint (Int.divs n1 n2))
    | Unsigned ->
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2)))
    (fun sg n1 n2 ->
    match sg with
    | Signed ->
      if (||) (Int64.eq n2 Int64.zero)
           ((&&) (Int64.eq n1 (Int64.repr Int64.min_signed))
             (Int64.eq n2 Int64.mone))
      then None
      else Some (Vlong (Int64.divs n1 n2))
    | Unsigned ->
      if Int64.eq n2 Int64.zero
      then None
      else Some (Vlong (Int64.divu n1 n2))) (fun n1 n2 -> Some (Vfloat
    (Float.div n1 n2))) (fun n1 n2 -> Some (Vsingle (Float32.div n1 n2))) v1
    t1 v2 t2

(** val sem_mod :
    coq_val -> coq_type -> coq_val -> coq_type -> coq_val option **)

let sem_mod v1 t1 v2 t2 =
  sem_binarith (fun sg n1 n2 ->
    match sg with
    | Signed ->
      if (||) (Int.eq n2 Int.zero)
           ((&&) (Int.eq n1 (Int.repr Int.min_signed)) (Int.eq n2 Int.mone))
      then None
      else Some (Vint (Int.mods n1 n2))
    | Unsigned ->
      if Int.eq n2 Int.zero then None else Some (Vint (Int.modu n1 n2)))
    (fun sg n1 n2 ->
    match sg with
    | Signed ->
      if (||) (Int64.eq n2 Int64.zero)
           ((&&) (Int64.eq n1 (Int64.repr Int64.min_signed))
             (Int64.eq n2 Int64.mone))
      then None
      else Some (Vlong (Int64.mods n1 n2))
    | Unsigned ->
      if Int64.eq n2 Int64.zero
      then None
      else Some (Vlong (Int64.modu n1 n2))) (fun n1 n2 -> None) (fun n1 n2 ->
    None) v1 t1 v2 t2

(** val sem_and :
    coq_val -> coq_type -> coq_val -> coq_type -> coq_val option **)

let sem_and v1 t1 v2 t2 =
  sem_binarith (fun sg n1 n2 -> Some (Vint (Int.coq_and n1 n2)))
    (fun sg n1 n2 -> Some (Vlong (Int64.coq_and n1 n2))) (fun n1 n2 -> None)
    (fun n1 n2 -> None) v1 t1 v2 t2

(** val sem_or :
    coq_val -> coq_type -> coq_val -> coq_type -> coq_val option **)

let sem_or v1 t1 v2 t2 =
  sem_binarith (fun sg n1 n2 -> Some (Vint (Int.coq_or n1 n2)))
    (fun sg n1 n2 -> Some (Vlong (Int64.coq_or n1 n2))) (fun n1 n2 -> None)
    (fun n1 n2 -> None) v1 t1 v2 t2

(** val sem_xor :
    coq_val -> coq_type -> coq_val -> coq_type -> coq_val option **)

let sem_xor v1 t1 v2 t2 =
  sem_binarith (fun sg n1 n2 -> Some (Vint (Int.xor n1 n2))) (fun sg n1 n2 ->
    Some (Vlong (Int64.xor n1 n2))) (fun n1 n2 -> None) (fun n1 n2 -> None)
    v1 t1 v2 t2

type classify_shift_cases =
| Coq_shift_case_ii of signedness
| Coq_shift_case_ll of signedness
| Coq_shift_case_il of signedness
| Coq_shift_case_li of signedness
| Coq_shift_default

(** val classify_shift : coq_type -> coq_type -> classify_shift_cases **)

let classify_shift ty1 ty2 =
  match typeconv ty1 with
  | Tint (i, s, a) ->
    (match i with
     | I32 ->
       (match typeconv ty2 with
        | Tint (i0, s0, a0) -> Coq_shift_case_ii s
        | Tlong (s0, a0) -> Coq_shift_case_il s
        | _ -> Coq_shift_default)
     | _ ->
       (match typeconv ty2 with
        | Tint (i0, s0, a0) -> Coq_shift_case_ii Signed
        | Tlong (s0, a0) -> Coq_shift_case_il Signed
        | _ -> Coq_shift_default))
  | Tlong (s, a) ->
    (match typeconv ty2 with
     | Tint (i, s0, a0) -> Coq_shift_case_li s
     | Tlong (s0, a0) -> Coq_shift_case_ll s
     | _ -> Coq_shift_default)
  | _ -> Coq_shift_default

(** val sem_shift :
    (signedness -> Int.int -> Int.int -> Int.int) -> (signedness -> Int64.int
    -> Int64.int -> Int64.int) -> coq_val -> coq_type -> coq_val -> coq_type
    -> coq_val option **)

let sem_shift sem_int sem_long v1 t1 v2 t2 =
  match classify_shift t1 t2 with
  | Coq_shift_case_ii sg ->
    (match v1 with
     | Vint n1 ->
       (match v2 with
        | Vint n2 ->
          if Int.ltu n2 Int.iwordsize
          then Some (Vint (sem_int sg n1 n2))
          else None
        | _ -> None)
     | _ -> None)
  | Coq_shift_case_ll sg ->
    (match v1 with
     | Vlong n1 ->
       (match v2 with
        | Vlong n2 ->
          if Int64.ltu n2 Int64.iwordsize
          then Some (Vlong (sem_long sg n1 n2))
          else None
        | _ -> None)
     | _ -> None)
  | Coq_shift_case_il sg ->
    (match v1 with
     | Vint n1 ->
       (match v2 with
        | Vlong n2 ->
          if Int64.ltu n2
               (Int64.repr (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                 Coq_xH)))))))
          then Some (Vint (sem_int sg n1 (Int64.loword n2)))
          else None
        | _ -> None)
     | _ -> None)
  | Coq_shift_case_li sg ->
    (match v1 with
     | Vlong n1 ->
       (match v2 with
        | Vint n2 ->
          if Int.ltu n2 Int64.iwordsize'
          then Some (Vlong (sem_long sg n1 (Int64.repr (Int.unsigned n2))))
          else None
        | _ -> None)
     | _ -> None)
  | Coq_shift_default -> None

(** val sem_shl :
    coq_val -> coq_type -> coq_val -> coq_type -> coq_val option **)

let sem_shl v1 t1 v2 t2 =
  sem_shift (fun sg n1 n2 -> Int.shl n1 n2) (fun sg n1 n2 -> Int64.shl n1 n2)
    v1 t1 v2 t2

(** val sem_shr :
    coq_val -> coq_type -> coq_val -> coq_type -> coq_val option **)

let sem_shr v1 t1 v2 t2 =
  sem_shift (fun sg n1 n2 ->
    match sg with
    | Signed -> Int.shr n1 n2
    | Unsigned -> Int.shru n1 n2) (fun sg n1 n2 ->
    match sg with
    | Signed -> Int64.shr n1 n2
    | Unsigned -> Int64.shru n1 n2) v1 t1 v2 t2

type classify_cmp_cases =
| Coq_cmp_case_pp
| Coq_cmp_case_pl
| Coq_cmp_case_lp
| Coq_cmp_default

(** val classify_cmp : coq_type -> coq_type -> classify_cmp_cases **)

let classify_cmp ty1 ty2 =
  match typeconv ty1 with
  | Tint (i, s, a) ->
    (match typeconv ty2 with
     | Tpointer (t, a0) -> Coq_cmp_case_pp
     | _ -> Coq_cmp_default)
  | Tlong (s, a) ->
    (match typeconv ty2 with
     | Tpointer (t, a0) -> Coq_cmp_case_lp
     | _ -> Coq_cmp_default)
  | Tpointer (t, a) ->
    (match typeconv ty2 with
     | Tint (i, s, a0) -> Coq_cmp_case_pp
     | Tlong (s, a0) -> Coq_cmp_case_pl
     | Tpointer (t0, a0) -> Coq_cmp_case_pp
     | _ -> Coq_cmp_default)
  | _ -> Coq_cmp_default

(** val sem_cmp :
    comparison -> coq_val -> coq_type -> coq_val -> coq_type -> Mem.mem ->
    coq_val option **)

let sem_cmp c v1 t1 v2 t2 m =
  match classify_cmp t1 t2 with
  | Coq_cmp_case_pp ->
    option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2)
  | Coq_cmp_case_pl ->
    (match v2 with
     | Vlong n2 ->
       let n3 = Int.repr (Int64.unsigned n2) in
       option_map Val.of_bool
         (Val.cmpu_bool (Mem.valid_pointer m) c v1 (Vint n3))
     | _ -> None)
  | Coq_cmp_case_lp ->
    (match v1 with
     | Vlong n1 ->
       let n2 = Int.repr (Int64.unsigned n1) in
       option_map Val.of_bool
         (Val.cmpu_bool (Mem.valid_pointer m) c (Vint n2) v2)
     | _ -> None)
  | Coq_cmp_default ->
    sem_binarith (fun sg n1 n2 -> Some
      (Val.of_bool
        (match sg with
         | Signed -> Int.cmp c n1 n2
         | Unsigned -> Int.cmpu c n1 n2))) (fun sg n1 n2 -> Some
      (Val.of_bool
        (match sg with
         | Signed -> Int64.cmp c n1 n2
         | Unsigned -> Int64.cmpu c n1 n2))) (fun n1 n2 -> Some
      (Val.of_bool (Float.cmp c n1 n2))) (fun n1 n2 -> Some
      (Val.of_bool (Float32.cmp c n1 n2))) v1 t1 v2 t2

type classify_fun_cases =
| Coq_fun_case_f of typelist * coq_type * calling_convention
| Coq_fun_default

(** val classify_fun : coq_type -> classify_fun_cases **)

let classify_fun = function
| Tpointer (t, a) ->
  (match t with
   | Tfunction (args, res, cc) -> Coq_fun_case_f (args, res, cc)
   | _ -> Coq_fun_default)
| Tfunction (args, res, cc) -> Coq_fun_case_f (args, res, cc)
| _ -> Coq_fun_default

type classify_switch_cases =
| Coq_switch_case_i
| Coq_switch_case_l
| Coq_switch_default

(** val classify_switch : coq_type -> classify_switch_cases **)

let classify_switch = function
| Tint (i, s, a) -> Coq_switch_case_i
| Tlong (s, a) -> Coq_switch_case_l
| _ -> Coq_switch_default

(** val sem_switch_arg : coq_val -> coq_type -> coq_Z option **)

let sem_switch_arg v ty =
  match classify_switch ty with
  | Coq_switch_case_i ->
    (match v with
     | Vint n -> Some (Int.unsigned n)
     | _ -> None)
  | Coq_switch_case_l ->
    (match v with
     | Vlong n -> Some (Int64.unsigned n)
     | _ -> None)
  | Coq_switch_default -> None

(** val sem_unary_operation :
    unary_operation -> coq_val -> coq_type -> coq_val option **)

let sem_unary_operation op v ty =
  match op with
  | Onotbool -> sem_notbool v ty
  | Onotint -> sem_notint v ty
  | Oneg -> sem_neg v ty
  | Oabsfloat -> sem_absfloat v ty

(** val sem_binary_operation :
    binary_operation -> coq_val -> coq_type -> coq_val -> coq_type -> Mem.mem
    -> coq_val option **)

let sem_binary_operation op v1 t1 v2 t2 m =
  match op with
  | Oadd -> sem_add v1 t1 v2 t2
  | Osub -> sem_sub v1 t1 v2 t2
  | Omul -> sem_mul v1 t1 v2 t2
  | Odiv -> sem_div v1 t1 v2 t2
  | Omod -> sem_mod v1 t1 v2 t2
  | Oand -> sem_and v1 t1 v2 t2
  | Oor -> sem_or v1 t1 v2 t2
  | Oxor -> sem_xor v1 t1 v2 t2
  | Oshl -> sem_shl v1 t1 v2 t2
  | Oshr -> sem_shr v1 t1 v2 t2
  | Oeq -> sem_cmp Ceq v1 t1 v2 t2 m
  | One -> sem_cmp Cne v1 t1 v2 t2 m
  | Olt -> sem_cmp Clt v1 t1 v2 t2 m
  | Ogt -> sem_cmp Cgt v1 t1 v2 t2 m
  | Ole -> sem_cmp Cle v1 t1 v2 t2 m
  | Oge -> sem_cmp Cge v1 t1 v2 t2 m

(** val incrdecr_type : coq_type -> coq_type **)

let incrdecr_type ty =
  match typeconv ty with
  | Tint (sz, sg, a) -> Tint (sz, sg, noattr)
  | Tlong (sg, a) -> Tlong (sg, noattr)
  | Tfloat (sz, a) -> Tfloat (sz, noattr)
  | Tpointer (ty0, a) -> Tpointer (ty0, a)
  | _ -> Tvoid

