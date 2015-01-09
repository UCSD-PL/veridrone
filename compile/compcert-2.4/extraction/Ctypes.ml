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

(** val attr_volatile : attr -> bool **)

let attr_volatile x = x.attr_volatile

(** val attr_alignas : attr -> coq_N option **)

let attr_alignas x = x.attr_alignas

(** val noattr : attr **)

let noattr =
  { attr_volatile = false; attr_alignas = None }

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

(** val type_eq : coq_type -> coq_type -> bool **)

let rec type_eq =
  let h = fun x y ->
    match x with
    | I8 ->
      (match y with
       | I8 -> true
       | _ -> false)
    | I16 ->
      (match y with
       | I16 -> true
       | _ -> false)
    | I32 ->
      (match y with
       | I32 -> true
       | _ -> false)
    | IBool ->
      (match y with
       | IBool -> true
       | _ -> false)
  in
  let h0 = fun x y ->
    match x with
    | Signed ->
      (match y with
       | Signed -> true
       | Unsigned -> false)
    | Unsigned ->
      (match y with
       | Signed -> false
       | Unsigned -> true)
  in
  let h1 = fun x y ->
    match x with
    | F32 ->
      (match y with
       | F32 -> true
       | F64 -> false)
    | F64 ->
      (match y with
       | F32 -> false
       | F64 -> true)
  in
  let h2 = fun x y ->
    let { attr_volatile = x0; attr_alignas = x1 } = x in
    let { attr_volatile = attr_volatile1; attr_alignas = attr_alignas1 } = y
    in
    if bool_dec x0 attr_volatile1
    then (match x1 with
          | Some x2 ->
            (match attr_alignas1 with
             | Some n -> N.eq_dec x2 n
             | None -> false)
          | None ->
            (match attr_alignas1 with
             | Some n -> false
             | None -> true))
    else false
  in
  (fun ty1 ty2 ->
  match ty1 with
  | Tvoid ->
    (match ty2 with
     | Tvoid -> true
     | _ -> false)
  | Tint (i, s, a) ->
    (match ty2 with
     | Tint (i0, s0, a0) ->
       if h i i0 then if h0 s s0 then h2 a a0 else false else false
     | _ -> false)
  | Tlong (s, a) ->
    (match ty2 with
     | Tlong (s0, a0) -> if h0 s s0 then h2 a a0 else false
     | _ -> false)
  | Tfloat (f, a) ->
    (match ty2 with
     | Tfloat (f0, a0) -> if h1 f f0 then h2 a a0 else false
     | _ -> false)
  | Tpointer (t, a) ->
    (match ty2 with
     | Tpointer (t0, a0) -> if type_eq t t0 then h2 a a0 else false
     | _ -> false)
  | Tarray (t, z, a) ->
    (match ty2 with
     | Tarray (t0, z0, a0) ->
       if type_eq t t0 then if zeq z z0 then h2 a a0 else false else false
     | _ -> false)
  | Tfunction (t, t0, c) ->
    (match ty2 with
     | Tfunction (t1, t2, c0) ->
       if typelist_eq t t1
       then if type_eq t0 t2
            then let { cc_vararg = x; cc_structret = x0 } = c in
                 let { cc_vararg = cc_vararg0; cc_structret =
                   cc_structret0 } = c0
                 in
                 if bool_dec x cc_vararg0
                 then bool_dec x0 cc_structret0
                 else false
            else false
       else false
     | _ -> false)
  | Tstruct (i, f, a) ->
    (match ty2 with
     | Tstruct (i0, f0, a0) ->
       if ident_eq i i0
       then if fieldlist_eq f f0 then h2 a a0 else false
       else false
     | _ -> false)
  | Tunion (i, f, a) ->
    (match ty2 with
     | Tunion (i0, f0, a0) ->
       if ident_eq i i0
       then if fieldlist_eq f f0 then h2 a a0 else false
       else false
     | _ -> false)
  | Tcomp_ptr (i, a) ->
    (match ty2 with
     | Tcomp_ptr (i0, a0) -> if ident_eq i i0 then h2 a a0 else false
     | _ -> false))

(** val typelist_eq : typelist -> typelist -> bool **)

and typelist_eq tyl1 tyl2 =
  match tyl1 with
  | Tnil ->
    (match tyl2 with
     | Tnil -> true
     | Tcons (t, t0) -> false)
  | Tcons (t, t0) ->
    (match tyl2 with
     | Tnil -> false
     | Tcons (t1, t2) -> if type_eq t t1 then typelist_eq t0 t2 else false)

(** val fieldlist_eq : fieldlist -> fieldlist -> bool **)

and fieldlist_eq fld1 fld2 =
  match fld1 with
  | Fnil ->
    (match fld2 with
     | Fnil -> true
     | Fcons (i, t, f) -> false)
  | Fcons (i, t, f) ->
    (match fld2 with
     | Fnil -> false
     | Fcons (i0, t0, f0) ->
       if ident_eq i i0
       then if type_eq t t0 then fieldlist_eq f f0 else false
       else false)

(** val attr_of_type : coq_type -> attr **)

let attr_of_type = function
| Tint (sz, si, a) -> a
| Tlong (si, a) -> a
| Tfloat (sz, a) -> a
| Tpointer (elt, a) -> a
| Tarray (elt, sz, a) -> a
| Tstruct (id, fld, a) -> a
| Tunion (id, fld, a) -> a
| Tcomp_ptr (id, a) -> a
| _ -> noattr

(** val change_attributes : (attr -> attr) -> coq_type -> coq_type **)

let change_attributes f ty = match ty with
| Tint (sz, si, a) -> Tint (sz, si, (f a))
| Tlong (si, a) -> Tlong (si, (f a))
| Tfloat (sz, a) -> Tfloat (sz, (f a))
| Tpointer (elt, a) -> Tpointer (elt, (f a))
| Tarray (elt, sz, a) -> Tarray (elt, sz, (f a))
| Tstruct (id, fld, a) -> Tstruct (id, fld, (f a))
| Tunion (id, fld, a) -> Tunion (id, fld, (f a))
| Tcomp_ptr (id, a) -> Tcomp_ptr (id, (f a))
| _ -> ty

(** val remove_attributes : coq_type -> coq_type **)

let remove_attributes ty =
  change_attributes (fun x -> noattr) ty

(** val attr_union : attr -> attr -> attr **)

let attr_union a1 a2 =
  { attr_volatile = ((||) a1.attr_volatile a2.attr_volatile); attr_alignas =
    (match a1.attr_alignas with
     | Some n1 ->
       (match a2.attr_alignas with
        | Some n2 -> Some (N.max n1 n2)
        | None -> Some n1)
     | None -> a2.attr_alignas) }

(** val merge_attributes : coq_type -> attr -> coq_type **)

let merge_attributes ty a =
  change_attributes (attr_union a) ty

(** val type_int32s : coq_type **)

let type_int32s =
  Tint (I32, Signed, noattr)

(** val type_bool : coq_type **)

let type_bool =
  Tint (IBool, Signed, noattr)

(** val typeconv : coq_type -> coq_type **)

let typeconv ty = match ty with
| Tint (i, s, a) ->
  (match i with
   | I32 -> remove_attributes ty
   | _ -> Tint (I32, Signed, noattr))
| Tarray (t, sz, a) -> Tpointer (t, noattr)
| Tfunction (t, t0, c) -> Tpointer (ty, noattr)
| _ -> remove_attributes ty

(** val default_argument_conversion : coq_type -> coq_type **)

let default_argument_conversion ty = match ty with
| Tint (i, s, a) ->
  (match i with
   | I32 -> remove_attributes ty
   | _ -> Tint (I32, Signed, noattr))
| Tfloat (f, a) -> Tfloat (F64, noattr)
| Tarray (t, sz, a) -> Tpointer (t, noattr)
| Tfunction (t, t0, c) -> Tpointer (ty, noattr)
| _ -> remove_attributes ty

(** val alignof : coq_type -> coq_Z **)

let rec alignof t =
  match (attr_of_type t).attr_alignas with
  | Some l -> two_p (Z.of_N l)
  | None ->
    (match t with
     | Tvoid -> Zpos Coq_xH
     | Tint (i, s, a) ->
       (match i with
        | I16 -> Zpos (Coq_xO Coq_xH)
        | I32 -> Zpos (Coq_xO (Coq_xO Coq_xH))
        | _ -> Zpos Coq_xH)
     | Tarray (t', z, a) -> alignof t'
     | Tfunction (t0, t1, c) -> Zpos Coq_xH
     | Tstruct (i, fld, a) -> alignof_fields fld
     | Tunion (i, fld, a) -> alignof_fields fld
     | _ -> Zpos (Coq_xO (Coq_xO Coq_xH)))

(** val alignof_fields : fieldlist -> coq_Z **)

and alignof_fields = function
| Fnil -> Zpos Coq_xH
| Fcons (id, t, f') -> Z.max (alignof t) (alignof_fields f')

(** val sizeof : coq_type -> coq_Z **)

let rec sizeof t = match t with
| Tint (i, s, a) ->
  (match i with
   | I16 -> Zpos (Coq_xO Coq_xH)
   | I32 -> Zpos (Coq_xO (Coq_xO Coq_xH))
   | _ -> Zpos Coq_xH)
| Tlong (s, a) -> Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
| Tfloat (f, a) ->
  (match f with
   | F32 -> Zpos (Coq_xO (Coq_xO Coq_xH))
   | F64 -> Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
| Tpointer (t0, a) -> Zpos (Coq_xO (Coq_xO Coq_xH))
| Tarray (t', n, a) -> Z.mul (sizeof t') (Z.max Z0 n)
| Tstruct (i, fld, a) -> align (sizeof_struct fld Z0) (alignof t)
| Tunion (i, fld, a) -> align (sizeof_union fld) (alignof t)
| Tcomp_ptr (i, a) -> Zpos (Coq_xO (Coq_xO Coq_xH))
| _ -> Zpos Coq_xH

(** val sizeof_struct : fieldlist -> coq_Z -> coq_Z **)

and sizeof_struct fld pos =
  match fld with
  | Fnil -> pos
  | Fcons (id, t, fld') ->
    sizeof_struct fld' (Z.add (align pos (alignof t)) (sizeof t))

(** val sizeof_union : fieldlist -> coq_Z **)

and sizeof_union = function
| Fnil -> Z0
| Fcons (id, t, fld') -> Z.max (sizeof t) (sizeof_union fld')

(** val field_offset_rec : ident -> fieldlist -> coq_Z -> coq_Z res **)

let rec field_offset_rec id fld pos =
  match fld with
  | Fnil ->
    Error ((MSG
      ('U'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('f'::('i'::('e'::('l'::('d'::(' '::[]))))))))))))))) :: ((CTX
      id) :: []))
  | Fcons (id', t, fld') ->
    if ident_eq id id'
    then OK (align pos (alignof t))
    else field_offset_rec id fld' (Z.add (align pos (alignof t)) (sizeof t))

(** val field_offset : ident -> fieldlist -> coq_Z res **)

let field_offset id fld =
  field_offset_rec id fld Z0

(** val field_type : ident -> fieldlist -> coq_type res **)

let rec field_type id = function
| Fnil ->
  Error ((MSG
    ('U'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('f'::('i'::('e'::('l'::('d'::(' '::[]))))))))))))))) :: ((CTX
    id) :: []))
| Fcons (id', t, fld') ->
  if ident_eq id id' then OK t else field_type id fld'

type mode =
| By_value of memory_chunk
| By_reference
| By_copy
| By_nothing

(** val access_mode : coq_type -> mode **)

let access_mode = function
| Tint (i, s, a) ->
  (match i with
   | I8 ->
     (match s with
      | Signed -> By_value Mint8signed
      | Unsigned -> By_value Mint8unsigned)
   | I16 ->
     (match s with
      | Signed -> By_value Mint16signed
      | Unsigned -> By_value Mint16unsigned)
   | I32 -> By_value Mint32
   | IBool -> By_value Mint8unsigned)
| Tlong (s, a) -> By_value Mint64
| Tfloat (f, a) ->
  (match f with
   | F32 -> By_value Mfloat32
   | F64 -> By_value Mfloat64)
| Tpointer (t, a) -> By_value Mint32
| Tarray (t, z, a) -> By_reference
| Tfunction (t, t0, c) -> By_reference
| Tstruct (i, f, a) -> By_copy
| Tunion (i, f, a) -> By_copy
| _ -> By_nothing

(** val type_is_volatile : coq_type -> bool **)

let type_is_volatile ty =
  match access_mode ty with
  | By_value m -> (attr_of_type ty).attr_volatile
  | _ -> false

(** val alignof_blockcopy : coq_type -> coq_Z **)

let rec alignof_blockcopy t = match t with
| Tint (i, s, a) ->
  (match i with
   | I16 -> Zpos (Coq_xO Coq_xH)
   | I32 -> Zpos (Coq_xO (Coq_xO Coq_xH))
   | _ -> Zpos Coq_xH)
| Tlong (s, a) -> Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
| Tfloat (f, a) ->
  (match f with
   | F32 -> Zpos (Coq_xO (Coq_xO Coq_xH))
   | F64 -> Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
| Tpointer (t0, a) -> Zpos (Coq_xO (Coq_xO Coq_xH))
| Tarray (t', z, a) -> alignof_blockcopy t'
| Tstruct (i, fld, a) ->
  Z.min (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) (alignof t)
| Tunion (i, fld, a) ->
  Z.min (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) (alignof t)
| Tcomp_ptr (i, a) -> Zpos (Coq_xO (Coq_xO Coq_xH))
| _ -> Zpos Coq_xH

(** val type_of_params : (ident * coq_type) list -> typelist **)

let rec type_of_params = function
| [] -> Tnil
| p :: rem -> let (id, ty) = p in Tcons (ty, (type_of_params rem))

(** val typ_of_type : coq_type -> typ **)

let typ_of_type = function
| Tlong (s, a) -> AST.Tlong
| Tfloat (f, a) ->
  (match f with
   | F32 -> Tsingle
   | F64 -> AST.Tfloat)
| _ -> AST.Tint

(** val opttyp_of_type : coq_type -> typ option **)

let opttyp_of_type = function
| Tvoid -> None
| Tlong (s, a) -> Some AST.Tlong
| Tfloat (f, a) ->
  (match f with
   | F32 -> Some Tsingle
   | F64 -> Some AST.Tfloat)
| _ -> Some AST.Tint

(** val typlist_of_typelist : typelist -> typ list **)

let rec typlist_of_typelist = function
| Tnil -> []
| Tcons (hd, tl0) -> (typ_of_type hd) :: (typlist_of_typelist tl0)

(** val signature_of_type :
    typelist -> coq_type -> calling_convention -> signature **)

let signature_of_type args res0 cc =
  { sig_args = (typlist_of_typelist args); sig_res = (opttyp_of_type res0);
    sig_cc = cc }

