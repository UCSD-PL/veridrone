open AST
open BinInt
open BinNums
open Cop
open Coqlib
open Csyntax
open Ctypes
open Datatypes
open Errors
open Integers
open Memory
open Values

(** val do_cast : coq_val -> coq_type -> coq_type -> coq_val res **)

let do_cast v t1 t2 =
  match sem_cast v t1 t2 with
  | Some v' -> OK v'
  | None ->
    Error
      (msg
        ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('c'::('a'::('s'::('t'::[])))))))))))))))

(** val constval : expr -> coq_val res **)

let rec constval = function
| Eval (v, ty) ->
  (match v with
   | Vundef ->
     Error
       (msg
         ('i'::('l'::('l'::('e'::('g'::('a'::('l'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::[])))))))))))))))))
   | Vptr (b, i) ->
     Error
       (msg
         ('i'::('l'::('l'::('e'::('g'::('a'::('l'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::[])))))))))))))))))
   | _ -> OK v)
| Evar (x, ty) -> OK (Vptr (x, Int.zero))
| Efield (l, f, ty) ->
  (match typeof l with
   | Tstruct (id, fList, a0) ->
     (match field_offset f fList with
      | OK x ->
        (match constval l with
         | OK x0 -> OK (Val.add x0 (Vint (Int.repr x)))
         | Error msg0 -> Error msg0)
      | Error msg0 -> Error msg0)
   | Tunion (id, fList, a0) -> constval l
   | _ ->
     Error
       (msg
         ('i'::('l'::('l'::('-'::('t'::('y'::('p'::('e'::('d'::(' '::('f'::('i'::('e'::('l'::('d'::(' '::('a'::('c'::('c'::('e'::('s'::('s'::[]))))))))))))))))))))))))
| Evalof (l, ty) ->
  (match access_mode ty with
   | By_value m ->
     Error
       (msg
         ('d'::('e'::('r'::('e'::('f'::('e'::('r'::('e'::('n'::('c'::('i'::('n'::('g'::(' '::('o'::('f'::(' '::('a'::('n'::(' '::('l'::('-'::('v'::('a'::('l'::('u'::('e'::[]))))))))))))))))))))))))))))
   | By_nothing ->
     Error
       (msg
         ('d'::('e'::('r'::('e'::('f'::('e'::('r'::('e'::('n'::('c'::('i'::('n'::('g'::(' '::('o'::('f'::(' '::('a'::('n'::(' '::('l'::('-'::('v'::('a'::('l'::('u'::('e'::[]))))))))))))))))))))))))))))
   | _ -> constval l)
| Ederef (r, ty) -> constval r
| Eaddrof (l, ty) -> constval l
| Eunop (op, r1, ty) ->
  (match constval r1 with
   | OK x ->
     (match sem_unary_operation op x (typeof r1) with
      | Some v -> OK v
      | None ->
        Error
          (msg
            ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('u'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))
   | Error msg0 -> Error msg0)
| Ebinop (op, r1, r2, ty) ->
  (match constval r1 with
   | OK x ->
     (match constval r2 with
      | OK x0 ->
        (match sem_binary_operation op x (typeof r1) x0 (typeof r2) Mem.empty with
         | Some v -> OK v
         | None ->
           Error
             (msg
               ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Ecast (r, ty) ->
  (match constval r with
   | OK x -> do_cast x (typeof r) ty
   | Error msg0 -> Error msg0)
| Eseqand (r1, r2, ty) ->
  (match constval r1 with
   | OK x ->
     (match constval r2 with
      | OK x0 ->
        (match bool_val x (typeof r1) with
         | Some b ->
           if b
           then (match do_cast x0 (typeof r2) type_bool with
                 | OK x1 -> do_cast x1 type_bool ty
                 | Error msg0 -> Error msg0)
           else OK (Vint Int.zero)
         | None ->
           Error
             (msg
               ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('&'::('&'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Eseqor (r1, r2, ty) ->
  (match constval r1 with
   | OK x ->
     (match constval r2 with
      | OK x0 ->
        (match bool_val x (typeof r1) with
         | Some b ->
           if b
           then OK (Vint Int.one)
           else (match do_cast x0 (typeof r2) type_bool with
                 | OK x1 -> do_cast x1 type_bool ty
                 | Error msg0 -> Error msg0)
         | None ->
           Error
             (msg
               ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('|'::('|'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Econdition (r1, r2, r3, ty) ->
  (match constval r1 with
   | OK x ->
     (match constval r2 with
      | OK x0 ->
        (match constval r3 with
         | OK x1 ->
           (match bool_val x (typeof r1) with
            | Some b ->
              if b
              then do_cast x0 (typeof r2) ty
              else do_cast x1 (typeof r3) ty
            | None ->
              Error
                (msg
                  ('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::[]))))))))))))))))))))))))
         | Error msg0 -> Error msg0)
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Esizeof (ty1, ty) -> OK (Vint (Int.repr (sizeof ty1)))
| Ealignof (ty1, ty) -> OK (Vint (Int.repr (alignof ty1)))
| Ecomma (r1, r2, ty) ->
  (match constval r1 with
   | OK x -> constval r2
   | Error msg0 -> Error msg0)
| Eparen (r, ty) ->
  (match constval r with
   | OK x -> do_cast x (typeof r) ty
   | Error msg0 -> Error msg0)
| _ ->
  Error
    (msg
      ('n'::('o'::('t'::(' '::('a'::(' '::('c'::('o'::('m'::('p'::('i'::('l'::('e'::('-'::('t'::('i'::('m'::('e'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::[]))))))))))))))))))))))))))))

type coq_initializer =
| Init_single of expr
| Init_array of initializer_list
| Init_struct of initializer_list
| Init_union of ident * coq_initializer
and initializer_list =
| Init_nil
| Init_cons of coq_initializer * initializer_list

(** val transl_init_single : coq_type -> expr -> init_data res **)

let transl_init_single ty a =
  match constval a with
  | OK x ->
    (match do_cast x (typeof a) ty with
     | OK x0 ->
       (match x0 with
        | Vundef ->
          Error
            (msg
              ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))))))))
        | Vint n ->
          (match ty with
           | Tint (i, sg, a0) ->
             (match i with
              | I16 -> OK (Init_int16 n)
              | I32 -> OK (Init_int32 n)
              | _ -> OK (Init_int8 n))
           | Tpointer (t, a0) -> OK (Init_int32 n)
           | Tcomp_ptr (i, a0) -> OK (Init_int32 n)
           | _ ->
             Error
               (msg
                 ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))
        | Vlong n ->
          (match ty with
           | Tlong (s, a0) -> OK (Init_int64 n)
           | _ ->
             Error
               (msg
                 ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))
        | Vfloat f ->
          (match ty with
           | Tfloat (f0, a0) ->
             (match f0 with
              | F32 ->
                Error
                  (msg
                    ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))
              | F64 -> OK (Init_float64 f))
           | _ ->
             Error
               (msg
                 ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))
        | Vsingle f ->
          (match ty with
           | Tfloat (f0, a0) ->
             (match f0 with
              | F32 -> OK (Init_float32 f)
              | F64 ->
                Error
                  (msg
                    ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))
           | _ ->
             Error
               (msg
                 ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))
        | Vptr (id, ofs) ->
          (match ty with
           | Tint (i, sg, a0) ->
             (match i with
              | I32 -> OK (Init_addrof (id, ofs))
              | _ ->
                Error
                  (msg
                    ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))
           | Tpointer (t, a0) -> OK (Init_addrof (id, ofs))
           | Tcomp_ptr (i, a0) -> OK (Init_addrof (id, ofs))
           | _ ->
             Error
               (msg
                 ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))))
     | Error msg0 -> Error msg0)
  | Error msg0 -> Error msg0

(** val padding : coq_Z -> coq_Z -> init_data list **)

let padding frm to0 =
  if zlt frm to0 then (Init_space (Z.sub to0 frm)) :: [] else []

(** val transl_init : coq_type -> coq_initializer -> init_data list res **)

let rec transl_init ty = function
| Init_single a ->
  (match transl_init_single ty a with
   | OK x -> OK (x :: [])
   | Error msg0 -> Error msg0)
| Init_array il ->
  (match ty with
   | Tarray (tyelt, nelt, a) -> transl_init_array tyelt il (Z.max Z0 nelt)
   | _ ->
     Error
       (msg
         ('w'::('r'::('o'::('n'::('g'::(' '::('t'::('y'::('p'::('e'::(' '::('f'::('o'::('r'::(' '::('c'::('o'::('m'::('p'::('o'::('u'::('n'::('d'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))))))))))
| Init_struct il ->
  (match ty with
   | Tstruct (id, fl, a) -> transl_init_struct id ty fl il Z0
   | _ ->
     Error
       (msg
         ('w'::('r'::('o'::('n'::('g'::(' '::('t'::('y'::('p'::('e'::(' '::('f'::('o'::('r'::(' '::('c'::('o'::('m'::('p'::('o'::('u'::('n'::('d'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))))))))))
| Init_union (f, i1) ->
  (match ty with
   | Tunion (id, fl, a) ->
     (match field_type f fl with
      | OK x ->
        (match transl_init x i1 with
         | OK x0 -> OK (app x0 (padding (sizeof x) (sizeof ty)))
         | Error msg0 -> Error msg0)
      | Error msg0 -> Error msg0)
   | _ ->
     Error
       (msg
         ('w'::('r'::('o'::('n'::('g'::(' '::('t'::('y'::('p'::('e'::(' '::('f'::('o'::('r'::(' '::('c'::('o'::('m'::('p'::('o'::('u'::('n'::('d'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))))))))))

(** val transl_init_array :
    coq_type -> initializer_list -> coq_Z -> init_data list res **)

and transl_init_array ty il sz =
  match il with
  | Init_nil ->
    if zeq sz Z0
    then OK []
    else if zle Z0 sz
         then OK ((Init_space (Z.mul sz (sizeof ty))) :: [])
         else Error
                (msg
                  ('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('e'::('l'::('e'::('m'::('e'::('n'::('t'::('s'::(' '::('i'::('n'::(' '::('a'::('r'::('r'::('a'::('y'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))))))))
  | Init_cons (i1, il') ->
    (match transl_init ty i1 with
     | OK x ->
       (match transl_init_array ty il' (Z.sub sz (Zpos Coq_xH)) with
        | OK x0 -> OK (app x x0)
        | Error msg0 -> Error msg0)
     | Error msg0 -> Error msg0)

(** val transl_init_struct :
    ident -> coq_type -> fieldlist -> initializer_list -> coq_Z -> init_data
    list res **)

and transl_init_struct id ty fl il pos =
  match il with
  | Init_nil ->
    (match fl with
     | Fnil -> OK (padding pos (sizeof ty))
     | Fcons (i, t, f) ->
       Error
         (msg
           ('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('e'::('l'::('e'::('m'::('e'::('n'::('t'::('s'::(' '::('i'::('n'::(' '::('s'::('t'::('r'::('u'::('c'::('t'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))))))))))
  | Init_cons (i1, il') ->
    (match fl with
     | Fnil ->
       Error
         (msg
           ('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('e'::('l'::('e'::('m'::('e'::('n'::('t'::('s'::(' '::('i'::('n'::(' '::('s'::('t'::('r'::('u'::('c'::('t'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))))))))))))))))))))
     | Fcons (i, ty1, fl') ->
       let pos1 = align pos (alignof ty1) in
       (match transl_init ty1 i1 with
        | OK x ->
          (match transl_init_struct id ty fl' il' (Z.add pos1 (sizeof ty1)) with
           | OK x0 -> OK (app (padding pos pos1) (app x x0))
           | Error msg0 -> Error msg0)
        | Error msg0 -> Error msg0))

