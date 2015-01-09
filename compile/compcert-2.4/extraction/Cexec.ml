open AST
open BinInt
open BinNums
open Cop
open Coqlib
open Csem
open Csyntax
open Ctypes
open Datatypes
open Determinism
open Errors
open Events
open Globalenvs
open Integers
open List0
open Maps
open Memory
open Values

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val is_val : expr -> (coq_val * coq_type) option **)

let is_val = function
| Eval (v, ty) -> Some (v, ty)
| _ -> None

(** val is_loc : expr -> ((block * Int.int) * coq_type) option **)

let is_loc = function
| Eloc (b, ofs, ty) -> Some ((b, ofs), ty)
| _ -> None

(** val is_val_list : exprlist -> (coq_val * coq_type) list option **)

let rec is_val_list = function
| Enil -> Some []
| Econs (a1, al0) ->
  (match is_val a1 with
   | Some vt1 ->
     (match is_val_list al0 with
      | Some vtl -> Some (vt1 :: vtl)
      | None -> None)
   | None -> None)

(** val is_skip : statement -> bool **)

let is_skip = function
| Sskip -> true
| _ -> false

(** val eventval_of_val : genv -> coq_val -> typ -> eventval option **)

let eventval_of_val ge v t =
  match v with
  | Vundef -> None
  | Vint i ->
    (match t with
     | AST.Tint -> Some (EVint i)
     | _ -> None)
  | Vlong n ->
    (match t with
     | AST.Tlong -> Some (EVlong n)
     | _ -> None)
  | Vfloat f ->
    (match t with
     | AST.Tfloat -> Some (EVfloat f)
     | _ -> None)
  | Vsingle f ->
    (match t with
     | Tsingle -> Some (EVsingle f)
     | _ -> None)
  | Vptr (b, ofs) ->
    (match t with
     | AST.Tint ->
       (match Genv.invert_symbol ge b with
        | Some id -> Some (EVptr_global (id, ofs))
        | None -> None)
     | _ -> None)

(** val list_eventval_of_val :
    genv -> coq_val list -> typ list -> eventval list option **)

let rec list_eventval_of_val ge vl tl =
  match vl with
  | [] ->
    (match tl with
     | [] -> Some []
     | t :: l -> None)
  | v1 :: vl0 ->
    (match tl with
     | [] -> None
     | t1 :: tl0 ->
       (match eventval_of_val ge v1 t1 with
        | Some ev1 ->
          (match list_eventval_of_val ge vl0 tl0 with
           | Some evl -> Some (ev1 :: evl)
           | None -> None)
        | None -> None))

(** val val_of_eventval : genv -> eventval -> typ -> coq_val option **)

let val_of_eventval ge ev t =
  match ev with
  | EVint i ->
    (match t with
     | AST.Tint -> Some (Vint i)
     | _ -> None)
  | EVlong n ->
    (match t with
     | AST.Tlong -> Some (Vlong n)
     | _ -> None)
  | EVfloat f ->
    (match t with
     | AST.Tfloat -> Some (Vfloat f)
     | _ -> None)
  | EVsingle f ->
    (match t with
     | Tsingle -> Some (Vsingle f)
     | _ -> None)
  | EVptr_global (id, ofs) ->
    (match t with
     | AST.Tint ->
       (match Genv.find_symbol ge id with
        | Some b -> Some (Vptr (b, ofs))
        | None -> None)
     | _ -> None)

(** val do_volatile_load :
    genv -> world -> memory_chunk -> Mem.mem -> block -> Int.int ->
    ((world * trace) * coq_val) option **)

let do_volatile_load ge w chunk m b ofs =
  if block_is_volatile ge b
  then (match Genv.invert_symbol ge b with
        | Some id ->
          (match nextworld_vload w chunk id ofs with
           | Some p ->
             let (res, w') = p in
             (match val_of_eventval ge res (type_of_chunk chunk) with
              | Some vres ->
                Some ((w', ((Event_vload (chunk, id, ofs, res)) :: [])),
                  (Val.load_result chunk vres))
              | None -> None)
           | None -> None)
        | None -> None)
  else (match Mem.load chunk m b (Int.unsigned ofs) with
        | Some v -> Some ((w, coq_E0), v)
        | None -> None)

(** val do_volatile_store :
    genv -> world -> memory_chunk -> Mem.mem -> block -> Int.int -> coq_val
    -> ((world * trace) * Mem.mem) option **)

let do_volatile_store ge w chunk m b ofs v =
  if block_is_volatile ge b
  then (match Genv.invert_symbol ge b with
        | Some id ->
          (match eventval_of_val ge (Val.load_result chunk v)
                   (type_of_chunk chunk) with
           | Some ev ->
             (match nextworld_vstore w chunk id ofs ev with
              | Some w' ->
                Some ((w', ((Event_vstore (chunk, id, ofs, ev)) :: [])), m)
              | None -> None)
           | None -> None)
        | None -> None)
  else (match Mem.store chunk m b (Int.unsigned ofs) v with
        | Some m' -> Some ((w, coq_E0), m')
        | None -> None)

(** val do_deref_loc :
    genv -> world -> coq_type -> Mem.mem -> block -> Int.int ->
    ((world * trace) * coq_val) option **)

let do_deref_loc ge w ty m b ofs =
  match access_mode ty with
  | By_value chunk ->
    if type_is_volatile ty
    then do_volatile_load ge w chunk m b ofs
    else (match Mem.loadv chunk m (Vptr (b, ofs)) with
          | Some v -> Some ((w, coq_E0), v)
          | None -> None)
  | By_nothing -> None
  | _ -> Some ((w, coq_E0), (Vptr (b, ofs)))

(** val check_assign_copy :
    coq_type -> block -> Int.int -> block -> Int.int -> bool **)

let check_assign_copy ty b ofs b' ofs' =
  let s = fun _ -> coq_Zdivide_dec (alignof_blockcopy ty) (Int.unsigned ofs')
  in
  if s __
  then let s0 = fun _ ->
         coq_Zdivide_dec (alignof_blockcopy ty) (Int.unsigned ofs)
       in
       if s0 __
       then let s1 = eq_block b' b in
            if s1
            then let s2 = zeq (Int.unsigned ofs') (Int.unsigned ofs) in
                 if s2
                 then true
                 else let s3 =
                        zle (Z.add (Int.unsigned ofs') (sizeof ty))
                          (Int.unsigned ofs)
                      in
                      if s3
                      then true
                      else zle (Z.add (Int.unsigned ofs) (sizeof ty))
                             (Int.unsigned ofs')
            else true
       else false
  else false

(** val do_assign_loc :
    genv -> world -> coq_type -> Mem.mem -> block -> Int.int -> coq_val ->
    ((world * trace) * Mem.mem) option **)

let do_assign_loc ge w ty m b ofs v =
  match access_mode ty with
  | By_value chunk ->
    if type_is_volatile ty
    then do_volatile_store ge w chunk m b ofs v
    else (match Mem.storev chunk m (Vptr (b, ofs)) v with
          | Some m' -> Some ((w, coq_E0), m')
          | None -> None)
  | By_copy ->
    (match v with
     | Vptr (b', ofs') ->
       if check_assign_copy ty b ofs b' ofs'
       then (match Mem.loadbytes m b' (Int.unsigned ofs') (sizeof ty) with
             | Some bytes ->
               (match Mem.storebytes m b (Int.unsigned ofs) bytes with
                | Some m' -> Some ((w, coq_E0), m')
                | None -> None)
             | None -> None)
       else None
     | _ -> None)
  | _ -> None

(** val do_ef_volatile_load :
    genv -> memory_chunk -> world -> coq_val list -> Mem.mem ->
    (((world * trace) * coq_val) * Mem.mem) option **)

let do_ef_volatile_load ge chunk w vargs m =
  match vargs with
  | [] -> None
  | v :: l ->
    (match v with
     | Vptr (b, ofs) ->
       (match l with
        | [] ->
          (match do_volatile_load ge w chunk m b ofs with
           | Some p -> Some (p, m)
           | None -> None)
        | v0 :: l0 -> None)
     | _ -> None)

(** val do_ef_volatile_store :
    genv -> memory_chunk -> world -> coq_val list -> Mem.mem ->
    (((world * trace) * coq_val) * Mem.mem) option **)

let do_ef_volatile_store ge chunk w vargs m =
  match vargs with
  | [] -> None
  | v0 :: l ->
    (match v0 with
     | Vptr (b, ofs) ->
       (match l with
        | [] -> None
        | v :: l0 ->
          (match l0 with
           | [] ->
             (match do_volatile_store ge w chunk m b ofs v with
              | Some p -> let (p0, m') = p in Some ((p0, Vundef), m')
              | None -> None)
           | v1 :: l1 -> None))
     | _ -> None)

(** val do_ef_volatile_load_global :
    genv -> memory_chunk -> ident -> Int.int -> world -> coq_val list ->
    Mem.mem -> (((world * trace) * coq_val) * Mem.mem) option **)

let do_ef_volatile_load_global ge chunk id ofs w vargs m =
  match Genv.find_symbol ge id with
  | Some b -> do_ef_volatile_load ge chunk w ((Vptr (b, ofs)) :: vargs) m
  | None -> None

(** val do_ef_volatile_store_global :
    genv -> memory_chunk -> ident -> Int.int -> world -> coq_val list ->
    Mem.mem -> (((world * trace) * coq_val) * Mem.mem) option **)

let do_ef_volatile_store_global ge chunk id ofs w vargs m =
  match Genv.find_symbol ge id with
  | Some b -> do_ef_volatile_store ge chunk w ((Vptr (b, ofs)) :: vargs) m
  | None -> None

(** val do_ef_malloc :
    world -> coq_val list -> Mem.mem ->
    (((world * trace) * coq_val) * Mem.mem) option **)

let do_ef_malloc w vargs m =
  match vargs with
  | [] -> None
  | v :: l ->
    (match v with
     | Vint n ->
       (match l with
        | [] ->
          let (m', b) =
            Mem.alloc m (Zneg (Coq_xO (Coq_xO Coq_xH))) (Int.unsigned n)
          in
          (match Mem.store Mint32 m' b (Zneg (Coq_xO (Coq_xO Coq_xH))) (Vint
                   n) with
           | Some m'' -> Some (((w, coq_E0), (Vptr (b, Int.zero))), m'')
           | None -> None)
        | v0 :: l0 -> None)
     | _ -> None)

(** val do_ef_free :
    world -> coq_val list -> Mem.mem ->
    (((world * trace) * coq_val) * Mem.mem) option **)

let do_ef_free w vargs m =
  match vargs with
  | [] -> None
  | v :: l ->
    (match v with
     | Vptr (b, lo) ->
       (match l with
        | [] ->
          (match Mem.load Mint32 m b
                   (Z.sub (Int.unsigned lo) (Zpos (Coq_xO (Coq_xO Coq_xH)))) with
           | Some vsz ->
             (match vsz with
              | Vint sz ->
                if zlt Z0 (Int.unsigned sz)
                then (match Mem.free m b
                              (Z.sub (Int.unsigned lo) (Zpos (Coq_xO (Coq_xO
                                Coq_xH))))
                              (Z.add (Int.unsigned lo) (Int.unsigned sz)) with
                      | Some m' -> Some (((w, coq_E0), Vundef), m')
                      | None -> None)
                else None
              | _ -> None)
           | None -> None)
        | v0 :: l0 -> None)
     | _ -> None)

(** val memcpy_check_args :
    coq_Z -> coq_Z -> block -> coq_Z -> block -> coq_Z -> bool **)

let memcpy_check_args sz al bdst odst bsrc osrc =
  let x =
    let s = zeq al (Zpos Coq_xH) in
    if s
    then true
    else let s0 = zeq al (Zpos (Coq_xO Coq_xH)) in
         if s0
         then true
         else let s1 = zeq al (Zpos (Coq_xO (Coq_xO Coq_xH))) in
              if s1
              then true
              else zeq al (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
  in
  if x
  then let s = zle Z0 sz in
       if s
       then let s0 = fun _ -> coq_Zdivide_dec al sz in
            if s0 __
            then let u = fun x0 ->
                   let s1 = zeq sz Z0 in
                   if s1 then true else coq_Zdivide_dec al x0
                 in
                 let s1 = u osrc in
                 if s1
                 then let s2 = u odst in
                      if s2
                      then let s3 = eq_block bsrc bdst in
                           if s3
                           then let s4 = zeq osrc odst in
                                if s4
                                then true
                                else let s5 = zle (Z.add osrc sz) odst in
                                     if s5
                                     then true
                                     else zle (Z.add odst sz) osrc
                           else true
                      else false
                 else false
            else false
       else false
  else false

(** val do_ef_memcpy :
    coq_Z -> coq_Z -> world -> coq_val list -> Mem.mem ->
    (((world * trace) * coq_val) * Mem.mem) option **)

let do_ef_memcpy sz al w vargs m =
  match vargs with
  | [] -> None
  | v :: l ->
    (match v with
     | Vptr (bdst, odst) ->
       (match l with
        | [] -> None
        | v0 :: l0 ->
          (match v0 with
           | Vptr (bsrc, osrc) ->
             (match l0 with
              | [] ->
                if memcpy_check_args sz al bdst (Int.unsigned odst) bsrc
                     (Int.unsigned osrc)
                then (match Mem.loadbytes m bsrc (Int.unsigned osrc) sz with
                      | Some bytes ->
                        (match Mem.storebytes m bdst (Int.unsigned odst)
                                 bytes with
                         | Some m' -> Some (((w, coq_E0), Vundef), m')
                         | None -> None)
                      | None -> None)
                else None
              | v1 :: l1 -> None)
           | _ -> None))
     | _ -> None)

(** val do_ef_annot :
    genv -> ident -> annot_arg list -> world -> coq_val list -> Mem.mem ->
    (((world * trace) * coq_val) * Mem.mem) option **)

let do_ef_annot ge text targs w vargs m =
  match list_eventval_of_val ge vargs (annot_args_typ targs) with
  | Some args ->
    Some (((w, ((Event_annot (text,
      (annot_eventvals targs args))) :: coq_E0)), Vundef), m)
  | None -> None

(** val do_ef_annot_val :
    genv -> ident -> typ -> world -> coq_val list -> Mem.mem ->
    (((world * trace) * coq_val) * Mem.mem) option **)

let do_ef_annot_val ge text targ w vargs m =
  match vargs with
  | [] -> None
  | varg :: l ->
    (match l with
     | [] ->
       (match eventval_of_val ge varg targ with
        | Some arg ->
          Some (((w, ((Event_annot (text, (arg :: []))) :: coq_E0)), varg),
            m)
        | None -> None)
     | v :: l0 -> None)

(** val do_external :
    genv -> (ident -> signature -> genv -> world -> coq_val list -> Mem.mem
    -> (((world * trace) * coq_val) * Mem.mem) option) -> (ident -> genv ->
    world -> coq_val list -> Mem.mem ->
    (((world * trace) * coq_val) * Mem.mem) option) -> external_function ->
    world -> coq_val list -> Mem.mem ->
    (((world * trace) * coq_val) * Mem.mem) option **)

let do_external ge do_external_function do_inline_assembly = function
| EF_external (name, sg) -> do_external_function name sg ge
| EF_builtin (name, sg) -> do_external_function name sg ge
| EF_vload chunk -> do_ef_volatile_load ge chunk
| EF_vstore chunk -> do_ef_volatile_store ge chunk
| EF_vload_global (chunk, id, ofs) ->
  do_ef_volatile_load_global ge chunk id ofs
| EF_vstore_global (chunk, id, ofs) ->
  do_ef_volatile_store_global ge chunk id ofs
| EF_malloc -> do_ef_malloc
| EF_free -> do_ef_free
| EF_memcpy (sz, al) -> do_ef_memcpy sz al
| EF_annot (text, targs) -> do_ef_annot ge text targs
| EF_annot_val (text, targ) -> do_ef_annot_val ge text targ
| EF_inline_asm text -> do_inline_assembly text ge

type reduction =
| Lred of expr * Mem.mem
| Rred of expr * Mem.mem * trace
| Callred of fundef * coq_val list * coq_type * Mem.mem
| Stuckred

(** val sem_cast_arguments :
    (coq_val * coq_type) list -> typelist -> coq_val list option **)

let rec sem_cast_arguments vtl tl =
  match vtl with
  | [] ->
    (match tl with
     | Tnil -> Some []
     | Tcons (t, t0) -> None)
  | p :: vtl0 ->
    let (v1, t1) = p in
    (match tl with
     | Tnil -> None
     | Tcons (t1', tl0) ->
       (match sem_cast v1 t1 t1' with
        | Some v ->
          (match sem_cast_arguments vtl0 tl0 with
           | Some vl -> Some (v :: vl)
           | None -> None)
        | None -> None))

type 'a reducts = ((expr -> 'a) * reduction) list

(** val topred : reduction -> expr reducts **)

let topred r =
  ((fun x -> x), r) :: []

(** val stuck : expr reducts **)

let stuck =
  ((fun x -> x), Stuckred) :: []

(** val incontext : ('a1 -> 'a2) -> 'a1 reducts -> 'a2 reducts **)

let incontext ctx ll =
  map (fun z -> ((fun x -> ctx (fst z x)), (snd z))) ll

(** val incontext2 :
    ('a1 -> 'a3) -> 'a1 reducts -> ('a2 -> 'a3) -> 'a2 reducts -> 'a3 reducts **)

let incontext2 ctx1 ll1 ctx2 ll2 =
  app (incontext ctx1 ll1) (incontext ctx2 ll2)

(** val step_expr :
    genv -> (ident -> signature -> genv -> world -> coq_val list -> Mem.mem
    -> (((world * trace) * coq_val) * Mem.mem) option) -> (ident -> genv ->
    world -> coq_val list -> Mem.mem ->
    (((world * trace) * coq_val) * Mem.mem) option) -> env -> world -> kind
    -> expr -> Mem.mem -> expr reducts **)

let step_expr ge do_external_function do_inline_assembly e w =
  let rec step_expr0 k a m =
    match k with
    | LV ->
      (match a with
       | Evar (x, ty) ->
         (match PTree.get x e with
          | Some p ->
            let (b, ty') = p in
            if type_eq ty ty'
            then topred (Lred ((Eloc (b, Int.zero, ty)), m))
            else stuck
          | None ->
            (match Genv.find_symbol ge x with
             | Some b -> topred (Lred ((Eloc (b, Int.zero, ty)), m))
             | None -> stuck))
       | Efield (r, f, ty) ->
         (match is_val r with
          | Some p ->
            let (v, ty') = p in
            (match v with
             | Vptr (b, ofs) ->
               (match ty' with
                | Tstruct (id, fList, a0) ->
                  (match field_offset f fList with
                   | OK delta ->
                     topred (Lred ((Eloc (b, (Int.add ofs (Int.repr delta)),
                       ty)), m))
                   | Error e0 -> stuck)
                | Tunion (id, fList, a0) ->
                  topred (Lred ((Eloc (b, ofs, ty)), m))
                | _ -> stuck)
             | _ -> stuck)
          | None ->
            incontext (fun x -> Efield (x, f, ty)) (step_expr0 RV r m))
       | Ederef (r, ty) ->
         (match is_val r with
          | Some p ->
            let (v, ty') = p in
            (match v with
             | Vptr (b, ofs) -> topred (Lred ((Eloc (b, ofs, ty)), m))
             | _ -> stuck)
          | None -> incontext (fun x -> Ederef (x, ty)) (step_expr0 RV r m))
       | Eloc (b, ofs, ty) -> []
       | _ -> stuck)
    | RV ->
      (match a with
       | Eval (v, ty) -> []
       | Evalof (l, ty) ->
         (match is_loc l with
          | Some p ->
            let (p0, ty') = p in
            let (b, ofs) = p0 in
            if type_eq ty ty'
            then (match do_deref_loc ge w ty m b ofs with
                  | Some p1 ->
                    let (p2, v) = p1 in
                    let (w', t) = p2 in topred (Rred ((Eval (v, ty)), m, t))
                  | None -> stuck)
            else stuck
          | None -> incontext (fun x -> Evalof (x, ty)) (step_expr0 LV l m))
       | Eaddrof (l, ty) ->
         (match is_loc l with
          | Some p ->
            let (p0, ty') = p in
            let (b, ofs) = p0 in
            topred (Rred ((Eval ((Vptr (b, ofs)), ty)), m, coq_E0))
          | None -> incontext (fun x -> Eaddrof (x, ty)) (step_expr0 LV l m))
       | Eunop (op, r1, ty) ->
         (match is_val r1 with
          | Some p ->
            let (v1, ty1) = p in
            (match sem_unary_operation op v1 ty1 with
             | Some v -> topred (Rred ((Eval (v, ty)), m, coq_E0))
             | None -> stuck)
          | None ->
            incontext (fun x -> Eunop (op, x, ty)) (step_expr0 RV r1 m))
       | Ebinop (op, r1, r2, ty) ->
         (match is_val r1 with
          | Some p ->
            let (v1, ty1) = p in
            (match is_val r2 with
             | Some p0 ->
               let (v2, ty2) = p0 in
               (match sem_binary_operation op v1 ty1 v2 ty2 m with
                | Some v -> topred (Rred ((Eval (v, ty)), m, coq_E0))
                | None -> stuck)
             | None ->
               incontext2 (fun x -> Ebinop (op, x, r2, ty))
                 (step_expr0 RV r1 m) (fun x -> Ebinop (op, r1, x, ty))
                 (step_expr0 RV r2 m))
          | None ->
            incontext2 (fun x -> Ebinop (op, x, r2, ty)) (step_expr0 RV r1 m)
              (fun x -> Ebinop (op, r1, x, ty)) (step_expr0 RV r2 m))
       | Ecast (r1, ty) ->
         (match is_val r1 with
          | Some p ->
            let (v1, ty1) = p in
            (match sem_cast v1 ty1 ty with
             | Some v -> topred (Rred ((Eval (v, ty)), m, coq_E0))
             | None -> stuck)
          | None -> incontext (fun x -> Ecast (x, ty)) (step_expr0 RV r1 m))
       | Eseqand (r1, r2, ty) ->
         (match is_val r1 with
          | Some p ->
            let (v1, ty1) = p in
            (match bool_val v1 ty1 with
             | Some b ->
               if b
               then topred (Rred ((Eparen ((Eparen (r2, type_bool)), ty)), m,
                      coq_E0))
               else topred (Rred ((Eval ((Vint Int.zero), ty)), m, coq_E0))
             | None -> stuck)
          | None ->
            incontext (fun x -> Eseqand (x, r2, ty)) (step_expr0 RV r1 m))
       | Eseqor (r1, r2, ty) ->
         (match is_val r1 with
          | Some p ->
            let (v1, ty1) = p in
            (match bool_val v1 ty1 with
             | Some b ->
               if b
               then topred (Rred ((Eval ((Vint Int.one), ty)), m, coq_E0))
               else topred (Rred ((Eparen ((Eparen (r2, type_bool)), ty)), m,
                      coq_E0))
             | None -> stuck)
          | None ->
            incontext (fun x -> Eseqor (x, r2, ty)) (step_expr0 RV r1 m))
       | Econdition (r1, r2, r3, ty) ->
         (match is_val r1 with
          | Some p ->
            let (v1, ty1) = p in
            (match bool_val v1 ty1 with
             | Some b ->
               topred (Rred ((Eparen ((if b then r2 else r3), ty)), m,
                 coq_E0))
             | None -> stuck)
          | None ->
            incontext (fun x -> Econdition (x, r2, r3, ty))
              (step_expr0 RV r1 m))
       | Esizeof (ty', ty) ->
         topred (Rred ((Eval ((Vint (Int.repr (sizeof ty'))), ty)), m,
           coq_E0))
       | Ealignof (ty', ty) ->
         topred (Rred ((Eval ((Vint (Int.repr (alignof ty'))), ty)), m,
           coq_E0))
       | Eassign (l1, r2, ty) ->
         (match is_loc l1 with
          | Some p ->
            let (p0, ty1) = p in
            let (b, ofs) = p0 in
            (match is_val r2 with
             | Some p1 ->
               let (v2, ty2) = p1 in
               if type_eq ty1 ty
               then (match sem_cast v2 ty2 ty1 with
                     | Some v ->
                       (match do_assign_loc ge w ty1 m b ofs v with
                        | Some p2 ->
                          let (p3, m') = p2 in
                          let (w', t) = p3 in
                          topred (Rred ((Eval (v, ty)), m', t))
                        | None -> stuck)
                     | None -> stuck)
               else stuck
             | None ->
               incontext2 (fun x -> Eassign (x, r2, ty)) (step_expr0 LV l1 m)
                 (fun x -> Eassign (l1, x, ty)) (step_expr0 RV r2 m))
          | None ->
            incontext2 (fun x -> Eassign (x, r2, ty)) (step_expr0 LV l1 m)
              (fun x -> Eassign (l1, x, ty)) (step_expr0 RV r2 m))
       | Eassignop (op, l1, r2, tyres, ty) ->
         (match is_loc l1 with
          | Some p ->
            let (p0, ty1) = p in
            let (b, ofs) = p0 in
            (match is_val r2 with
             | Some p1 ->
               let (v2, ty2) = p1 in
               if type_eq ty1 ty
               then (match do_deref_loc ge w ty1 m b ofs with
                     | Some p2 ->
                       let (p3, v1) = p2 in
                       let (w', t) = p3 in
                       let r' = Eassign ((Eloc (b, ofs, ty1)), (Ebinop (op,
                         (Eval (v1, ty1)), (Eval (v2, ty2)), tyres)), ty1)
                       in
                       topred (Rred (r', m, t))
                     | None -> stuck)
               else stuck
             | None ->
               incontext2 (fun x -> Eassignop (op, x, r2, tyres, ty))
                 (step_expr0 LV l1 m) (fun x -> Eassignop (op, l1, x, tyres,
                 ty)) (step_expr0 RV r2 m))
          | None ->
            incontext2 (fun x -> Eassignop (op, x, r2, tyres, ty))
              (step_expr0 LV l1 m) (fun x -> Eassignop (op, l1, x, tyres,
              ty)) (step_expr0 RV r2 m))
       | Epostincr (id, l, ty) ->
         (match is_loc l with
          | Some p ->
            let (p0, ty1) = p in
            let (b, ofs) = p0 in
            if type_eq ty1 ty
            then (match do_deref_loc ge w ty m b ofs with
                  | Some p1 ->
                    let (p2, v1) = p1 in
                    let (w', t) = p2 in
                    let op =
                      match id with
                      | Incr -> Oadd
                      | Decr -> Osub
                    in
                    let r' = Ecomma ((Eassign ((Eloc (b, ofs, ty)), (Ebinop
                      (op, (Eval (v1, ty)), (Eval ((Vint Int.one),
                      type_int32s)), (incrdecr_type ty))), ty)), (Eval (v1,
                      ty)), ty)
                    in
                    topred (Rred (r', m, t))
                  | None -> stuck)
            else stuck
          | None ->
            incontext (fun x -> Epostincr (id, x, ty)) (step_expr0 LV l m))
       | Ecomma (r1, r2, ty) ->
         (match is_val r1 with
          | Some p ->
            if type_eq (typeof r2) ty
            then topred (Rred (r2, m, coq_E0))
            else stuck
          | None ->
            incontext (fun x -> Ecomma (x, r2, ty)) (step_expr0 RV r1 m))
       | Ecall (r1, rargs, ty) ->
         (match is_val r1 with
          | Some p ->
            let (vf, tyf) = p in
            (match is_val_list rargs with
             | Some vtl ->
               (match classify_fun tyf with
                | Coq_fun_case_f (tyargs, tyres, cconv) ->
                  (match Genv.find_funct ge vf with
                   | Some fd ->
                     (match sem_cast_arguments vtl tyargs with
                      | Some vargs ->
                        if type_eq (type_of_fundef fd) (Tfunction (tyargs,
                             tyres, cconv))
                        then topred (Callred (fd, vargs, ty, m))
                        else stuck
                      | None -> stuck)
                   | None -> stuck)
                | Coq_fun_default -> stuck)
             | None ->
               incontext2 (fun x -> Ecall (x, rargs, ty))
                 (step_expr0 RV r1 m) (fun x -> Ecall (r1, x, ty))
                 (step_exprlist rargs m))
          | None ->
            incontext2 (fun x -> Ecall (x, rargs, ty)) (step_expr0 RV r1 m)
              (fun x -> Ecall (r1, x, ty)) (step_exprlist rargs m))
       | Ebuiltin (ef, tyargs, rargs, ty) ->
         (match is_val_list rargs with
          | Some vtl ->
            (match sem_cast_arguments vtl tyargs with
             | Some vargs ->
               (match do_external ge do_external_function do_inline_assembly
                        ef w vargs m with
                | Some p ->
                  let (p0, m') = p in
                  let (p1, v) = p0 in
                  let (w', t) = p1 in topred (Rred ((Eval (v, ty)), m', t))
                | None -> stuck)
             | None -> stuck)
          | None ->
            incontext (fun x -> Ebuiltin (ef, tyargs, x, ty))
              (step_exprlist rargs m))
       | Eparen (r1, ty) ->
         (match is_val r1 with
          | Some p ->
            let (v1, ty1) = p in
            (match sem_cast v1 ty1 ty with
             | Some v -> topred (Rred ((Eval (v, ty)), m, coq_E0))
             | None -> stuck)
          | None -> incontext (fun x -> Eparen (x, ty)) (step_expr0 RV r1 m))
       | _ -> stuck)
  and step_exprlist rl m =
    match rl with
    | Enil -> []
    | Econs (r1, rs) ->
      incontext2 (fun x -> Econs (x, rs)) (step_expr0 RV r1 m) (fun x ->
        Econs (r1, x)) (step_exprlist rs m)
  in step_expr0

(** val do_alloc_variables :
    env -> Mem.mem -> (ident * coq_type) list -> env * Mem.mem **)

let rec do_alloc_variables e m = function
| [] -> (e, m)
| p :: l' ->
  let (id, ty) = p in
  let (m1, b1) = Mem.alloc m Z0 (sizeof ty) in
  do_alloc_variables (PTree.set id (b1, ty) e) m1 l'

(** val sem_bind_parameters :
    genv -> world -> env -> Mem.mem -> (ident * coq_type) list -> coq_val
    list -> Mem.mem option **)

let rec sem_bind_parameters ge w e m l lv =
  match l with
  | [] ->
    (match lv with
     | [] -> Some m
     | v :: l0 -> None)
  | p :: params ->
    let (id, ty) = p in
    (match lv with
     | [] -> None
     | v1 :: lv0 ->
       (match PTree.get id e with
        | Some p0 ->
          let (b, ty') = p0 in
          if type_eq ty ty'
          then (match do_assign_loc ge w ty m b Int.zero v1 with
                | Some p1 ->
                  let (p2, m1) = p1 in
                  let (w', t) = p2 in
                  (match t with
                   | [] -> sem_bind_parameters ge w e m1 params lv0
                   | e0 :: l0 -> None)
                | None -> None)
          else None
        | None -> None))

(** val expr_final_state :
    coq_function -> cont -> env -> ((expr -> expr) * reduction) ->
    trace * state **)

let expr_final_state f k e c_rd =
  match snd c_rd with
  | Lred (a, m) -> (coq_E0, (ExprState (f, (fst c_rd a), k, e, m)))
  | Rred (a, m, t) -> (t, (ExprState (f, (fst c_rd a), k, e, m)))
  | Callred (fd, vargs, ty, m) ->
    (coq_E0, (Callstate (fd, vargs, (Kcall (f, e, (fst c_rd), ty, k)), m)))
  | Stuckred -> (coq_E0, Stuckstate)

(** val ret : state -> (trace * state) list **)

let ret s =
  (coq_E0, s) :: []

(** val do_step :
    genv -> (ident -> signature -> genv -> world -> coq_val list -> Mem.mem
    -> (((world * trace) * coq_val) * Mem.mem) option) -> (ident -> genv ->
    world -> coq_val list -> Mem.mem ->
    (((world * trace) * coq_val) * Mem.mem) option) -> world -> state ->
    (trace * state) list **)

let do_step ge do_external_function do_inline_assembly w = function
| State (f, s0, k, e, m) ->
  (match s0 with
   | Sskip ->
     (match k with
      | Kstop ->
        (match Mem.free_list m (blocks_of_env e) with
         | Some m' -> ret (Returnstate (Vundef, k, m'))
         | None -> [])
      | Kseq (s1, k0) -> ret (State (f, s1, k0, e, m))
      | Kwhile2 (x, s1, k0) -> ret (State (f, (Swhile (x, s1)), k0, e, m))
      | Kdowhile1 (x, s1, k0) ->
        ret (ExprState (f, x, (Kdowhile2 (x, s1, k0)), e, m))
      | Kfor3 (a2, a3, s1, k0) ->
        ret (State (f, a3, (Kfor4 (a2, a3, s1, k0)), e, m))
      | Kfor4 (a2, a3, s1, k0) ->
        ret (State (f, (Sfor (Sskip, a2, a3, s1)), k0, e, m))
      | Kswitch2 k0 -> ret (State (f, Sskip, k0, e, m))
      | Kcall (f0, e0, e1, t, c) ->
        (match Mem.free_list m (blocks_of_env e) with
         | Some m' -> ret (Returnstate (Vundef, k, m'))
         | None -> [])
      | _ -> [])
   | Sdo x -> ret (ExprState (f, x, (Kdo k), e, m))
   | Ssequence (s1, s2) -> ret (State (f, s1, (Kseq (s2, k)), e, m))
   | Sifthenelse (a, s1, s2) ->
     ret (ExprState (f, a, (Kifthenelse (s1, s2, k)), e, m))
   | Swhile (x, s1) -> ret (ExprState (f, x, (Kwhile1 (x, s1, k)), e, m))
   | Sdowhile (a, s1) -> ret (State (f, s1, (Kdowhile1 (a, s1, k)), e, m))
   | Sfor (a1, a2, a3, s1) ->
     if is_skip a1
     then ret (ExprState (f, a2, (Kfor2 (a2, a3, s1, k)), e, m))
     else ret (State (f, a1, (Kseq ((Sfor (Sskip, a2, a3, s1)), k)), e, m))
   | Sbreak ->
     (match k with
      | Kseq (s1, k0) -> ret (State (f, Sbreak, k0, e, m))
      | Kwhile2 (x, s1, k0) -> ret (State (f, Sskip, k0, e, m))
      | Kdowhile1 (x, s1, k0) -> ret (State (f, Sskip, k0, e, m))
      | Kfor3 (a2, a3, s1, k0) -> ret (State (f, Sskip, k0, e, m))
      | Kswitch2 k0 -> ret (State (f, Sskip, k0, e, m))
      | _ -> [])
   | Scontinue ->
     (match k with
      | Kseq (s1, k0) -> ret (State (f, Scontinue, k0, e, m))
      | Kwhile2 (x, s1, k0) -> ret (State (f, (Swhile (x, s1)), k0, e, m))
      | Kdowhile1 (x, s1, k0) ->
        ret (ExprState (f, x, (Kdowhile2 (x, s1, k0)), e, m))
      | Kfor3 (a2, a3, s1, k0) ->
        ret (State (f, a3, (Kfor4 (a2, a3, s1, k0)), e, m))
      | Kswitch2 k0 -> ret (State (f, Scontinue, k0, e, m))
      | _ -> [])
   | Sreturn o ->
     (match o with
      | Some x -> ret (ExprState (f, x, (Kreturn k), e, m))
      | None ->
        (match Mem.free_list m (blocks_of_env e) with
         | Some m' -> ret (Returnstate (Vundef, (call_cont k), m'))
         | None -> []))
   | Sswitch (x, sl) -> ret (ExprState (f, x, (Kswitch1 (sl, k)), e, m))
   | Slabel (lbl, s1) -> ret (State (f, s1, k, e, m))
   | Sgoto lbl ->
     (match find_label lbl f.fn_body (call_cont k) with
      | Some p -> let (s', k') = p in ret (State (f, s', k', e, m))
      | None -> []))
| ExprState (f, a, k, e, m) ->
  (match is_val a with
   | Some p ->
     let (v, ty) = p in
     (match k with
      | Kdo k0 -> ret (State (f, Sskip, k0, e, m))
      | Kifthenelse (s1, s2, k0) ->
        (match bool_val v ty with
         | Some b -> ret (State (f, (if b then s1 else s2), k0, e, m))
         | None -> [])
      | Kwhile1 (x, s0, k0) ->
        (match bool_val v ty with
         | Some b ->
           if b
           then ret (State (f, s0, (Kwhile2 (x, s0, k0)), e, m))
           else ret (State (f, Sskip, k0, e, m))
         | None -> [])
      | Kdowhile2 (x, s0, k0) ->
        (match bool_val v ty with
         | Some b ->
           if b
           then ret (State (f, (Sdowhile (x, s0)), k0, e, m))
           else ret (State (f, Sskip, k0, e, m))
         | None -> [])
      | Kfor2 (a2, a3, s0, k0) ->
        (match bool_val v ty with
         | Some b ->
           if b
           then ret (State (f, s0, (Kfor3 (a2, a3, s0, k0)), e, m))
           else ret (State (f, Sskip, k0, e, m))
         | None -> [])
      | Kswitch1 (sl, k0) ->
        (match sem_switch_arg v ty with
         | Some n ->
           ret (State (f, (seq_of_labeled_statement (select_switch n sl)),
             (Kswitch2 k0), e, m))
         | None -> [])
      | Kreturn k0 ->
        (match sem_cast v ty f.fn_return with
         | Some v' ->
           (match Mem.free_list m (blocks_of_env e) with
            | Some m' -> ret (Returnstate (v', (call_cont k0), m'))
            | None -> [])
         | None -> [])
      | _ -> [])
   | None ->
     map (expr_final_state f k e)
       (step_expr ge do_external_function do_inline_assembly e w RV a m))
| Callstate (fd, vargs, k, m) ->
  (match fd with
   | Internal f ->
     if list_norepet_dec ident_eq
          (app (var_names f.fn_params) (var_names f.fn_vars))
     then let (e, m1) =
            do_alloc_variables empty_env m (app f.fn_params f.fn_vars)
          in
          (match sem_bind_parameters ge w e m1 f.fn_params vargs with
           | Some m2 -> ret (State (f, f.fn_body, k, e, m2))
           | None -> [])
     else []
   | External (ef, t, t0, c) ->
     (match do_external ge do_external_function do_inline_assembly ef w vargs
              m with
      | Some p ->
        let (p0, m') = p in
        let (p1, v) = p0 in
        let (w', t1) = p1 in (t1, (Returnstate (v, k, m'))) :: []
      | None -> []))
| Returnstate (v, k0, m) ->
  (match k0 with
   | Kcall (f, e, c, ty, k) ->
     ret (ExprState (f, (c (Eval (v, ty))), k, e, m))
   | _ -> [])
| Stuckstate -> []

(** val do_initial_state : program -> (genv * state) option **)

let do_initial_state p =
  let ge = Genv.globalenv p in
  (match Genv.init_mem p with
   | Some m0 ->
     (match Genv.find_symbol ge p.prog_main with
      | Some b ->
        (match Genv.find_funct_ptr ge b with
         | Some f ->
           if type_eq (type_of_fundef f) (Tfunction (Tnil, type_int32s,
                cc_default))
           then Some (ge, (Callstate (f, [], Kstop, m0)))
           else None
         | None -> None)
      | None -> None)
   | None -> None)

(** val at_final_state : state -> Int.int option **)

let at_final_state = function
| Returnstate (res, k, m) ->
  (match res with
   | Vint r ->
     (match k with
      | Kstop -> Some r
      | _ -> None)
   | _ -> None)
| _ -> None

