open AST
open BinPos
open Clight
open Cop
open Csyntax
open Ctypes
open Datatypes
open Errors
open Integers
open Values

type generator = { gen_next : ident; gen_trail : (ident * coq_type) list }

(** val gen_next : generator -> ident **)

let gen_next x = x.gen_next

(** val gen_trail : generator -> (ident * coq_type) list **)

let gen_trail x = x.gen_trail

type 'a result =
| Err of errmsg
| Res of 'a * generator

type 'a mon = generator -> 'a result

(** val first_unused_ident : unit -> ident **)

let first_unused_ident = Camlcoq.first_unused_ident

(** val initial_generator : unit -> generator **)

let initial_generator x =
  { gen_next = (first_unused_ident x); gen_trail = [] }

(** val gensym : coq_type -> ident mon **)

let gensym ty g =
  Res (g.gen_next, { gen_next = (Pos.succ g.gen_next); gen_trail =
    ((g.gen_next, ty) :: g.gen_trail) })

(** val reset_trail : unit mon **)

let reset_trail g =
  Res ((), { gen_next = g.gen_next; gen_trail = [] })

(** val get_trail : (ident * coq_type) list mon **)

let get_trail g =
  Res (g.gen_trail, g)

(** val makeseq_rec :
    Clight.statement -> Clight.statement list -> Clight.statement **)

let rec makeseq_rec s = function
| [] -> s
| s' :: l' -> makeseq_rec (Clight.Ssequence (s, s')) l'

(** val makeseq : Clight.statement list -> Clight.statement **)

let makeseq l =
  makeseq_rec Clight.Sskip l

(** val eval_simpl_expr : Clight.expr -> coq_val option **)

let rec eval_simpl_expr = function
| Econst_int (n, t) -> Some (Vint n)
| Econst_float (n, t) -> Some (Vfloat n)
| Econst_single (n, t) -> Some (Vsingle n)
| Econst_long (n, t) -> Some (Vlong n)
| Clight.Ecast (b, ty) ->
  (match eval_simpl_expr b with
   | Some v -> sem_cast v (Clight.typeof b) ty
   | None -> None)
| _ -> None

(** val makeif :
    Clight.expr -> Clight.statement -> Clight.statement -> Clight.statement **)

let makeif a s1 s2 =
  match eval_simpl_expr a with
  | Some v ->
    (match bool_val v (Clight.typeof a) with
     | Some b -> if b then s1 else s2
     | None -> Clight.Sifthenelse (a, s1, s2))
  | None -> Clight.Sifthenelse (a, s1, s2)

(** val transl_incrdecr :
    incr_or_decr -> Clight.expr -> coq_type -> Clight.expr **)

let transl_incrdecr id a ty =
  match id with
  | Incr ->
    Clight.Ebinop (Oadd, a, (Econst_int (Int.one, type_int32s)),
      (incrdecr_type ty))
  | Decr ->
    Clight.Ebinop (Osub, a, (Econst_int (Int.one, type_int32s)),
      (incrdecr_type ty))

(** val chunk_for_volatile_type : coq_type -> memory_chunk option **)

let chunk_for_volatile_type ty =
  if type_is_volatile ty
  then (match access_mode ty with
        | By_value chunk -> Some chunk
        | _ -> None)
  else None

(** val make_set : ident -> Clight.expr -> Clight.statement **)

let make_set id l =
  match chunk_for_volatile_type (Clight.typeof l) with
  | Some chunk ->
    let typtr = Tpointer ((Clight.typeof l), noattr) in
    Sbuiltin ((Some id), (EF_vload chunk), (Tcons (typtr, Tnil)),
    ((Clight.Eaddrof (l, typtr)) :: []))
  | None -> Sset (id, l)

(** val transl_valof :
    coq_type -> Clight.expr -> (Clight.statement list * Clight.expr) mon **)

let transl_valof ty l g =
  if type_is_volatile ty
  then (match gensym ty g with
        | Err msg0 -> Err msg0
        | Res (a, g') ->
          Res ((((make_set a l) :: []), (Etempvar (a, ty))), g'))
  else Res (([], l), g)

(** val make_assign : Clight.expr -> Clight.expr -> Clight.statement **)

let make_assign l r =
  match chunk_for_volatile_type (Clight.typeof l) with
  | Some chunk ->
    let ty = Clight.typeof l in
    let typtr = Tpointer (ty, noattr) in
    Sbuiltin (None, (EF_vstore chunk), (Tcons (typtr, (Tcons (ty, Tnil)))),
    ((Clight.Eaddrof (l, typtr)) :: (r :: [])))
  | None -> Sassign (l, r)

type set_destination =
| SDbase of coq_type * ident
| SDcons of coq_type * ident * set_destination

type destination =
| For_val
| For_effects
| For_set of set_destination

(** val dummy_expr : Clight.expr **)

let dummy_expr =
  Econst_int (Int.zero, type_int32s)

(** val do_set : set_destination -> Clight.expr -> Clight.statement list **)

let rec do_set sd a =
  match sd with
  | SDbase (ty, tmp) -> (Sset (tmp, (Clight.Ecast (a, ty)))) :: []
  | SDcons (ty, tmp, sd') ->
    (Sset (tmp, (Clight.Ecast (a, ty)))) :: (do_set sd' (Etempvar (tmp, ty)))

(** val finish :
    destination -> Clight.statement list -> Clight.expr -> Clight.statement
    list * Clight.expr **)

let finish dst sl a =
  match dst with
  | For_set sd -> ((app sl (do_set sd a)), a)
  | _ -> (sl, a)

(** val sd_temp : set_destination -> ident **)

let sd_temp = function
| SDbase (ty, tmp) -> tmp
| SDcons (ty, tmp, sd0) -> tmp

(** val sd_seqbool_val : ident -> coq_type -> set_destination **)

let sd_seqbool_val tmp ty =
  SDcons (type_bool, tmp, (SDbase (ty, tmp)))

(** val sd_seqbool_set : coq_type -> set_destination -> set_destination **)

let sd_seqbool_set ty sd =
  let tmp = sd_temp sd in SDcons (type_bool, tmp, (SDcons (ty, tmp, sd)))

(** val transl_expr :
    destination -> expr -> (Clight.statement list * Clight.expr) mon **)

let rec transl_expr dst = function
| Eval (v, ty) ->
  (fun g ->
    match v with
    | Vint n -> Res ((finish dst [] (Econst_int (n, ty))), g)
    | Vlong n -> Res ((finish dst [] (Econst_long (n, ty))), g)
    | Vfloat n -> Res ((finish dst [] (Econst_float (n, ty))), g)
    | Vsingle n -> Res ((finish dst [] (Econst_single (n, ty))), g)
    | _ ->
      Err
        (msg
          ('S'::('i'::('m'::('p'::('l'::('E'::('x'::('p'::('r'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('e'::('x'::('p'::('r'::(':'::(' '::('E'::('v'::('a'::('l'::[])))))))))))))))))))))))))))))
| Evar (x, ty) -> (fun g -> Res ((finish dst [] (Clight.Evar (x, ty))), g))
| Efield (r, f, ty) ->
  (fun g ->
    match transl_expr For_val r g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      Res ((finish dst (fst a0) (Clight.Efield ((snd a0), f, ty))), g'))
| Evalof (l, ty) ->
  (fun g ->
    match transl_expr For_val l g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      (match transl_valof (typeof l) (snd a0) g' with
       | Err msg0 -> Err msg0
       | Res (a1, g'0) ->
         Res ((finish dst (app (fst a0) (fst a1)) (snd a1)), g'0)))
| Ederef (r, ty) ->
  (fun g ->
    match transl_expr For_val r g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      Res ((finish dst (fst a0) (Clight.Ederef ((snd a0), ty))), g'))
| Eaddrof (l, ty) ->
  (fun g ->
    match transl_expr For_val l g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      Res ((finish dst (fst a0) (Clight.Eaddrof ((snd a0), ty))), g'))
| Eunop (op, r1, ty) ->
  (fun g ->
    match transl_expr For_val r1 g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      Res ((finish dst (fst a0) (Clight.Eunop (op, (snd a0), ty))), g'))
| Ebinop (op, r1, r2, ty) ->
  (fun g ->
    match transl_expr For_val r1 g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      (match transl_expr For_val r2 g' with
       | Err msg0 -> Err msg0
       | Res (a1, g'0) ->
         Res
           ((finish dst (app (fst a0) (fst a1)) (Clight.Ebinop (op, (snd a0),
              (snd a1), ty))), g'0)))
| Ecast (r1, ty) ->
  (fun g ->
    match transl_expr For_val r1 g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      Res ((finish dst (fst a0) (Clight.Ecast ((snd a0), ty))), g'))
| Eseqand (r1, r2, ty) ->
  (fun g ->
    match transl_expr For_val r1 g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      (match dst with
       | For_val ->
         (match gensym ty g' with
          | Err msg0 -> Err msg0
          | Res (a1, g'0) ->
            (match transl_expr (For_set (sd_seqbool_val a1 ty)) r2 g'0 with
             | Err msg0 -> Err msg0
             | Res (a2, g'1) ->
               Res
                 (((app (fst a0)
                     ((makeif (snd a0) (makeseq (fst a2)) (Sset (a1,
                        (Econst_int (Int.zero, ty))))) :: [])), (Etempvar
                 (a1, ty))), g'1)))
       | For_effects ->
         (match transl_expr For_effects r2 g' with
          | Err msg0 -> Err msg0
          | Res (a1, g'0) ->
            Res
              (((app (fst a0)
                  ((makeif (snd a0) (makeseq (fst a1)) Clight.Sskip) :: [])),
              dummy_expr), g'0))
       | For_set sd ->
         (match transl_expr (For_set (sd_seqbool_set ty sd)) r2 g' with
          | Err msg0 -> Err msg0
          | Res (a1, g'0) ->
            Res
              (((app (fst a0)
                  ((makeif (snd a0) (makeseq (fst a1))
                     (makeseq (do_set sd (Econst_int (Int.zero, ty))))) :: [])),
              dummy_expr), g'0))))
| Eseqor (r1, r2, ty) ->
  (fun g ->
    match transl_expr For_val r1 g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      (match dst with
       | For_val ->
         (match gensym ty g' with
          | Err msg0 -> Err msg0
          | Res (a1, g'0) ->
            (match transl_expr (For_set (sd_seqbool_val a1 ty)) r2 g'0 with
             | Err msg0 -> Err msg0
             | Res (a2, g'1) ->
               Res
                 (((app (fst a0)
                     ((makeif (snd a0) (Sset (a1, (Econst_int (Int.one,
                        ty)))) (makeseq (fst a2))) :: [])), (Etempvar (a1,
                 ty))), g'1)))
       | For_effects ->
         (match transl_expr For_effects r2 g' with
          | Err msg0 -> Err msg0
          | Res (a1, g'0) ->
            Res
              (((app (fst a0)
                  ((makeif (snd a0) Clight.Sskip (makeseq (fst a1))) :: [])),
              dummy_expr), g'0))
       | For_set sd ->
         (match transl_expr (For_set (sd_seqbool_set ty sd)) r2 g' with
          | Err msg0 -> Err msg0
          | Res (a1, g'0) ->
            Res
              (((app (fst a0)
                  ((makeif (snd a0)
                     (makeseq (do_set sd (Econst_int (Int.one, ty))))
                     (makeseq (fst a1))) :: [])), dummy_expr), g'0))))
| Econdition (r1, r2, r3, ty) ->
  (fun g ->
    match transl_expr For_val r1 g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      (match dst with
       | For_val ->
         (match gensym ty g' with
          | Err msg0 -> Err msg0
          | Res (a1, g'0) ->
            (match transl_expr (For_set (SDbase (ty, a1))) r2 g'0 with
             | Err msg0 -> Err msg0
             | Res (a2, g'1) ->
               (match transl_expr (For_set (SDbase (ty, a1))) r3 g'1 with
                | Err msg0 -> Err msg0
                | Res (a3, g'2) ->
                  Res
                    (((app (fst a0)
                        ((makeif (snd a0) (makeseq (fst a2))
                           (makeseq (fst a3))) :: [])), (Etempvar (a1, ty))),
                    g'2))))
       | For_effects ->
         (match transl_expr For_effects r2 g' with
          | Err msg0 -> Err msg0
          | Res (a1, g'0) ->
            (match transl_expr For_effects r3 g'0 with
             | Err msg0 -> Err msg0
             | Res (a2, g'1) ->
               Res
                 (((app (fst a0)
                     ((makeif (snd a0) (makeseq (fst a1)) (makeseq (fst a2))) :: [])),
                 dummy_expr), g'1)))
       | For_set sd ->
         (match gensym ty g' with
          | Err msg0 -> Err msg0
          | Res (a1, g'0) ->
            (match transl_expr (For_set (SDcons (ty, a1, sd))) r2 g'0 with
             | Err msg0 -> Err msg0
             | Res (a2, g'1) ->
               (match transl_expr (For_set (SDcons (ty, a1, sd))) r3 g'1 with
                | Err msg0 -> Err msg0
                | Res (a3, g'2) ->
                  Res
                    (((app (fst a0)
                        ((makeif (snd a0) (makeseq (fst a2))
                           (makeseq (fst a3))) :: [])), dummy_expr), g'2))))))
| Esizeof (ty', ty) ->
  (fun g -> Res ((finish dst [] (coq_Esizeof ty' ty)), g))
| Ealignof (ty', ty) ->
  (fun g -> Res ((finish dst [] (coq_Ealignof ty' ty)), g))
| Eassign (l1, r2, ty) ->
  (fun g ->
    match transl_expr For_val l1 g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      (match transl_expr For_val r2 g' with
       | Err msg0 -> Err msg0
       | Res (a1, g'0) ->
         let ty1 = typeof l1 in
         let ty2 = typeof r2 in
         (match dst with
          | For_effects ->
            Res
              (((app (fst a0)
                  (app (fst a1) ((make_assign (snd a0) (snd a1)) :: []))),
              dummy_expr), g'0)
          | _ ->
            (match gensym ty2 g'0 with
             | Err msg0 -> Err msg0
             | Res (a2, g'1) ->
               Res
                 ((finish dst
                    (app (fst a0)
                      (app (fst a1) ((Sset (a2,
                        (snd a1))) :: ((make_assign (snd a0) (Etempvar (a2,
                                         ty2))) :: [])))) (Clight.Ecast
                    ((Etempvar (a2, ty2)), ty1))), g'1)))))
| Eassignop (op, l1, r2, tyres, ty) ->
  let ty1 = typeof l1 in
  (fun g ->
  match transl_expr For_val l1 g with
  | Err msg0 -> Err msg0
  | Res (a0, g') ->
    let a1 = snd a0 in
    (match transl_expr For_val r2 g' with
     | Err msg0 -> Err msg0
     | Res (a2, g'0) ->
       (match transl_valof ty1 a1 g'0 with
        | Err msg0 -> Err msg0
        | Res (a3, g'1) ->
          (match dst with
           | For_effects ->
             Res
               (((app (fst a0)
                   (app (fst a2)
                     (app (fst a3)
                       ((make_assign a1 (Clight.Ebinop (op, (snd a3),
                          (snd a2), tyres))) :: [])))), dummy_expr), g'1)
           | _ ->
             (match gensym tyres g'1 with
              | Err msg0 -> Err msg0
              | Res (a4, g'2) ->
                Res
                  ((finish dst
                     (app (fst a0)
                       (app (fst a2)
                         (app (fst a3) ((Sset (a4, (Clight.Ebinop (op,
                           (snd a3), (snd a2),
                           tyres)))) :: ((make_assign a1 (Etempvar (a4,
                                           tyres))) :: []))))) (Clight.Ecast
                     ((Etempvar (a4, tyres)), ty1))), g'2))))))
| Epostincr (id, l1, ty) ->
  let ty1 = typeof l1 in
  (fun g ->
  match transl_expr For_val l1 g with
  | Err msg0 -> Err msg0
  | Res (a0, g') ->
    let a1 = snd a0 in
    (match dst with
     | For_effects ->
       (match transl_valof ty1 a1 g' with
        | Err msg0 -> Err msg0
        | Res (a2, g'0) ->
          Res
            (((app (fst a0)
                (app (fst a2)
                  ((make_assign a1 (transl_incrdecr id (snd a2) ty1)) :: []))),
            dummy_expr), g'0))
     | _ ->
       (match gensym ty1 g' with
        | Err msg0 -> Err msg0
        | Res (a2, g'0) ->
          Res
            ((finish dst
               (app (fst a0)
                 ((make_set a2 a1) :: ((make_assign a1
                                         (transl_incrdecr id (Etempvar (a2,
                                           ty1)) ty1)) :: []))) (Etempvar
               (a2, ty1))), g'0))))
| Ecomma (r1, r2, ty) ->
  (fun g ->
    match transl_expr For_effects r1 g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      (match transl_expr dst r2 g' with
       | Err msg0 -> Err msg0
       | Res (a1, g'0) -> Res (((app (fst a0) (fst a1)), (snd a1)), g'0)))
| Ecall (r1, rl2, ty) ->
  (fun g ->
    match transl_expr For_val r1 g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      (match transl_exprlist rl2 g' with
       | Err msg0 -> Err msg0
       | Res (a1, g'0) ->
         (match dst with
          | For_effects ->
            Res
              (((app (fst a0)
                  (app (fst a1) ((Scall (None, (snd a0), (snd a1))) :: []))),
              dummy_expr), g'0)
          | _ ->
            (match gensym ty g'0 with
             | Err msg0 -> Err msg0
             | Res (a2, g'1) ->
               Res
                 ((finish dst
                    (app (fst a0)
                      (app (fst a1) ((Scall ((Some a2), (snd a0),
                        (snd a1))) :: []))) (Etempvar (a2, ty))), g'1)))))
| Ebuiltin (ef, tyargs, rl, ty) ->
  (fun g ->
    match transl_exprlist rl g with
    | Err msg0 -> Err msg0
    | Res (a0, g') ->
      (match dst with
       | For_effects ->
         Res
           (((app (fst a0) ((Sbuiltin (None, ef, tyargs, (snd a0))) :: [])),
           dummy_expr), g')
       | _ ->
         (match gensym ty g' with
          | Err msg0 -> Err msg0
          | Res (a1, g'0) ->
            Res
              ((finish dst
                 (app (fst a0) ((Sbuiltin ((Some a1), ef, tyargs,
                   (snd a0))) :: [])) (Etempvar (a1, ty))), g'0))))
| Eloc (b, ofs, ty) ->
  (fun g -> Err
    (msg
      ('S'::('i'::('m'::('p'::('l'::('E'::('x'::('p'::('r'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('e'::('x'::('p'::('r'::(':'::(' '::('E'::('l'::('o'::('c'::[])))))))))))))))))))))))))))))
| Eparen (r1, ty) ->
  (fun g -> Err
    (msg
      ('S'::('i'::('m'::('p'::('l'::('E'::('x'::('p'::('r'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('e'::('x'::('p'::('r'::(':'::(' '::('p'::('a'::('r'::('e'::('n'::[]))))))))))))))))))))))))))))))

(** val transl_exprlist :
    exprlist -> (Clight.statement list * Clight.expr list) mon **)

and transl_exprlist rl g =
  match rl with
  | Enil -> Res (([], []), g)
  | Econs (r1, rl2) ->
    (match transl_expr For_val r1 g with
     | Err msg0 -> Err msg0
     | Res (a, g') ->
       (match transl_exprlist rl2 g' with
        | Err msg0 -> Err msg0
        | Res (a0, g'0) ->
          Res (((app (fst a) (fst a0)), ((snd a) :: (snd a0))), g'0)))

(** val transl_expression : expr -> (Clight.statement * Clight.expr) mon **)

let transl_expression r g =
  match transl_expr For_val r g with
  | Err msg0 -> Err msg0
  | Res (a, g') -> Res (((makeseq (fst a)), (snd a)), g')

(** val transl_expr_stmt : expr -> Clight.statement mon **)

let transl_expr_stmt r g =
  match transl_expr For_effects r g with
  | Err msg0 -> Err msg0
  | Res (a, g') -> Res ((makeseq (fst a)), g')

(** val transl_if :
    expr -> Clight.statement -> Clight.statement -> Clight.statement mon **)

let transl_if r s1 s2 g =
  match transl_expr For_val r g with
  | Err msg0 -> Err msg0
  | Res (a, g') ->
    Res ((makeseq (app (fst a) ((makeif (snd a) s1 s2) :: []))), g')

(** val is_Sskip : statement -> bool **)

let is_Sskip = function
| Sskip -> true
| _ -> false

(** val transl_stmt : statement -> Clight.statement mon **)

let rec transl_stmt = function
| Sskip -> (fun g -> Res (Clight.Sskip, g))
| Sdo e -> transl_expr_stmt e
| Ssequence (s1, s2) ->
  (fun g ->
    match transl_stmt s1 g with
    | Err msg0 -> Err msg0
    | Res (a, g') ->
      (match transl_stmt s2 g' with
       | Err msg0 -> Err msg0
       | Res (a0, g'0) -> Res ((Clight.Ssequence (a, a0)), g'0)))
| Sifthenelse (e, s1, s2) ->
  (fun g ->
    match transl_stmt s1 g with
    | Err msg0 -> Err msg0
    | Res (a, g') ->
      (match transl_stmt s2 g' with
       | Err msg0 -> Err msg0
       | Res (a0, g'0) ->
         (match transl_expression e g'0 with
          | Err msg0 -> Err msg0
          | Res (a1, g'1) ->
            Res ((Clight.Ssequence ((fst a1), (Clight.Sifthenelse ((snd a1),
              a, a0)))), g'1))))
| Swhile (e, s1) ->
  (fun g ->
    match transl_if e Clight.Sskip Clight.Sbreak g with
    | Err msg0 -> Err msg0
    | Res (a, g') ->
      (match transl_stmt s1 g' with
       | Err msg0 -> Err msg0
       | Res (a0, g'0) ->
         Res ((Sloop ((Clight.Ssequence (a, a0)), Clight.Sskip)), g'0)))
| Sdowhile (e, s1) ->
  (fun g ->
    match transl_if e Clight.Sskip Clight.Sbreak g with
    | Err msg0 -> Err msg0
    | Res (a, g') ->
      (match transl_stmt s1 g' with
       | Err msg0 -> Err msg0
       | Res (a0, g'0) -> Res ((Sloop (a0, a)), g'0)))
| Sfor (s1, e2, s3, s4) ->
  (fun g ->
    match transl_stmt s1 g with
    | Err msg0 -> Err msg0
    | Res (a, g') ->
      (match transl_if e2 Clight.Sskip Clight.Sbreak g' with
       | Err msg0 -> Err msg0
       | Res (a0, g'0) ->
         (match transl_stmt s3 g'0 with
          | Err msg0 -> Err msg0
          | Res (a1, g'1) ->
            (match transl_stmt s4 g'1 with
             | Err msg0 -> Err msg0
             | Res (a2, g'2) ->
               if is_Sskip s1
               then Res ((Sloop ((Clight.Ssequence (a0, a2)), a1)), g'2)
               else Res ((Clight.Ssequence (a, (Sloop ((Clight.Ssequence (a0,
                      a2)), a1)))), g'2)))))
| Sbreak -> (fun g -> Res (Clight.Sbreak, g))
| Scontinue -> (fun g -> Res (Clight.Scontinue, g))
| Sreturn o ->
  (fun g ->
    match o with
    | Some e ->
      (match transl_expression e g with
       | Err msg0 -> Err msg0
       | Res (a, g') ->
         Res ((Clight.Ssequence ((fst a), (Clight.Sreturn (Some (snd a))))),
           g'))
    | None -> Res ((Clight.Sreturn None), g))
| Sswitch (e, ls) ->
  (fun g ->
    match transl_expression e g with
    | Err msg0 -> Err msg0
    | Res (a, g') ->
      (match transl_lblstmt ls g' with
       | Err msg0 -> Err msg0
       | Res (a0, g'0) ->
         Res ((Clight.Ssequence ((fst a), (Clight.Sswitch ((snd a), a0)))),
           g'0)))
| Slabel (lbl, s1) ->
  (fun g ->
    match transl_stmt s1 g with
    | Err msg0 -> Err msg0
    | Res (a, g') -> Res ((Clight.Slabel (lbl, a)), g'))
| Sgoto lbl -> (fun g -> Res ((Clight.Sgoto lbl), g))

(** val transl_lblstmt :
    labeled_statements -> Clight.labeled_statements mon **)

and transl_lblstmt ls g =
  match ls with
  | LSnil -> Res (Clight.LSnil, g)
  | LScons (c, s, ls1) ->
    (match transl_stmt s g with
     | Err msg0 -> Err msg0
     | Res (a, g') ->
       (match transl_lblstmt ls1 g' with
        | Err msg0 -> Err msg0
        | Res (a0, g'0) -> Res ((Clight.LScons (c, a, a0)), g'0)))

(** val transl_function : coq_function -> Clight.coq_function mon **)

let transl_function f g =
  match reset_trail g with
  | Err msg0 -> Err msg0
  | Res (a, g') ->
    (match transl_stmt f.fn_body g' with
     | Err msg0 -> Err msg0
     | Res (a0, g'0) ->
       (match get_trail g'0 with
        | Err msg0 -> Err msg0
        | Res (a1, g'1) ->
          Res ({ Clight.fn_return = f.fn_return; Clight.fn_callconv =
            f.fn_callconv; Clight.fn_params = f.fn_params; Clight.fn_vars =
            f.fn_vars; fn_temps = a1; Clight.fn_body = a0 }, g'1)))

(** val transl_fundef : fundef -> Clight.fundef mon **)

let transl_fundef fd g =
  match fd with
  | Internal f ->
    (match transl_function f g with
     | Err msg0 -> Err msg0
     | Res (a, g') -> Res ((Clight.Internal a), g'))
  | External (ef, targs, tres, cconv) ->
    Res ((Clight.External (ef, targs, tres, cconv)), g)

(** val transl_globdefs :
    (ident * (fundef, coq_type) globdef) list -> generator ->
    (ident * (Clight.fundef, coq_type) globdef) list res **)

let rec transl_globdefs l g =
  match l with
  | [] -> OK []
  | p :: l' ->
    let (id, g0) = p in
    (match g0 with
     | Gfun f ->
       (match transl_fundef f g with
        | Err msg0 ->
          Error ((MSG
            ('I'::('n'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::[]))))))))))))) :: ((CTX
            id) :: ((MSG (':'::(' '::[]))) :: msg0)))
        | Res (tf, g') ->
          (match transl_globdefs l' g' with
           | OK x -> OK ((id, (Gfun tf)) :: x)
           | Error msg0 -> Error msg0))
     | Gvar v ->
       (match transl_globdefs l' g with
        | OK x -> OK ((id, (Gvar v)) :: x)
        | Error msg0 -> Error msg0))

(** val transl_program : program -> Clight.program res **)

let transl_program p =
  match transl_globdefs p.prog_defs (initial_generator ()) with
  | OK x -> OK { prog_defs = x; prog_main = p.prog_main }
  | Error msg0 -> Error msg0

