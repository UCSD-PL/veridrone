open BinInt
open BinNums
open CminorSel
open Compopts
open Coqlib
open Datatypes
open Floats
open Integers
open Op
open SelectOp
open Zpower

(** val find_div_mul_params :
    nat -> coq_Z -> coq_Z -> coq_Z -> (coq_Z * coq_Z) option **)

let rec find_div_mul_params fuel nc d p =
  match fuel with
  | O -> None
  | S fuel' ->
    let twp = two_p p in
    if zlt (Z.mul nc (Z.sub d (Z.modulo twp d))) twp
    then Some
           ((Z.sub p (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
              Coq_xH))))))),
           (Z.div (Z.sub (Z.add twp d) (Z.modulo twp d)) d))
    else find_div_mul_params fuel' nc d (Z.add p (Zpos Coq_xH))

(** val divs_mul_params : coq_Z -> (coq_Z * coq_Z) option **)

let divs_mul_params d =
  match find_div_mul_params Int.wordsize
          (Z.sub (Z.sub Int.half_modulus (Z.modulo Int.half_modulus d)) (Zpos
            Coq_xH)) d (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))) with
  | Some p0 ->
    let (p, m) = p0 in
    if (&&)
         ((&&)
           ((&&)
             ((&&)
               ((&&)
                 ((&&) ((fun x -> x) (zlt Z0 d))
                   ((fun x -> x)
                     (zlt
                       (two_p
                         (Z.add (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                           Coq_xH)))))) p)) (Z.mul m d))))
                 ((fun x -> x)
                   (zle (Z.mul m d)
                     (Z.add
                       (two_p
                         (Z.add (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                           Coq_xH)))))) p)) (two_p (Z.add p (Zpos Coq_xH)))))))
               ((fun x -> x) (zle Z0 m))) ((fun x -> x) (zlt m Int.modulus)))
           ((fun x -> x) (zle Z0 p)))
         ((fun x -> x)
           (zlt p (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))
    then Some (p, m)
    else None
  | None -> None

(** val divu_mul_params : coq_Z -> (coq_Z * coq_Z) option **)

let divu_mul_params d =
  match find_div_mul_params Int.wordsize
          (Z.sub (Z.sub Int.modulus (Z.modulo Int.modulus d)) (Zpos Coq_xH))
          d (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))) with
  | Some p0 ->
    let (p, m) = p0 in
    if (&&)
         ((&&)
           ((&&)
             ((&&)
               ((&&)
                 ((&&) ((fun x -> x) (zlt Z0 d))
                   ((fun x -> x)
                     (zle
                       (two_p
                         (Z.add (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                           Coq_xH)))))) p)) (Z.mul m d))))
                 ((fun x -> x)
                   (zle (Z.mul m d)
                     (Z.add
                       (two_p
                         (Z.add (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                           Coq_xH)))))) p)) (two_p p)))))
               ((fun x -> x) (zle Z0 m))) ((fun x -> x) (zlt m Int.modulus)))
           ((fun x -> x) (zle Z0 p)))
         ((fun x -> x)
           (zlt p (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))
    then Some (p, m)
    else None
  | None -> None

(** val divu_mul : coq_Z -> coq_Z -> expr **)

let divu_mul p m =
  shruimm (Eop (Omulhu, (Econs ((Eletvar O), (Econs ((Eop ((Ointconst
    (Int.repr m)), Enil)), Enil)))))) (Int.repr p)

(** val divuimm : expr -> Int.int -> expr **)

let divuimm e1 n2 =
  match Int.is_power2 n2 with
  | Some l -> shruimm e1 l
  | None ->
    if optim_for_size ()
    then divu_base e1 (Eop ((Ointconst n2), Enil))
    else (match divu_mul_params (Int.unsigned n2) with
          | Some p0 -> let (p, m) = p0 in Elet (e1, (divu_mul p m))
          | None -> divu_base e1 (Eop ((Ointconst n2), Enil)))

type divu_cases =
| Coq_divu_case1 of Int.int
| Coq_divu_default of expr

(** val divu_match : expr -> divu_cases **)

let divu_match = function
| Eop (o, e) ->
  (match o with
   | Ointconst n2 ->
     (match e with
      | Enil -> Coq_divu_case1 n2
      | Econs (e0, e1) ->
        Coq_divu_default (Eop ((Ointconst n2), (Econs (e0, e1)))))
   | x -> Coq_divu_default (Eop (x, e)))
| x -> Coq_divu_default x

(** val divu : expr -> expr -> expr **)

let divu e1 e2 =
  match divu_match e2 with
  | Coq_divu_case1 n2 -> divuimm e1 n2
  | Coq_divu_default e3 -> divu_base e1 e3

(** val mod_from_div : expr -> Int.int -> expr **)

let mod_from_div equo n =
  Eop (Osub, (Econs ((Eletvar O), (Econs ((mulimm n equo), Enil)))))

(** val moduimm : expr -> Int.int -> expr **)

let moduimm e1 n2 =
  match Int.is_power2 n2 with
  | Some l -> andimm (Int.sub n2 Int.one) e1
  | None ->
    if optim_for_size ()
    then modu_base e1 (Eop ((Ointconst n2), Enil))
    else (match divu_mul_params (Int.unsigned n2) with
          | Some p0 ->
            let (p, m) = p0 in Elet (e1, (mod_from_div (divu_mul p m) n2))
          | None -> modu_base e1 (Eop ((Ointconst n2), Enil)))

type modu_cases =
| Coq_modu_case1 of Int.int
| Coq_modu_default of expr

(** val modu_match : expr -> modu_cases **)

let modu_match = function
| Eop (o, e) ->
  (match o with
   | Ointconst n2 ->
     (match e with
      | Enil -> Coq_modu_case1 n2
      | Econs (e0, e1) ->
        Coq_modu_default (Eop ((Ointconst n2), (Econs (e0, e1)))))
   | x -> Coq_modu_default (Eop (x, e)))
| x -> Coq_modu_default x

(** val modu : expr -> expr -> expr **)

let modu e1 e2 =
  match modu_match e2 with
  | Coq_modu_case1 n2 -> moduimm e1 n2
  | Coq_modu_default e3 -> modu_base e1 e3

(** val divs_mul : coq_Z -> coq_Z -> expr **)

let divs_mul p m =
  let e2 = Eop (Omulhs, (Econs ((Eletvar O), (Econs ((Eop ((Ointconst
    (Int.repr m)), Enil)), Enil)))))
  in
  let e3 = if zlt m Int.half_modulus then e2 else add e2 (Eletvar O) in
  add (shrimm e3 (Int.repr p))
    (shruimm (Eletvar O) (Int.repr (Z.sub Int.zwordsize (Zpos Coq_xH))))

(** val divsimm : expr -> Int.int -> expr **)

let divsimm e1 n2 =
  match Int.is_power2 n2 with
  | Some l ->
    if Int.ltu l (Int.repr (Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
    then shrximm e1 l
    else divs_base e1 (Eop ((Ointconst n2), Enil))
  | None ->
    if optim_for_size ()
    then divs_base e1 (Eop ((Ointconst n2), Enil))
    else (match divs_mul_params (Int.signed n2) with
          | Some p0 -> let (p, m) = p0 in Elet (e1, (divs_mul p m))
          | None -> divs_base e1 (Eop ((Ointconst n2), Enil)))

type divs_cases =
| Coq_divs_case1 of Int.int
| Coq_divs_default of expr

(** val divs_match : expr -> divs_cases **)

let divs_match = function
| Eop (o, e) ->
  (match o with
   | Ointconst n2 ->
     (match e with
      | Enil -> Coq_divs_case1 n2
      | Econs (e0, e1) ->
        Coq_divs_default (Eop ((Ointconst n2), (Econs (e0, e1)))))
   | x -> Coq_divs_default (Eop (x, e)))
| x -> Coq_divs_default x

(** val divs : expr -> expr -> expr **)

let divs e1 e2 =
  match divs_match e2 with
  | Coq_divs_case1 n2 -> divsimm e1 n2
  | Coq_divs_default e3 -> divs_base e1 e3

(** val modsimm : expr -> Int.int -> expr **)

let modsimm e1 n2 =
  match Int.is_power2 n2 with
  | Some l ->
    if Int.ltu l (Int.repr (Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
    then Elet (e1, (mod_from_div (shrximm (Eletvar O) l) n2))
    else mods_base e1 (Eop ((Ointconst n2), Enil))
  | None ->
    if optim_for_size ()
    then mods_base e1 (Eop ((Ointconst n2), Enil))
    else (match divs_mul_params (Int.signed n2) with
          | Some p0 ->
            let (p, m) = p0 in Elet (e1, (mod_from_div (divs_mul p m) n2))
          | None -> mods_base e1 (Eop ((Ointconst n2), Enil)))

type mods_cases =
| Coq_mods_case1 of Int.int
| Coq_mods_default of expr

(** val mods_match : expr -> mods_cases **)

let mods_match = function
| Eop (o, e) ->
  (match o with
   | Ointconst n2 ->
     (match e with
      | Enil -> Coq_mods_case1 n2
      | Econs (e0, e1) ->
        Coq_mods_default (Eop ((Ointconst n2), (Econs (e0, e1)))))
   | x -> Coq_mods_default (Eop (x, e)))
| x -> Coq_mods_default x

(** val mods : expr -> expr -> expr **)

let mods e1 e2 =
  match mods_match e2 with
  | Coq_mods_case1 n2 -> modsimm e1 n2
  | Coq_mods_default e3 -> mods_base e1 e3

(** val divfimm : expr -> float -> expr **)

let divfimm e n =
  match Float.exact_inverse n with
  | Some n' ->
    Eop (Omulf, (Econs (e, (Econs ((Eop ((Ofloatconst n'), Enil)), Enil)))))
  | None ->
    Eop (Odivf, (Econs (e, (Econs ((Eop ((Ofloatconst n), Enil)), Enil)))))

type divf_cases =
| Coq_divf_case1 of float
| Coq_divf_default of expr

(** val divf_match : expr -> divf_cases **)

let divf_match = function
| Eop (o, e) ->
  (match o with
   | Ofloatconst n2 ->
     (match e with
      | Enil -> Coq_divf_case1 n2
      | Econs (e0, e1) ->
        Coq_divf_default (Eop ((Ofloatconst n2), (Econs (e0, e1)))))
   | x -> Coq_divf_default (Eop (x, e)))
| x -> Coq_divf_default x

(** val divf : expr -> expr -> expr **)

let divf e1 e2 =
  match divf_match e2 with
  | Coq_divf_case1 n2 -> divfimm e1 n2
  | Coq_divf_default e3 -> Eop (Odivf, (Econs (e1, (Econs (e3, Enil)))))

(** val divfsimm : expr -> float32 -> expr **)

let divfsimm e n =
  match Float32.exact_inverse n with
  | Some n' ->
    Eop (Omulfs, (Econs (e, (Econs ((Eop ((Osingleconst n'), Enil)),
      Enil)))))
  | None ->
    Eop (Odivfs, (Econs (e, (Econs ((Eop ((Osingleconst n), Enil)), Enil)))))

type divfs_cases =
| Coq_divfs_case1 of float32
| Coq_divfs_default of expr

(** val divfs_match : expr -> divfs_cases **)

let divfs_match = function
| Eop (o, e) ->
  (match o with
   | Osingleconst n2 ->
     (match e with
      | Enil -> Coq_divfs_case1 n2
      | Econs (e0, e1) ->
        Coq_divfs_default (Eop ((Osingleconst n2), (Econs (e0, e1)))))
   | x -> Coq_divfs_default (Eop (x, e)))
| x -> Coq_divfs_default x

(** val divfs : expr -> expr -> expr **)

let divfs e1 e2 =
  match divfs_match e2 with
  | Coq_divfs_case1 n2 -> divfsimm e1 n2
  | Coq_divfs_default e3 -> Eop (Odivfs, (Econs (e1, (Econs (e3, Enil)))))

