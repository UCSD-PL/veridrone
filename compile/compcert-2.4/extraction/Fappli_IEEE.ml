open BinInt
open BinNums
open BinPos
open Bool
open Datatypes
open Fcalc_bracket
open Fcalc_round
open Fcore_FLT
open Fcore_Zaux
open Fcore_digits
open Zpower

type full_float =
| F754_zero of bool
| F754_infinity of bool
| F754_nan of bool * positive
| F754_finite of bool * positive * coq_Z

type nan_pl = positive

type binary_float =
| B754_zero of bool
| B754_infinity of bool
| B754_nan of bool * nan_pl
| B754_finite of bool * positive * coq_Z

(** val coq_FF2B : coq_Z -> coq_Z -> full_float -> binary_float **)

let coq_FF2B prec emax = function
| F754_zero s -> B754_zero s
| F754_infinity s -> B754_infinity s
| F754_nan (b, pl) -> B754_nan (b, pl)
| F754_finite (s, m, e) -> B754_finite (s, m, e)

(** val radix2 : radix **)

let radix2 =
  Zpos (Coq_xO Coq_xH)

(** val coq_Bopp :
    coq_Z -> coq_Z -> (bool -> nan_pl -> bool * nan_pl) -> binary_float ->
    binary_float **)

let coq_Bopp prec emax opp_nan = function
| B754_zero sx -> B754_zero (negb sx)
| B754_infinity sx -> B754_infinity (negb sx)
| B754_nan (sx, plx) ->
  let (sres, plres) = opp_nan sx plx in B754_nan (sres, plres)
| B754_finite (sx, mx, ex) -> B754_finite ((negb sx), mx, ex)

type shr_record = { shr_m : coq_Z; shr_r : bool; shr_s : bool }

(** val shr_m : shr_record -> coq_Z **)

let shr_m x = x.shr_m

(** val shr_1 : shr_record -> shr_record **)

let shr_1 mrs =
  let { shr_m = m; shr_r = r; shr_s = s } = mrs in
  let s0 = (||) r s in
  (match m with
   | Z0 -> { shr_m = Z0; shr_r = false; shr_s = s0 }
   | Zpos p0 ->
     (match p0 with
      | Coq_xI p -> { shr_m = (Zpos p); shr_r = true; shr_s = s0 }
      | Coq_xO p -> { shr_m = (Zpos p); shr_r = false; shr_s = s0 }
      | Coq_xH -> { shr_m = Z0; shr_r = true; shr_s = s0 })
   | Zneg p0 ->
     (match p0 with
      | Coq_xI p -> { shr_m = (Zneg p); shr_r = true; shr_s = s0 }
      | Coq_xO p -> { shr_m = (Zneg p); shr_r = false; shr_s = s0 }
      | Coq_xH -> { shr_m = Z0; shr_r = true; shr_s = s0 }))

(** val loc_of_shr_record : shr_record -> location **)

let loc_of_shr_record mrs =
  let { shr_m = shr_m0; shr_r = shr_r0; shr_s = shr_s0 } = mrs in
  if shr_r0
  then if shr_s0 then Coq_loc_Inexact Gt else Coq_loc_Inexact Eq
  else if shr_s0 then Coq_loc_Inexact Lt else Coq_loc_Exact

(** val shr_record_of_loc : coq_Z -> location -> shr_record **)

let shr_record_of_loc m = function
| Coq_loc_Exact -> { shr_m = m; shr_r = false; shr_s = false }
| Coq_loc_Inexact c ->
  (match c with
   | Eq -> { shr_m = m; shr_r = true; shr_s = false }
   | Lt -> { shr_m = m; shr_r = false; shr_s = true }
   | Gt -> { shr_m = m; shr_r = true; shr_s = true })

(** val shr : shr_record -> coq_Z -> coq_Z -> shr_record * coq_Z **)

let shr mrs e n = match n with
| Zpos p -> ((Pos.iter p shr_1 mrs), (Z.add e n))
| _ -> (mrs, e)

(** val coq_Zdigits2 : coq_Z -> coq_Z **)

let coq_Zdigits2 m = match m with
| Z0 -> m
| Zpos p -> Z.of_nat (S (digits2_Pnat p))
| Zneg p -> Z.of_nat (S (digits2_Pnat p))

(** val shr_fexp :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> location -> shr_record * coq_Z **)

let shr_fexp prec emax =
  let emin = Z.sub (Z.sub (Zpos (Coq_xI Coq_xH)) emax) prec in
  let fexp = coq_FLT_exp emin prec in
  (fun m e l ->
  shr (shr_record_of_loc m l) e (Z.sub (fexp (Z.add (coq_Zdigits2 m) e)) e))

type mode =
| Coq_mode_NE
| Coq_mode_ZR
| Coq_mode_DN
| Coq_mode_UP
| Coq_mode_NA

(** val choice_mode : mode -> bool -> coq_Z -> location -> coq_Z **)

let choice_mode m sx mx lx =
  match m with
  | Coq_mode_NE -> cond_incr (round_N (negb (coq_Zeven mx)) lx) mx
  | Coq_mode_ZR -> mx
  | Coq_mode_DN -> cond_incr (round_sign_DN sx lx) mx
  | Coq_mode_UP -> cond_incr (round_sign_UP sx lx) mx
  | Coq_mode_NA -> cond_incr (round_N true lx) mx

(** val overflow_to_inf : mode -> bool -> bool **)

let overflow_to_inf m s =
  match m with
  | Coq_mode_ZR -> false
  | Coq_mode_DN -> s
  | Coq_mode_UP -> negb s
  | _ -> true

(** val binary_overflow : coq_Z -> coq_Z -> mode -> bool -> full_float **)

let binary_overflow prec emax m s =
  if overflow_to_inf m s
  then F754_infinity s
  else F754_finite (s,
         (match Z.sub (Z.pow (Zpos (Coq_xO Coq_xH)) prec) (Zpos Coq_xH) with
          | Zpos p -> p
          | _ -> Coq_xH), (Z.sub emax prec))

(** val binary_round_aux :
    coq_Z -> coq_Z -> mode -> bool -> positive -> coq_Z -> location ->
    full_float **)

let binary_round_aux prec emax mode0 sx mx ex lx =
  let (mrs', e') = shr_fexp prec emax (Zpos mx) ex lx in
  let (mrs'', e'') =
    shr_fexp prec emax
      (choice_mode mode0 sx mrs'.shr_m (loc_of_shr_record mrs')) e'
      Coq_loc_Exact
  in
  (match mrs''.shr_m with
   | Z0 -> F754_zero sx
   | Zpos m ->
     if Z.leb e'' (Z.sub emax prec)
     then F754_finite (sx, m, e'')
     else binary_overflow prec emax mode0 sx
   | Zneg p -> F754_nan (false, Coq_xH))

(** val coq_Bmult :
    coq_Z -> coq_Z -> (binary_float -> binary_float -> bool * nan_pl) -> mode
    -> binary_float -> binary_float -> binary_float **)

let coq_Bmult prec emax mult_nan m x y =
  match x with
  | B754_zero sx ->
    let f = fun pl -> B754_nan ((fst pl), (snd pl)) in
    (match y with
     | B754_zero sy -> B754_zero (xorb sx sy)
     | B754_finite (sy, m0, e) -> B754_zero (xorb sx sy)
     | _ -> f (mult_nan x y))
  | B754_infinity sx ->
    let f = fun pl -> B754_nan ((fst pl), (snd pl)) in
    (match y with
     | B754_infinity sy -> B754_infinity (xorb sx sy)
     | B754_finite (sy, m0, e) -> B754_infinity (xorb sx sy)
     | _ -> f (mult_nan x y))
  | B754_nan (b, n) -> let pl = mult_nan x y in B754_nan ((fst pl), (snd pl))
  | B754_finite (sx, mx, ex) ->
    let f = fun pl -> B754_nan ((fst pl), (snd pl)) in
    (match y with
     | B754_zero sy -> B754_zero (xorb sx sy)
     | B754_infinity sy -> B754_infinity (xorb sx sy)
     | B754_nan (b, n) -> f (mult_nan x y)
     | B754_finite (sy, my, ey) ->
       coq_FF2B prec emax
         (binary_round_aux prec emax m (xorb sx sy) (Pos.mul mx my)
           (Z.add ex ey) Coq_loc_Exact))

(** val shl_align : positive -> coq_Z -> coq_Z -> positive * coq_Z **)

let shl_align mx ex ex' =
  match Z.sub ex' ex with
  | Zneg d -> ((shift_pos d mx), ex')
  | _ -> (mx, ex)

(** val shl_align_fexp :
    coq_Z -> coq_Z -> positive -> coq_Z -> positive * coq_Z **)

let shl_align_fexp prec emax =
  let emin = Z.sub (Z.sub (Zpos (Coq_xI Coq_xH)) emax) prec in
  let fexp = coq_FLT_exp emin prec in
  (fun mx ex ->
  shl_align mx ex (fexp (Z.add (Z.of_nat (S (digits2_Pnat mx))) ex)))

(** val binary_round :
    coq_Z -> coq_Z -> mode -> bool -> positive -> coq_Z -> full_float **)

let binary_round prec emax m sx mx ex =
  let (mz, ez) = shl_align_fexp prec emax mx ex in
  binary_round_aux prec emax m sx mz ez Coq_loc_Exact

(** val binary_normalize :
    coq_Z -> coq_Z -> mode -> coq_Z -> coq_Z -> bool -> binary_float **)

let binary_normalize prec emax mode0 m e szero =
  match m with
  | Z0 -> B754_zero szero
  | Zpos m0 -> coq_FF2B prec emax (binary_round prec emax mode0 false m0 e)
  | Zneg m0 -> coq_FF2B prec emax (binary_round prec emax mode0 true m0 e)

(** val coq_Bplus :
    coq_Z -> coq_Z -> (binary_float -> binary_float -> bool * nan_pl) -> mode
    -> binary_float -> binary_float -> binary_float **)

let coq_Bplus prec emax plus_nan m x y =
  match x with
  | B754_zero sx ->
    let f = fun pl -> B754_nan ((fst pl), (snd pl)) in
    (match y with
     | B754_zero sy ->
       if eqb sx sy
       then x
       else (match m with
             | Coq_mode_DN -> B754_zero true
             | _ -> B754_zero false)
     | B754_nan (b, n) -> f (plus_nan x y)
     | _ -> y)
  | B754_infinity sx ->
    let f = fun pl -> B754_nan ((fst pl), (snd pl)) in
    (match y with
     | B754_infinity sy -> if eqb sx sy then x else f (plus_nan x y)
     | B754_nan (b, n) -> f (plus_nan x y)
     | _ -> x)
  | B754_nan (b, n) -> let pl = plus_nan x y in B754_nan ((fst pl), (snd pl))
  | B754_finite (sx, mx, ex) ->
    let f = fun pl -> B754_nan ((fst pl), (snd pl)) in
    (match y with
     | B754_zero b -> x
     | B754_infinity b -> y
     | B754_nan (b, n) -> f (plus_nan x y)
     | B754_finite (sy, my, ey) ->
       let ez = Z.min ex ey in
       binary_normalize prec emax m
         (Z.add (cond_Zopp sx (Zpos (fst (shl_align mx ex ez))))
           (cond_Zopp sy (Zpos (fst (shl_align my ey ez))))) ez
         (match m with
          | Coq_mode_DN -> true
          | _ -> false))

(** val coq_Bminus :
    coq_Z -> coq_Z -> (binary_float -> binary_float -> bool * nan_pl) -> mode
    -> binary_float -> binary_float -> binary_float **)

let coq_Bminus prec emax minus_nan m x y =
  coq_Bplus prec emax minus_nan m x
    (coq_Bopp prec emax (fun x0 x1 -> (x0, x1)) y)

(** val coq_Fdiv_core_binary :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> (coq_Z * coq_Z) * location **)

let coq_Fdiv_core_binary prec m1 e1 m2 e2 =
  let d1 = coq_Zdigits2 m1 in
  let d2 = coq_Zdigits2 m2 in
  let e = Z.sub e1 e2 in
  (match Z.sub (Z.add d2 prec) d1 with
   | Zpos p ->
     let m = Z.mul m1 (Z.pow_pos (Zpos (Coq_xO Coq_xH)) p) in
     let e' = Z.add e (Zneg p) in
     let (q, r) = Z.div_eucl m m2 in
     ((q, e'), (new_location m2 r Coq_loc_Exact))
   | _ ->
     let (q, r) = Z.div_eucl m1 m2 in
     ((q, e), (new_location m2 r Coq_loc_Exact)))

(** val coq_Bdiv :
    coq_Z -> coq_Z -> (binary_float -> binary_float -> bool * nan_pl) -> mode
    -> binary_float -> binary_float -> binary_float **)

let coq_Bdiv prec emax div_nan m x y =
  match x with
  | B754_zero sx ->
    let f = fun pl -> B754_nan ((fst pl), (snd pl)) in
    (match y with
     | B754_infinity sy -> B754_zero (xorb sx sy)
     | B754_finite (sy, m0, e) -> B754_zero (xorb sx sy)
     | _ -> f (div_nan x y))
  | B754_infinity sx ->
    let f = fun pl -> B754_nan ((fst pl), (snd pl)) in
    (match y with
     | B754_zero sy -> B754_infinity (xorb sx sy)
     | B754_finite (sy, m0, e) -> B754_infinity (xorb sx sy)
     | _ -> f (div_nan x y))
  | B754_nan (b, n) -> let pl = div_nan x y in B754_nan ((fst pl), (snd pl))
  | B754_finite (sx, mx, ex) ->
    let f = fun pl -> B754_nan ((fst pl), (snd pl)) in
    (match y with
     | B754_zero sy -> B754_infinity (xorb sx sy)
     | B754_infinity sy -> B754_zero (xorb sx sy)
     | B754_nan (b, n) -> f (div_nan x y)
     | B754_finite (sy, my, ey) ->
       coq_FF2B prec emax
         (let (p, lz) = coq_Fdiv_core_binary prec (Zpos mx) ex (Zpos my) ey
          in
          let (mz, ez) = p in
          (match mz with
           | Zpos mz0 -> binary_round_aux prec emax m (xorb sx sy) mz0 ez lz
           | _ -> F754_nan (false, Coq_xH))))

