open BinInt
open BinNums
open BinPos
open Datatypes
open Fappli_IEEE
open Fappli_IEEE_bits
open Fcore_Zaux
open ZArith_dec

(** val coq_Beq_dec :
    coq_Z -> coq_Z -> binary_float -> binary_float -> bool **)

let coq_Beq_dec prec emax f1 f2 =
  match f1 with
  | B754_zero b ->
    (match f2 with
     | B754_zero b0 ->
       if b then if b0 then true else false else if b0 then false else true
     | _ -> false)
  | B754_infinity b ->
    (match f2 with
     | B754_infinity b0 ->
       if b then if b0 then true else false else if b0 then false else true
     | _ -> false)
  | B754_nan (b, n) ->
    (match f2 with
     | B754_nan (b0, n0) ->
       if b
       then if b0 then Pos.eq_dec n n0 else false
       else if b0 then false else Pos.eq_dec n n0
     | _ -> false)
  | B754_finite (b, m, e) ->
    (match f2 with
     | B754_finite (b0, m0, e1) ->
       if b
       then if b0
            then let s = Pos.eq_dec m m0 in
                 if s then Z.eq_dec e e1 else false
            else false
       else if b0
            then false
            else let s = Pos.eq_dec m m0 in
                 if s then Z.eq_dec e e1 else false
     | _ -> false)

(** val coq_Bcompare :
    coq_Z -> coq_Z -> binary_float -> binary_float -> comparison option **)

let coq_Bcompare prec emax f1 f2 =
  match f1 with
  | B754_zero b ->
    (match f2 with
     | B754_zero b0 -> Some Eq
     | B754_infinity b0 -> if b0 then Some Gt else Some Lt
     | B754_nan (b0, n) -> None
     | B754_finite (b0, m, e) -> if b0 then Some Gt else Some Lt)
  | B754_infinity b ->
    if b
    then (match f2 with
          | B754_infinity b0 -> if b0 then Some Eq else Some Lt
          | B754_nan (b0, n) -> None
          | _ -> Some Lt)
    else (match f2 with
          | B754_infinity b0 -> if b0 then Some Gt else Some Eq
          | B754_nan (b0, n) -> None
          | _ -> Some Gt)
  | B754_nan (b, n) -> None
  | B754_finite (s1, m1, e1) ->
    if s1
    then (match f2 with
          | B754_zero b -> Some Lt
          | B754_infinity b -> if b then Some Gt else Some Lt
          | B754_nan (b, n) -> None
          | B754_finite (s2, m2, e2) ->
            if s1
            then if s2
                 then (match Z.compare e1 e2 with
                       | Eq -> Some (coq_CompOpp (Pos.compare_cont m1 m2 Eq))
                       | Lt -> Some Gt
                       | Gt -> Some Lt)
                 else Some Lt
            else if s2
                 then Some Gt
                 else (match Z.compare e1 e2 with
                       | Eq -> Some (Pos.compare_cont m1 m2 Eq)
                       | x -> Some x))
    else (match f2 with
          | B754_zero b -> Some Gt
          | B754_infinity b -> if b then Some Gt else Some Lt
          | B754_nan (b, n) -> None
          | B754_finite (s2, m2, e2) ->
            if s1
            then if s2
                 then (match Z.compare e1 e2 with
                       | Eq -> Some (coq_CompOpp (Pos.compare_cont m1 m2 Eq))
                       | Lt -> Some Gt
                       | Gt -> Some Lt)
                 else Some Lt
            else if s2
                 then Some Gt
                 else (match Z.compare e1 e2 with
                       | Eq -> Some (Pos.compare_cont m1 m2 Eq)
                       | x -> Some x))

(** val coq_Babs :
    coq_Z -> coq_Z -> (bool -> nan_pl -> bool * nan_pl) -> binary_float ->
    binary_float **)

let coq_Babs prec emax abs_nan = function
| B754_zero sx -> B754_zero false
| B754_infinity sx -> B754_infinity false
| B754_nan (sx, plx) ->
  let (sres, plres) = abs_nan sx plx in B754_nan (sres, plres)
| B754_finite (sx, mx, ex) -> B754_finite (false, mx, ex)

(** val coq_BofZ : coq_Z -> coq_Z -> coq_Z -> binary_float **)

let coq_BofZ prec emax n =
  binary_normalize prec emax Coq_mode_NE n Z0 false

(** val coq_ZofB : coq_Z -> coq_Z -> binary_float -> coq_Z option **)

let coq_ZofB prec emax = function
| B754_zero b -> Some Z0
| B754_finite (s, m, e0) ->
  (match e0 with
   | Z0 -> Some (cond_Zopp s (Zpos m))
   | Zpos e ->
     Some (Z.mul (cond_Zopp s (Zpos m)) (Z.pow_pos (radix_val radix2) e))
   | Zneg e ->
     Some (cond_Zopp s (Z.div (Zpos m) (Z.pow_pos (radix_val radix2) e))))
| _ -> None

(** val coq_ZofB_range :
    coq_Z -> coq_Z -> binary_float -> coq_Z -> coq_Z -> coq_Z option **)

let coq_ZofB_range prec emax f zmin zmax =
  match coq_ZofB prec emax f with
  | Some z -> if (&&) (Z.leb zmin z) (Z.leb z zmax) then Some z else None
  | None -> None

(** val coq_Bexact_inverse_mantissa : coq_Z -> positive **)

let coq_Bexact_inverse_mantissa prec =
  Z.iter (Z.sub prec (Zpos Coq_xH)) (fun x -> Coq_xO x) Coq_xH

(** val coq_Bexact_inverse :
    coq_Z -> coq_Z -> binary_float -> binary_float option **)

let coq_Bexact_inverse prec emax =
  let emin = Z.sub (Z.sub (Zpos (Coq_xI Coq_xH)) emax) prec in
  (fun f ->
  match f with
  | B754_finite (s, m, e) ->
    if Pos.eq_dec m (coq_Bexact_inverse_mantissa prec)
    then let e' =
           Z.sub (Z.opp e)
             (Z.mul (Z.sub prec (Zpos Coq_xH)) (Zpos (Coq_xO Coq_xH)))
         in
         if coq_Z_le_dec emin e'
         then if coq_Z_le_dec e' emax
              then Some (B754_finite (s, m, e'))
              else None
         else None
    else None
  | x -> None)

(** val coq_Bconv :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> (bool -> nan_pl -> bool * nan_pl) ->
    mode -> binary_float -> binary_float **)

let coq_Bconv prec1 emax1 prec2 emax2 conv_nan md = function
| B754_nan (s, pl) -> let (s0, pl0) = conv_nan s pl in B754_nan (s0, pl0)
| B754_finite (s, m, e) ->
  binary_normalize prec2 emax2 md (cond_Zopp s (Zpos m)) e s
| x -> x

(** val b32_abs :
    (bool -> nan_pl -> bool * nan_pl) -> binary32 -> binary32 **)

let b32_abs =
  coq_Babs (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))) (Zpos (Coq_xO
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))

(** val b32_eq_dec : binary32 -> binary32 -> bool **)

let b32_eq_dec =
  coq_Beq_dec (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))) (Zpos (Coq_xO
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))

(** val b32_compare : binary32 -> binary32 -> comparison option **)

let b32_compare =
  coq_Bcompare (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))) (Zpos
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))

(** val b32_of_Z : coq_Z -> binary32 **)

let b32_of_Z =
  coq_BofZ (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))) (Zpos (Coq_xO
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))

(** val b32_to_Z_range : binary32 -> coq_Z -> coq_Z -> coq_Z option **)

let b32_to_Z_range =
  coq_ZofB_range (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))) (Zpos
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))

(** val b32_exact_inverse : binary32 -> binary32 option **)

let b32_exact_inverse =
  coq_Bexact_inverse (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))) (Zpos
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))

(** val b64_abs :
    (bool -> nan_pl -> bool * nan_pl) -> binary64 -> binary64 **)

let b64_abs =
  coq_Babs (Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))) (Zpos
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    (Coq_xO Coq_xH)))))))))))

(** val b64_eq_dec : binary64 -> binary64 -> bool **)

let b64_eq_dec =
  coq_Beq_dec (Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
    (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    (Coq_xO (Coq_xO Coq_xH)))))))))))

(** val b64_compare : binary64 -> binary64 -> comparison option **)

let b64_compare =
  coq_Bcompare (Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
    (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    (Coq_xO (Coq_xO Coq_xH)))))))))))

(** val b64_of_Z : coq_Z -> binary64 **)

let b64_of_Z =
  coq_BofZ (Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))) (Zpos
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    (Coq_xO Coq_xH)))))))))))

(** val b64_to_Z_range : binary64 -> coq_Z -> coq_Z -> coq_Z option **)

let b64_to_Z_range =
  coq_ZofB_range (Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
    (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    (Coq_xO (Coq_xO Coq_xH)))))))))))

(** val b64_exact_inverse : binary64 -> binary64 option **)

let b64_exact_inverse =
  coq_Bexact_inverse (Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
    Coq_xH)))))) (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))))

(** val b64_of_b32 :
    (bool -> nan_pl -> bool * nan_pl) -> mode -> binary32 -> binary64 **)

let b64_of_b32 =
  coq_Bconv (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))) (Zpos (Coq_xO
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))) (Zpos
    (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))) (Zpos (Coq_xO
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    Coq_xH)))))))))))

(** val b32_of_b64 :
    (bool -> nan_pl -> bool * nan_pl) -> mode -> binary64 -> binary32 **)

let b32_of_b64 =
  coq_Bconv (Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))) (Zpos
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    (Coq_xO Coq_xH))))))))))) (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI
    Coq_xH))))) (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    Coq_xH))))))))

