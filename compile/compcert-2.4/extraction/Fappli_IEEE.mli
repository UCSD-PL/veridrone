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

val coq_FF2B : coq_Z -> coq_Z -> full_float -> binary_float

val radix2 : radix

val coq_Bopp :
  coq_Z -> coq_Z -> (bool -> nan_pl -> bool * nan_pl) -> binary_float ->
  binary_float

type shr_record = { shr_m : coq_Z; shr_r : bool; shr_s : bool }

val shr_m : shr_record -> coq_Z

val shr_1 : shr_record -> shr_record

val loc_of_shr_record : shr_record -> location

val shr_record_of_loc : coq_Z -> location -> shr_record

val shr : shr_record -> coq_Z -> coq_Z -> shr_record * coq_Z

val coq_Zdigits2 : coq_Z -> coq_Z

val shr_fexp :
  coq_Z -> coq_Z -> coq_Z -> coq_Z -> location -> shr_record * coq_Z

type mode =
| Coq_mode_NE
| Coq_mode_ZR
| Coq_mode_DN
| Coq_mode_UP
| Coq_mode_NA

val choice_mode : mode -> bool -> coq_Z -> location -> coq_Z

val overflow_to_inf : mode -> bool -> bool

val binary_overflow : coq_Z -> coq_Z -> mode -> bool -> full_float

val binary_round_aux :
  coq_Z -> coq_Z -> mode -> bool -> positive -> coq_Z -> location ->
  full_float

val coq_Bmult :
  coq_Z -> coq_Z -> (binary_float -> binary_float -> bool * nan_pl) -> mode
  -> binary_float -> binary_float -> binary_float

val shl_align : positive -> coq_Z -> coq_Z -> positive * coq_Z

val shl_align_fexp : coq_Z -> coq_Z -> positive -> coq_Z -> positive * coq_Z

val binary_round :
  coq_Z -> coq_Z -> mode -> bool -> positive -> coq_Z -> full_float

val binary_normalize :
  coq_Z -> coq_Z -> mode -> coq_Z -> coq_Z -> bool -> binary_float

val coq_Bplus :
  coq_Z -> coq_Z -> (binary_float -> binary_float -> bool * nan_pl) -> mode
  -> binary_float -> binary_float -> binary_float

val coq_Bminus :
  coq_Z -> coq_Z -> (binary_float -> binary_float -> bool * nan_pl) -> mode
  -> binary_float -> binary_float -> binary_float

val coq_Fdiv_core_binary :
  coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> (coq_Z * coq_Z) * location

val coq_Bdiv :
  coq_Z -> coq_Z -> (binary_float -> binary_float -> bool * nan_pl) -> mode
  -> binary_float -> binary_float -> binary_float

