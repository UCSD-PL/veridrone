open BinInt
open BinNums
open BinPos
open Datatypes
open Fappli_IEEE
open Fappli_IEEE_bits
open Fcore_Zaux
open ZArith_dec

val coq_Beq_dec : coq_Z -> coq_Z -> binary_float -> binary_float -> bool

val coq_Bcompare :
  coq_Z -> coq_Z -> binary_float -> binary_float -> comparison option

val coq_Babs :
  coq_Z -> coq_Z -> (bool -> nan_pl -> bool * nan_pl) -> binary_float ->
  binary_float

val coq_BofZ : coq_Z -> coq_Z -> coq_Z -> binary_float

val coq_ZofB : coq_Z -> coq_Z -> binary_float -> coq_Z option

val coq_ZofB_range :
  coq_Z -> coq_Z -> binary_float -> coq_Z -> coq_Z -> coq_Z option

val coq_Bexact_inverse_mantissa : coq_Z -> positive

val coq_Bexact_inverse :
  coq_Z -> coq_Z -> binary_float -> binary_float option

val coq_Bconv :
  coq_Z -> coq_Z -> coq_Z -> coq_Z -> (bool -> nan_pl -> bool * nan_pl) ->
  mode -> binary_float -> binary_float

val b32_abs : (bool -> nan_pl -> bool * nan_pl) -> binary32 -> binary32

val b32_eq_dec : binary32 -> binary32 -> bool

val b32_compare : binary32 -> binary32 -> comparison option

val b32_of_Z : coq_Z -> binary32

val b32_to_Z_range : binary32 -> coq_Z -> coq_Z -> coq_Z option

val b32_exact_inverse : binary32 -> binary32 option

val b64_abs : (bool -> nan_pl -> bool * nan_pl) -> binary64 -> binary64

val b64_eq_dec : binary64 -> binary64 -> bool

val b64_compare : binary64 -> binary64 -> comparison option

val b64_of_Z : coq_Z -> binary64

val b64_to_Z_range : binary64 -> coq_Z -> coq_Z -> coq_Z option

val b64_exact_inverse : binary64 -> binary64 option

val b64_of_b32 :
  (bool -> nan_pl -> bool * nan_pl) -> mode -> binary32 -> binary64

val b32_of_b64 :
  (bool -> nan_pl -> bool * nan_pl) -> mode -> binary64 -> binary32

