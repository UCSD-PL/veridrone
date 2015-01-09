open BinInt
open BinNums
open Fappli_IEEE
open Zbool

val join_bits : coq_Z -> coq_Z -> bool -> coq_Z -> coq_Z -> coq_Z

val split_bits : coq_Z -> coq_Z -> coq_Z -> (bool * coq_Z) * coq_Z

val bits_of_binary_float : coq_Z -> coq_Z -> binary_float -> coq_Z

val binary_float_of_bits_aux : coq_Z -> coq_Z -> coq_Z -> full_float

val binary_float_of_bits : coq_Z -> coq_Z -> coq_Z -> binary_float

type binary32 = binary_float

val b32_opp :
  (bool -> nan_pl -> bool * nan_pl) -> binary_float -> binary_float

val b32_plus :
  (binary_float -> binary_float -> bool * nan_pl) -> mode -> binary_float ->
  binary_float -> binary_float

val b32_minus :
  (binary_float -> binary_float -> bool * nan_pl) -> mode -> binary_float ->
  binary_float -> binary_float

val b32_mult :
  (binary_float -> binary_float -> bool * nan_pl) -> mode -> binary_float ->
  binary_float -> binary_float

val b32_div :
  (binary_float -> binary_float -> bool * nan_pl) -> mode -> binary_float ->
  binary_float -> binary_float

val b32_of_bits : coq_Z -> binary32

val bits_of_b32 : binary32 -> coq_Z

type binary64 = binary_float

val b64_opp :
  (bool -> nan_pl -> bool * nan_pl) -> binary_float -> binary_float

val b64_plus :
  (binary_float -> binary_float -> bool * nan_pl) -> mode -> binary_float ->
  binary_float -> binary_float

val b64_minus :
  (binary_float -> binary_float -> bool * nan_pl) -> mode -> binary_float ->
  binary_float -> binary_float

val b64_mult :
  (binary_float -> binary_float -> bool * nan_pl) -> mode -> binary_float ->
  binary_float -> binary_float

val b64_div :
  (binary_float -> binary_float -> bool * nan_pl) -> mode -> binary_float ->
  binary_float -> binary_float

val b64_of_bits : coq_Z -> binary64

val bits_of_b64 : binary64 -> coq_Z

