open BinInt
open BinNums

val coq_Zeven : coq_Z -> bool

type radix =
  coq_Z
  (* singleton inductive, whose constructor was Build_radix *)

val radix_val : radix -> coq_Z

val cond_Zopp : bool -> coq_Z -> coq_Z

