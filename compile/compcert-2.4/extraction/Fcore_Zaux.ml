open BinInt
open BinNums

(** val coq_Zeven : coq_Z -> bool **)

let coq_Zeven = function
| Z0 -> true
| Zpos p ->
  (match p with
   | Coq_xO p0 -> true
   | _ -> false)
| Zneg p ->
  (match p with
   | Coq_xO p0 -> true
   | _ -> false)

type radix =
  coq_Z
  (* singleton inductive, whose constructor was Build_radix *)

(** val radix_val : radix -> coq_Z **)

let radix_val r =
  r

(** val cond_Zopp : bool -> coq_Z -> coq_Z **)

let cond_Zopp b m =
  if b then Z.opp m else m

