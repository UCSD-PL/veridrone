open Datatypes

(** val beq_nat : nat -> nat -> bool **)

let rec beq_nat n m =
  match n with
  | O ->
    (match m with
     | O -> true
     | S n0 -> false)
  | S n1 ->
    (match m with
     | O -> false
     | S m1 -> beq_nat n1 m1)

