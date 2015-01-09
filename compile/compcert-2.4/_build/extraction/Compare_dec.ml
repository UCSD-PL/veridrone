open Datatypes

(** val le_lt_dec : nat -> nat -> bool **)

let rec le_lt_dec n m =
  match n with
  | O -> true
  | S n0 ->
    (match m with
     | O -> false
     | S m0 -> le_lt_dec n0 m0)

(** val le_gt_dec : nat -> nat -> bool **)

let le_gt_dec n m =
  le_lt_dec n m

(** val nat_compare : nat -> nat -> comparison **)

let rec nat_compare n m =
  match n with
  | O ->
    (match m with
     | O -> Eq
     | S n0 -> Lt)
  | S n' ->
    (match m with
     | O -> Gt
     | S m' -> nat_compare n' m')

