open Datatypes

(** val plus : nat -> nat -> nat **)

let rec plus n m =
  match n with
  | O -> m
  | S p -> S (plus p m)

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
  | O -> m
  | S n' ->
    (match m with
     | O -> n
     | S m' -> S (max n' m'))

(** val min : nat -> nat -> nat **)

let rec min n m =
  match n with
  | O -> O
  | S n' ->
    (match m with
     | O -> O
     | S m' -> S (min n' m'))

(** val nat_iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n f x =
  match n with
  | O -> x
  | S n' -> f (nat_iter n' f x)

