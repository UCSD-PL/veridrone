open Datatypes

val size : nat

val coq_On : int

val coq_In : int

val sneakr : bool -> int -> int

val sneakl : bool -> int -> int

val shiftr : int -> int

val twice : int -> int

val twice_plus_one : int -> int

val firstr : int -> bool

val iszero : int -> bool

val recr_aux : nat -> 'a1 -> (bool -> int -> 'a1 -> 'a1) -> int -> 'a1

val recr : 'a1 -> (bool -> int -> 'a1 -> 'a1) -> int -> 'a1

val incr : int -> int

val compare31 : int -> int -> comparison

val iter_int31 : int -> ('a1 -> 'a1) -> 'a1 -> 'a1

