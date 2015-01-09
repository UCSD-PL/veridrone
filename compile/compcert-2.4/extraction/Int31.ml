open Datatypes

(** val size : nat **)

let size =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O))))))))))))))))))))))))))))))

(** val coq_On : int **)

let coq_On = 0

(** val coq_In : int **)

let coq_In = 1

(** val sneakr : bool -> int -> int **)

let sneakr b i =
  Camlcoq.Int31.destr
    (fun a a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 ->
    Camlcoq.Int31.constr (b, a, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24,
    a25, a26, a27,
    a28))
    i

(** val sneakl : bool -> int -> int **)

let sneakl b i =
  Camlcoq.Int31.destr
    (fun d a a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 ->
    Camlcoq.Int31.constr (a, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24,
    a25, a26, a27, a28,
    b))
    i

(** val shiftr : int -> int **)

let shiftr =
  sneakr false

(** val twice : int -> int **)

let twice = Camlcoq.Int31.twice

(** val twice_plus_one : int -> int **)

let twice_plus_one = Camlcoq.Int31.twice_plus_one

(** val firstr : int -> bool **)

let firstr i =
  Camlcoq.Int31.destr
    (fun x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 d ->
    d)
    i

(** val iszero : int -> bool **)

let iszero i =
  Camlcoq.Int31.destr
    (fun a a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 ->
    match a with
    | false ->
      (match a0 with
       | false ->
         (match a1 with
          | false ->
            (match a2 with
             | false ->
               (match a3 with
                | false ->
                  (match a4 with
                   | false ->
                     (match a5 with
                      | false ->
                        (match a6 with
                         | false ->
                           (match a7 with
                            | false ->
                              (match a8 with
                               | false ->
                                 (match a9 with
                                  | false ->
                                    (match a10 with
                                     | false ->
                                       (match a11 with
                                        | false ->
                                          (match a12 with
                                           | false ->
                                             (match a13 with
                                              | false ->
                                                (match a14 with
                                                 | false ->
                                                   (match a15 with
                                                    | false ->
                                                      (match a16 with
                                                       | false ->
                                                         (match a17 with
                                                          | false ->
                                                            (match a18 with
                                                             | false ->
                                                               (match a19 with
                                                                | false ->
                                                                  (match a20 with
                                                                   | false ->
                                                                    (match a21 with
                                                                    | false ->
                                                                    (match a22 with
                                                                    | false ->
                                                                    (match a23 with
                                                                    | false ->
                                                                    (match a24 with
                                                                    | false ->
                                                                    (match a25 with
                                                                    | false ->
                                                                    (match a26 with
                                                                    | false ->
                                                                    (match a27 with
                                                                    | false ->
                                                                    (match a28 with
                                                                    | false ->
                                                                    (match a29 with
                                                                    | false ->
                                                                    true
                                                                    | true ->
                                                                    false)
                                                                    | true ->
                                                                    false)
                                                                    | true ->
                                                                    false)
                                                                    | true ->
                                                                    false)
                                                                    | true ->
                                                                    false)
                                                                    | true ->
                                                                    false)
                                                                    | true ->
                                                                    false)
                                                                    | true ->
                                                                    false)
                                                                    | true ->
                                                                    false)
                                                                   | true ->
                                                                    false)
                                                                | true ->
                                                                  false)
                                                             | true -> false)
                                                          | true -> false)
                                                       | true -> false)
                                                    | true -> false)
                                                 | true -> false)
                                              | true -> false)
                                           | true -> false)
                                        | true -> false)
                                     | true -> false)
                                  | true -> false)
                               | true -> false)
                            | true -> false)
                         | true -> false)
                      | true -> false)
                   | true -> false)
                | true -> false)
             | true -> false)
          | true -> false)
       | true -> false)
    | true -> false)
    i

(** val recr_aux :
    nat -> 'a1 -> (bool -> int -> 'a1 -> 'a1) -> int -> 'a1 **)

let rec recr_aux n case0 caserec i =
  match n with
  | O -> case0
  | S next ->
    if iszero i
    then case0
    else let si = shiftr i in
         caserec (firstr i) si (recr_aux next case0 caserec si)

(** val recr : 'a1 -> (bool -> int -> 'a1 -> 'a1) -> int -> 'a1 **)

let recr case0 caserec i =
  recr_aux size case0 caserec i

(** val incr : int -> int **)

let incr =
  recr coq_In (fun b si rec0 ->
    match b with
    | false -> sneakl true si
    | true -> sneakl false rec0)

(** val compare31 : int -> int -> comparison **)

let compare31 = Camlcoq.Int31.compare

(** val iter_int31 : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let iter_int31 i f =
  recr (fun x -> x) (fun b si rec0 x ->
    match b with
    | false -> rec0 (rec0 x)
    | true -> f (rec0 (rec0 x))) i

