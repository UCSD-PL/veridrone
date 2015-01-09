open BinNums
open Datatypes
open Fappli_IEEE
open Peano

(** val big_endian : bool **)

let big_endian =
  false

(** val default_pl_64 : bool * nan_pl **)

let default_pl_64 =
  (true,
    (nat_iter (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))
      (fun x -> Coq_xO x) Coq_xH))

(** val choose_binop_pl_64 : bool -> nan_pl -> bool -> nan_pl -> bool **)

let choose_binop_pl_64 s1 pl1 s2 pl2 =
  false

(** val default_pl_32 : bool * nan_pl **)

let default_pl_32 =
  (true,
    (nat_iter (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S O)))))))))))))))))))))) (fun x -> Coq_xO x) Coq_xH))

(** val choose_binop_pl_32 : bool -> nan_pl -> bool -> nan_pl -> bool **)

let choose_binop_pl_32 s1 pl1 s2 pl2 =
  false

(** val float_of_single_preserves_sNaN : bool **)

let float_of_single_preserves_sNaN =
  false

