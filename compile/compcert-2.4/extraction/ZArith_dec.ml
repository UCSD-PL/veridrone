open BinInt
open BinNums
open Datatypes

(** val coq_Z_lt_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_lt_dec x y =
  match Z.compare x y with
  | Lt -> true
  | _ -> false

(** val coq_Z_le_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_le_dec x y =
  match Z.compare x y with
  | Gt -> false
  | _ -> true

(** val coq_Z_gt_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_gt_dec x y =
  match Z.compare x y with
  | Gt -> true
  | _ -> false

(** val coq_Z_ge_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_ge_dec x y =
  match Z.compare x y with
  | Lt -> false
  | _ -> true

(** val coq_Z_le_gt_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_le_gt_dec x y =
  coq_Z_le_dec x y

(** val coq_Z_gt_le_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_gt_le_dec x y =
  coq_Z_gt_dec x y

(** val coq_Z_ge_lt_dec : coq_Z -> coq_Z -> bool **)

let coq_Z_ge_lt_dec x y =
  coq_Z_ge_dec x y

