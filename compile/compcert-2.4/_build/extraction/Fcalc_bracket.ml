open BinInt
open BinNums
open Datatypes
open Fcore_Zaux
open Zbool

type location =
| Coq_loc_Exact
| Coq_loc_Inexact of comparison

(** val new_location_even : coq_Z -> coq_Z -> location -> location **)

let new_location_even nb_steps k l =
  if coq_Zeq_bool k Z0
  then (match l with
        | Coq_loc_Exact -> l
        | Coq_loc_Inexact c -> Coq_loc_Inexact Lt)
  else Coq_loc_Inexact
         (match Z.compare (Z.mul (Zpos (Coq_xO Coq_xH)) k) nb_steps with
          | Eq ->
            (match l with
             | Coq_loc_Exact -> Eq
             | Coq_loc_Inexact c -> Gt)
          | x -> x)

(** val new_location_odd : coq_Z -> coq_Z -> location -> location **)

let new_location_odd nb_steps k l =
  if coq_Zeq_bool k Z0
  then (match l with
        | Coq_loc_Exact -> l
        | Coq_loc_Inexact c -> Coq_loc_Inexact Lt)
  else Coq_loc_Inexact
         (match Z.compare
                  (Z.add (Z.mul (Zpos (Coq_xO Coq_xH)) k) (Zpos Coq_xH))
                  nb_steps with
          | Eq ->
            (match l with
             | Coq_loc_Exact -> Lt
             | Coq_loc_Inexact l0 -> l0)
          | x -> x)

(** val new_location : coq_Z -> coq_Z -> location -> location **)

let new_location nb_steps =
  if coq_Zeven nb_steps
  then new_location_even nb_steps
  else new_location_odd nb_steps

