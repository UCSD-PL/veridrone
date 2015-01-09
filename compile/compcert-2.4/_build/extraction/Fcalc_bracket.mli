open BinInt
open BinNums
open Datatypes
open Fcore_Zaux
open Zbool

type location =
| Coq_loc_Exact
| Coq_loc_Inexact of comparison

val new_location_even : coq_Z -> coq_Z -> location -> location

val new_location_odd : coq_Z -> coq_Z -> location -> location

val new_location : coq_Z -> coq_Z -> location -> location

