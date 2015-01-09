open AST
open Conventions1
open List0
open Locations

(** val parameter_of_argument : loc -> loc **)

let parameter_of_argument l = match l with
| R r -> l
| S (sl, n, ty) ->
  (match sl with
   | Outgoing -> S (Incoming, n, ty)
   | _ -> l)

(** val loc_parameters : signature -> loc list **)

let loc_parameters s =
  map parameter_of_argument (loc_arguments s)

(** val tailcall_is_possible : signature -> bool **)

let tailcall_is_possible sg =
  let rec tcisp = function
  | [] -> true
  | l0 :: l' ->
    (match l0 with
     | R r -> tcisp l'
     | S (sl, pos, ty) -> false)
  in tcisp (loc_arguments sg)

