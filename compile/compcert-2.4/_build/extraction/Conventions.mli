open AST
open Conventions1
open List0
open Locations

val parameter_of_argument : loc -> loc

val loc_parameters : signature -> loc list

val tailcall_is_possible : signature -> bool

