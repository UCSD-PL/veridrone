open AST
open Events
open Integers

type world =
| World of (ident -> eventval list -> (eventval * world) option)
   * (memory_chunk -> ident -> Int.int -> (eventval * world) option)
   * (memory_chunk -> ident -> Int.int -> eventval -> world option)

(** val nextworld_vload :
    world -> memory_chunk -> ident -> Int.int -> (eventval * world) option **)

let nextworld_vload w chunk id ofs =
  let World (io, vl, vs) = w in vl chunk id ofs

(** val nextworld_vstore :
    world -> memory_chunk -> ident -> Int.int -> eventval -> world option **)

let nextworld_vstore w chunk id ofs v =
  let World (io, vl, vs) = w in vs chunk id ofs v

