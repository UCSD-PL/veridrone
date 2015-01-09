open AST
open Events
open Integers

type world =
| World of (ident -> eventval list -> (eventval * world) option)
   * (memory_chunk -> ident -> Int.int -> (eventval * world) option)
   * (memory_chunk -> ident -> Int.int -> eventval -> world option)

val nextworld_vload :
  world -> memory_chunk -> ident -> Int.int -> (eventval * world) option

val nextworld_vstore :
  world -> memory_chunk -> ident -> Int.int -> eventval -> world option

