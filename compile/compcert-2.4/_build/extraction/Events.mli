open AST
open Floats
open Globalenvs
open Integers
open Values

type eventval =
| EVint of Int.int
| EVlong of Int64.int
| EVfloat of float
| EVsingle of float32
| EVptr_global of ident * Int.int

type event =
| Event_syscall of ident * eventval list * eventval
| Event_vload of memory_chunk * ident * Int.int * eventval
| Event_vstore of memory_chunk * ident * Int.int * eventval
| Event_annot of ident * eventval list

type trace = event list

val coq_E0 : trace

val block_is_volatile : ('a1, 'a2) Genv.t -> block -> bool

val annot_eventvals : annot_arg list -> eventval list -> eventval list

val proj_sig_res' : signature -> typ list

