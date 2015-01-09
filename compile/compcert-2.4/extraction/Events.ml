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

(** val coq_E0 : trace **)

let coq_E0 =
  []

(** val block_is_volatile : ('a1, 'a2) Genv.t -> block -> bool **)

let block_is_volatile ge b =
  match Genv.find_var_info ge b with
  | Some gv -> gv.gvar_volatile
  | None -> false

(** val annot_eventvals :
    annot_arg list -> eventval list -> eventval list **)

let rec annot_eventvals targs vargs =
  match targs with
  | [] -> vargs
  | a :: targs' ->
    (match a with
     | AA_arg ty ->
       (match vargs with
        | [] -> vargs
        | varg :: vargs' -> varg :: (annot_eventvals targs' vargs'))
     | AA_int n -> (EVint n) :: (annot_eventvals targs' vargs)
     | AA_float n -> (EVfloat n) :: (annot_eventvals targs' vargs))

(** val proj_sig_res' : signature -> typ list **)

let proj_sig_res' s =
  match s.sig_res with
  | Some ty ->
    (match ty with
     | Tlong -> Tint :: (Tint :: [])
     | _ -> ty :: [])
  | None -> Tint :: []

