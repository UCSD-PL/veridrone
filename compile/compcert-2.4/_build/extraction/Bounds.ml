open AST
open BinInt
open BinNums
open Conventions1
open Datatypes
open Linear
open List0
open Locations
open Machregs

type bounds = { bound_local : coq_Z; bound_int_callee_save : coq_Z;
                bound_float_callee_save : coq_Z; bound_outgoing : coq_Z;
                bound_stack_data : coq_Z }

(** val bound_local : bounds -> coq_Z **)

let bound_local x = x.bound_local

(** val bound_int_callee_save : bounds -> coq_Z **)

let bound_int_callee_save x = x.bound_int_callee_save

(** val bound_float_callee_save : bounds -> coq_Z **)

let bound_float_callee_save x = x.bound_float_callee_save

(** val bound_outgoing : bounds -> coq_Z **)

let bound_outgoing x = x.bound_outgoing

(** val bound_stack_data : bounds -> coq_Z **)

let bound_stack_data x = x.bound_stack_data

(** val regs_of_instr : instruction -> mreg list **)

let regs_of_instr = function
| Lgetstack (sl, ofs, ty, r) -> r :: []
| Lsetstack (r, sl, ofs, ty) -> r :: []
| Lop (op, args, res) -> res :: []
| Lload (chunk, addr, args, dst) -> dst :: []
| Lbuiltin (ef, args, res) -> app res (destroyed_by_builtin ef)
| _ -> []

(** val slots_of_locs : loc list -> ((slot * coq_Z) * typ) list **)

let rec slots_of_locs = function
| [] -> []
| l0 :: l' ->
  (match l0 with
   | R r -> slots_of_locs l'
   | S (sl, ofs, ty) -> ((sl, ofs), ty) :: (slots_of_locs l'))

(** val slots_of_instr : instruction -> ((slot * coq_Z) * typ) list **)

let slots_of_instr = function
| Lgetstack (sl, ofs, ty, r) -> ((sl, ofs), ty) :: []
| Lsetstack (r, sl, ofs, ty) -> ((sl, ofs), ty) :: []
| Lannot (ef, args) -> slots_of_locs args
| _ -> []

(** val max_over_list : ('a1 -> coq_Z) -> 'a1 list -> coq_Z **)

let max_over_list valu l =
  fold_left (fun m l0 -> Z.max m (valu l0)) l Z0

(** val max_over_instrs : coq_function -> (instruction -> coq_Z) -> coq_Z **)

let max_over_instrs f valu =
  max_over_list valu f.fn_code

(** val max_over_regs_of_instr : (mreg -> coq_Z) -> instruction -> coq_Z **)

let max_over_regs_of_instr valu i =
  max_over_list valu (regs_of_instr i)

(** val max_over_slots_of_instr :
    (((slot * coq_Z) * typ) -> coq_Z) -> instruction -> coq_Z **)

let max_over_slots_of_instr valu i =
  max_over_list valu (slots_of_instr i)

(** val max_over_regs_of_funct : coq_function -> (mreg -> coq_Z) -> coq_Z **)

let max_over_regs_of_funct f valu =
  max_over_instrs f (max_over_regs_of_instr valu)

(** val max_over_slots_of_funct :
    coq_function -> (((slot * coq_Z) * typ) -> coq_Z) -> coq_Z **)

let max_over_slots_of_funct f valu =
  max_over_instrs f (max_over_slots_of_instr valu)

(** val int_callee_save : mreg -> coq_Z **)

let int_callee_save r =
  Z.add (Zpos Coq_xH) (index_int_callee_save r)

(** val float_callee_save : mreg -> coq_Z **)

let float_callee_save r =
  Z.add (Zpos Coq_xH) (index_float_callee_save r)

(** val local_slot : ((slot * coq_Z) * typ) -> coq_Z **)

let local_slot = function
| (p, ty) ->
  let (s0, ofs) = p in
  (match s0 with
   | Local -> Z.add ofs (typesize ty)
   | _ -> Z0)

(** val outgoing_slot : ((slot * coq_Z) * typ) -> coq_Z **)

let outgoing_slot = function
| (p, ty) ->
  let (s0, ofs) = p in
  (match s0 with
   | Outgoing -> Z.add ofs (typesize ty)
   | _ -> Z0)

(** val outgoing_space : instruction -> coq_Z **)

let outgoing_space = function
| Lcall (sig0, s) -> size_arguments sig0
| _ -> Z0

(** val function_bounds : coq_function -> bounds **)

let function_bounds f =
  { bound_local = (max_over_slots_of_funct f local_slot);
    bound_int_callee_save = (max_over_regs_of_funct f int_callee_save);
    bound_float_callee_save = (max_over_regs_of_funct f float_callee_save);
    bound_outgoing =
    (Z.max (max_over_instrs f outgoing_space)
      (max_over_slots_of_funct f outgoing_slot)); bound_stack_data =
    (Z.max f.fn_stacksize Z0) }

