open AST
open BinInt
open BinNums
open Bounds
open Conventions1
open Coqlib
open Datatypes
open Errors
open Integers
open Linear
open Lineartyping
open List0
open Locations
open Mach
open Machregs
open Op
open Stacklayout

type frame_index =
| FI_link
| FI_retaddr
| FI_local of coq_Z * typ
| FI_arg of coq_Z * typ
| FI_saved_int of coq_Z
| FI_saved_float of coq_Z

(** val offset_of_index : frame_env -> frame_index -> coq_Z **)

let offset_of_index fe = function
| FI_link -> fe.fe_ofs_link
| FI_retaddr -> fe.fe_ofs_retaddr
| FI_local (x, ty) ->
  Z.add fe.fe_ofs_local (Z.mul (Zpos (Coq_xO (Coq_xO Coq_xH))) x)
| FI_arg (x, ty) ->
  Z.add fe_ofs_arg (Z.mul (Zpos (Coq_xO (Coq_xO Coq_xH))) x)
| FI_saved_int x ->
  Z.add fe.fe_ofs_int_callee_save (Z.mul (Zpos (Coq_xO (Coq_xO Coq_xH))) x)
| FI_saved_float x ->
  Z.add fe.fe_ofs_float_callee_save
    (Z.mul (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) x)

(** val save_callee_save_reg :
    (frame_env -> coq_Z) -> (mreg -> coq_Z) -> (coq_Z -> frame_index) -> typ
    -> frame_env -> mreg -> code -> instruction list **)

let save_callee_save_reg bound number mkindex ty fe cs k =
  let i = number cs in
  if zlt i (bound fe)
  then (Msetstack (cs, (Int.repr (offset_of_index fe (mkindex i))), ty)) :: k
  else k

(** val save_callee_save_regs :
    (frame_env -> coq_Z) -> (mreg -> coq_Z) -> (coq_Z -> frame_index) -> typ
    -> frame_env -> mreg list -> code -> code **)

let save_callee_save_regs bound number mkindex ty fe csl k =
  fold_right (save_callee_save_reg bound number mkindex ty fe) k csl

(** val save_callee_save_int : frame_env -> code -> code **)

let save_callee_save_int fe =
  save_callee_save_regs fe_num_int_callee_save index_int_callee_save
    (fun x -> FI_saved_int x) Tany32 fe int_callee_save_regs

(** val save_callee_save_float : frame_env -> code -> code **)

let save_callee_save_float fe =
  save_callee_save_regs fe_num_float_callee_save index_float_callee_save
    (fun x -> FI_saved_float x) Tany64 fe float_callee_save_regs

(** val save_callee_save : frame_env -> code -> code **)

let save_callee_save fe k =
  save_callee_save_int fe (save_callee_save_float fe k)

(** val restore_callee_save_reg :
    (frame_env -> coq_Z) -> (mreg -> coq_Z) -> (coq_Z -> frame_index) -> typ
    -> frame_env -> mreg -> code -> instruction list **)

let restore_callee_save_reg bound number mkindex ty fe cs k =
  let i = number cs in
  if zlt i (bound fe)
  then (Mgetstack ((Int.repr (offset_of_index fe (mkindex i))), ty, cs)) :: k
  else k

(** val restore_callee_save_regs :
    (frame_env -> coq_Z) -> (mreg -> coq_Z) -> (coq_Z -> frame_index) -> typ
    -> frame_env -> mreg list -> code -> code **)

let restore_callee_save_regs bound number mkindex ty fe csl k =
  fold_right (restore_callee_save_reg bound number mkindex ty fe) k csl

(** val restore_callee_save_int : frame_env -> code -> code **)

let restore_callee_save_int fe =
  restore_callee_save_regs fe_num_int_callee_save index_int_callee_save
    (fun x -> FI_saved_int x) Tany32 fe int_callee_save_regs

(** val restore_callee_save_float : frame_env -> code -> code **)

let restore_callee_save_float fe =
  restore_callee_save_regs fe_num_float_callee_save index_float_callee_save
    (fun x -> FI_saved_float x) Tany64 fe float_callee_save_regs

(** val restore_callee_save : frame_env -> code -> code **)

let restore_callee_save fe k =
  restore_callee_save_int fe (restore_callee_save_float fe k)

(** val transl_op : frame_env -> operation -> operation **)

let transl_op fe op =
  shift_stack_operation (Int.repr fe.fe_stack_data) op

(** val transl_addr : frame_env -> addressing -> addressing **)

let transl_addr fe addr =
  shift_stack_addressing (Int.repr fe.fe_stack_data) addr

(** val transl_annot_param : frame_env -> loc -> annot_param **)

let transl_annot_param fe = function
| R r -> APreg r
| S (sl, ofs, ty) ->
  (match sl with
   | Local ->
     APstack ((chunk_of_type ty), (offset_of_index fe (FI_local (ofs, ty))))
   | _ -> APstack (Mint32, (Zneg Coq_xH)))

(** val transl_instr : frame_env -> Linear.instruction -> code -> code **)

let transl_instr fe i k =
  match i with
  | Lgetstack (sl, ofs, ty, r) ->
    (match sl with
     | Local ->
       (Mgetstack ((Int.repr (offset_of_index fe (FI_local (ofs, ty)))), ty,
         r)) :: k
     | Incoming ->
       (Mgetparam ((Int.repr (offset_of_index fe (FI_arg (ofs, ty)))), ty,
         r)) :: k
     | Outgoing ->
       (Mgetstack ((Int.repr (offset_of_index fe (FI_arg (ofs, ty)))), ty,
         r)) :: k)
  | Lsetstack (r, sl, ofs, ty) ->
    (match sl with
     | Local ->
       (Msetstack (r, (Int.repr (offset_of_index fe (FI_local (ofs, ty)))),
         ty)) :: k
     | Incoming -> k
     | Outgoing ->
       (Msetstack (r, (Int.repr (offset_of_index fe (FI_arg (ofs, ty)))),
         ty)) :: k)
  | Lop (op, args, res0) -> (Mop ((transl_op fe op), args, res0)) :: k
  | Lload (chunk, addr, args, dst) ->
    (Mload (chunk, (transl_addr fe addr), args, dst)) :: k
  | Lstore (chunk, addr, args, src) ->
    (Mstore (chunk, (transl_addr fe addr), args, src)) :: k
  | Lcall (sig0, ros) -> (Mcall (sig0, ros)) :: k
  | Ltailcall (sig0, ros) ->
    restore_callee_save fe ((Mtailcall (sig0, ros)) :: k)
  | Lbuiltin (ef, args, dst) -> (Mbuiltin (ef, args, dst)) :: k
  | Lannot (ef, args) ->
    (Mannot (ef, (map (transl_annot_param fe) args))) :: k
  | Llabel lbl -> (Mlabel lbl) :: k
  | Lgoto lbl -> (Mgoto lbl) :: k
  | Lcond (cond, args, lbl) -> (Mcond (cond, args, lbl)) :: k
  | Ljumptable (arg, tbl) -> (Mjumptable (arg, tbl)) :: k
  | Lreturn -> restore_callee_save fe (Mreturn :: k)

(** val transl_code : frame_env -> Linear.instruction list -> code **)

let transl_code fe il =
  list_fold_right (transl_instr fe) il []

(** val transl_body : Linear.coq_function -> frame_env -> code **)

let transl_body f fe =
  save_callee_save fe (transl_code fe f.Linear.fn_code)

(** val transf_function : Linear.coq_function -> coq_function res **)

let transf_function f =
  let fe = make_env (function_bounds f) in
  if negb (wt_function f)
  then Error
         (msg
           ('I'::('l'::('l'::('-'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('L'::('i'::('n'::('e'::('a'::('r'::(' '::('c'::('o'::('d'::('e'::[])))))))))))))))))))))))
  else if zlt Int.max_unsigned fe.fe_size
       then Error
              (msg
                ('T'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('s'::('p'::('i'::('l'::('l'::('e'::('d'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::('s'::(','::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('s'::('i'::('z'::('e'::(' '::('e'::('x'::('c'::('e'::('e'::('d'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))))
       else OK { fn_sig = f.Linear.fn_sig; fn_code = (transl_body f fe);
              fn_stacksize = fe.fe_size; fn_link_ofs =
              (Int.repr fe.fe_ofs_link); fn_retaddr_ofs =
              (Int.repr fe.fe_ofs_retaddr) }

(** val transf_fundef : Linear.fundef -> fundef res **)

let transf_fundef f =
  transf_partial_fundef transf_function f

(** val transf_program : Linear.program -> program res **)

let transf_program p =
  transform_partial_program transf_fundef p

