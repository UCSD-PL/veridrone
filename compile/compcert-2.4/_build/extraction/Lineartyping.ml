open AST
open BinNums
open Conventions
open Conventions1
open Coqlib
open Events
open Linear
open List0
open Locations
open Machregs
open Op

(** val slot_valid : coq_function -> slot -> coq_Z -> typ -> bool **)

let slot_valid funct sl ofs ty =
  (&&)
    (match sl with
     | Incoming ->
       (fun x -> x)
         (in_dec Loc.eq (S (Incoming, ofs, ty))
           (loc_parameters funct.fn_sig))
     | _ -> (fun x -> x) (zle Z0 ofs))
    (match ty with
     | Tlong -> false
     | _ -> true)

(** val slot_writable : slot -> bool **)

let slot_writable = function
| Incoming -> false
| _ -> true

(** val loc_valid : coq_function -> loc -> bool **)

let loc_valid funct = function
| R r -> true
| S (sl, ofs, ty) ->
  (match sl with
   | Local -> slot_valid funct Local ofs ty
   | _ -> false)

(** val wt_instr : coq_function -> instruction -> bool **)

let wt_instr funct = function
| Lgetstack (sl, ofs, ty, r) ->
  (&&) (subtype ty (mreg_type r)) (slot_valid funct sl ofs ty)
| Lsetstack (r, sl, ofs, ty) ->
  (&&) (slot_valid funct sl ofs ty) (slot_writable sl)
| Lop (op, args, res) ->
  (match is_move_operation op args with
   | Some arg -> subtype (mreg_type arg) (mreg_type res)
   | None ->
     let (targs, tres) = type_of_operation op in subtype tres (mreg_type res))
| Lload (chunk, addr, args, dst) ->
  subtype (type_of_chunk chunk) (mreg_type dst)
| Ltailcall (sg, ros) -> (fun x -> x) (zeq (size_arguments sg) Z0)
| Lbuiltin (ef, args, res) ->
  subtype_list (proj_sig_res' (ef_sig ef)) (map mreg_type res)
| Lannot (ef, args) -> forallb (loc_valid funct) args
| _ -> true

(** val wt_code : coq_function -> code -> bool **)

let wt_code f c =
  forallb (wt_instr f) c

(** val wt_function : coq_function -> bool **)

let wt_function f =
  wt_code f f.fn_code

