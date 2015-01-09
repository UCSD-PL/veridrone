open AST
open BinInt
open BinNums
open Datatypes
open Locations
open Machregs

(** val int_caller_save_regs : mreg list **)

let int_caller_save_regs =
  AX :: (CX :: (DX :: []))

(** val float_caller_save_regs : mreg list **)

let float_caller_save_regs =
  X0 :: (X1 :: (X2 :: (X3 :: (X4 :: (X5 :: (X6 :: (X7 :: [])))))))

(** val int_callee_save_regs : mreg list **)

let int_callee_save_regs =
  BX :: (SI :: (DI :: (BP :: [])))

(** val float_callee_save_regs : mreg list **)

let float_callee_save_regs =
  []

(** val destroyed_at_call : mreg list **)

let destroyed_at_call =
  FP0 :: (app int_caller_save_regs float_caller_save_regs)

(** val dummy_int_reg : mreg **)

let dummy_int_reg =
  AX

(** val dummy_float_reg : mreg **)

let dummy_float_reg =
  X0

(** val index_int_callee_save : mreg -> coq_Z **)

let index_int_callee_save = function
| BX -> Z0
| SI -> Zpos Coq_xH
| DI -> Zpos (Coq_xO Coq_xH)
| BP -> Zpos (Coq_xI Coq_xH)
| _ -> Zneg Coq_xH

(** val index_float_callee_save : mreg -> coq_Z **)

let index_float_callee_save r =
  Zneg Coq_xH

(** val loc_result : signature -> mreg list **)

let loc_result s =
  match s.sig_res with
  | Some t ->
    (match t with
     | Tint -> AX :: []
     | Tlong -> DX :: (AX :: [])
     | Tany32 -> AX :: []
     | Tany64 -> X0 :: []
     | _ -> FP0 :: [])
  | None -> AX :: []

(** val loc_arguments_rec : typ list -> coq_Z -> loc list **)

let rec loc_arguments_rec tyl ofs =
  match tyl with
  | [] -> []
  | t :: tys ->
    (match t with
     | Tfloat ->
       (S (Outgoing, ofs,
         Tfloat)) :: (loc_arguments_rec tys
                       (Z.add ofs (Zpos (Coq_xO Coq_xH))))
     | Tlong ->
       (S (Outgoing, (Z.add ofs (Zpos Coq_xH)), Tint)) :: ((S (Outgoing, ofs,
         Tint)) :: (loc_arguments_rec tys (Z.add ofs (Zpos (Coq_xO Coq_xH)))))
     | Tany64 ->
       (S (Outgoing, ofs,
         Tany64)) :: (loc_arguments_rec tys
                       (Z.add ofs (Zpos (Coq_xO Coq_xH))))
     | x ->
       (S (Outgoing, ofs,
         x)) :: (loc_arguments_rec tys (Z.add ofs (Zpos Coq_xH))))

(** val loc_arguments : signature -> loc list **)

let loc_arguments s =
  loc_arguments_rec s.sig_args Z0

(** val size_arguments_rec : typ list -> coq_Z -> coq_Z **)

let rec size_arguments_rec tyl ofs =
  match tyl with
  | [] -> ofs
  | ty :: tys -> size_arguments_rec tys (Z.add ofs (typesize ty))

(** val size_arguments : signature -> coq_Z **)

let size_arguments s =
  size_arguments_rec s.sig_args Z0

