open BinInt
open BinNums
open Bounds
open Coqlib

(** val fe_ofs_arg : coq_Z **)

let fe_ofs_arg =
  Z0

type frame_env = { fe_size : coq_Z; fe_ofs_link : coq_Z;
                   fe_ofs_retaddr : coq_Z; fe_ofs_local : coq_Z;
                   fe_ofs_int_callee_save : coq_Z;
                   fe_num_int_callee_save : coq_Z;
                   fe_ofs_float_callee_save : coq_Z;
                   fe_num_float_callee_save : coq_Z; fe_stack_data : 
                   coq_Z }

(** val fe_size : frame_env -> coq_Z **)

let fe_size x = x.fe_size

(** val fe_ofs_link : frame_env -> coq_Z **)

let fe_ofs_link x = x.fe_ofs_link

(** val fe_ofs_retaddr : frame_env -> coq_Z **)

let fe_ofs_retaddr x = x.fe_ofs_retaddr

(** val fe_ofs_local : frame_env -> coq_Z **)

let fe_ofs_local x = x.fe_ofs_local

(** val fe_ofs_int_callee_save : frame_env -> coq_Z **)

let fe_ofs_int_callee_save x = x.fe_ofs_int_callee_save

(** val fe_num_int_callee_save : frame_env -> coq_Z **)

let fe_num_int_callee_save x = x.fe_num_int_callee_save

(** val fe_ofs_float_callee_save : frame_env -> coq_Z **)

let fe_ofs_float_callee_save x = x.fe_ofs_float_callee_save

(** val fe_num_float_callee_save : frame_env -> coq_Z **)

let fe_num_float_callee_save x = x.fe_num_float_callee_save

(** val fe_stack_data : frame_env -> coq_Z **)

let fe_stack_data x = x.fe_stack_data

(** val make_env : bounds -> frame_env **)

let make_env b =
  let olink = Z.mul (Zpos (Coq_xO (Coq_xO Coq_xH))) b.bound_outgoing in
  let oics = Z.add olink (Zpos (Coq_xO (Coq_xO Coq_xH))) in
  let ofcs =
    align
      (Z.add oics
        (Z.mul (Zpos (Coq_xO (Coq_xO Coq_xH))) b.bound_int_callee_save))
      (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
  in
  let ol =
    Z.add ofcs
      (Z.mul (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
        b.bound_float_callee_save)
  in
  let ostkdata =
    align (Z.add ol (Z.mul (Zpos (Coq_xO (Coq_xO Coq_xH))) b.bound_local))
      (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
  in
  let oretaddr =
    align (Z.add ostkdata b.bound_stack_data) (Zpos (Coq_xO (Coq_xO Coq_xH)))
  in
  let sz = Z.add oretaddr (Zpos (Coq_xO (Coq_xO Coq_xH))) in
  { fe_size = sz; fe_ofs_link = olink; fe_ofs_retaddr = oretaddr;
  fe_ofs_local = ol; fe_ofs_int_callee_save = oics; fe_num_int_callee_save =
  b.bound_int_callee_save; fe_ofs_float_callee_save = ofcs;
  fe_num_float_callee_save = b.bound_float_callee_save; fe_stack_data =
  ostkdata }

