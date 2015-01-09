open BinInt
open BinNums
open Bounds
open Coqlib

val fe_ofs_arg : coq_Z

type frame_env = { fe_size : coq_Z; fe_ofs_link : coq_Z;
                   fe_ofs_retaddr : coq_Z; fe_ofs_local : coq_Z;
                   fe_ofs_int_callee_save : coq_Z;
                   fe_num_int_callee_save : coq_Z;
                   fe_ofs_float_callee_save : coq_Z;
                   fe_num_float_callee_save : coq_Z; fe_stack_data : 
                   coq_Z }

val fe_size : frame_env -> coq_Z

val fe_ofs_link : frame_env -> coq_Z

val fe_ofs_retaddr : frame_env -> coq_Z

val fe_ofs_local : frame_env -> coq_Z

val fe_ofs_int_callee_save : frame_env -> coq_Z

val fe_num_int_callee_save : frame_env -> coq_Z

val fe_ofs_float_callee_save : frame_env -> coq_Z

val fe_num_float_callee_save : frame_env -> coq_Z

val fe_stack_data : frame_env -> coq_Z

val make_env : bounds -> frame_env

