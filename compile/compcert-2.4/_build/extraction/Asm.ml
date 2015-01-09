open AST
open BinNums
open Datatypes
open Floats
open Integers
open Machregs

type ireg =
| EAX
| EBX
| ECX
| EDX
| ESI
| EDI
| EBP
| ESP

type freg =
| XMM0
| XMM1
| XMM2
| XMM3
| XMM4
| XMM5
| XMM6
| XMM7

(** val ireg_eq : ireg -> ireg -> bool **)

let ireg_eq x y =
  match x with
  | EAX ->
    (match y with
     | EAX -> true
     | _ -> false)
  | EBX ->
    (match y with
     | EBX -> true
     | _ -> false)
  | ECX ->
    (match y with
     | ECX -> true
     | _ -> false)
  | EDX ->
    (match y with
     | EDX -> true
     | _ -> false)
  | ESI ->
    (match y with
     | ESI -> true
     | _ -> false)
  | EDI ->
    (match y with
     | EDI -> true
     | _ -> false)
  | EBP ->
    (match y with
     | EBP -> true
     | _ -> false)
  | ESP ->
    (match y with
     | ESP -> true
     | _ -> false)

type crbit =
| ZF
| CF
| PF
| SF
| OF

type preg =
| PC
| IR of ireg
| FR of freg
| ST0
| CR of crbit
| RA

type label = positive

type addrmode =
| Addrmode of ireg option * (ireg * Int.int) option
   * (Int.int, ident * Int.int) sum

type testcond =
| Cond_e
| Cond_ne
| Cond_b
| Cond_be
| Cond_ae
| Cond_a
| Cond_l
| Cond_le
| Cond_ge
| Cond_g
| Cond_p
| Cond_np

type instruction =
| Pmov_rr of ireg * ireg
| Pmov_ri of ireg * Int.int
| Pmov_ra of ireg * ident
| Pmov_rm of ireg * addrmode
| Pmov_mr of addrmode * ireg
| Pmovsd_ff of freg * freg
| Pmovsd_fi of freg * float
| Pmovsd_fm of freg * addrmode
| Pmovsd_mf of addrmode * freg
| Pmovss_fi of freg * float32
| Pmovss_fm of freg * addrmode
| Pmovss_mf of addrmode * freg
| Pfldl_m of addrmode
| Pfstpl_m of addrmode
| Pflds_m of addrmode
| Pfstps_m of addrmode
| Pxchg_rr of ireg * ireg
| Pmovb_mr of addrmode * ireg
| Pmovw_mr of addrmode * ireg
| Pmovzb_rr of ireg * ireg
| Pmovzb_rm of ireg * addrmode
| Pmovsb_rr of ireg * ireg
| Pmovsb_rm of ireg * addrmode
| Pmovzw_rr of ireg * ireg
| Pmovzw_rm of ireg * addrmode
| Pmovsw_rr of ireg * ireg
| Pmovsw_rm of ireg * addrmode
| Pcvtsd2ss_ff of freg * freg
| Pcvtss2sd_ff of freg * freg
| Pcvttsd2si_rf of ireg * freg
| Pcvtsi2sd_fr of freg * ireg
| Pcvttss2si_rf of ireg * freg
| Pcvtsi2ss_fr of freg * ireg
| Plea of ireg * addrmode
| Pneg of ireg
| Psub_rr of ireg * ireg
| Pimul_rr of ireg * ireg
| Pimul_ri of ireg * Int.int
| Pimul_r of ireg
| Pmul_r of ireg
| Pdiv of ireg
| Pidiv of ireg
| Pand_rr of ireg * ireg
| Pand_ri of ireg * Int.int
| Por_rr of ireg * ireg
| Por_ri of ireg * Int.int
| Pxor_r of ireg
| Pxor_rr of ireg * ireg
| Pxor_ri of ireg * Int.int
| Pnot of ireg
| Psal_rcl of ireg
| Psal_ri of ireg * Int.int
| Pshr_rcl of ireg
| Pshr_ri of ireg * Int.int
| Psar_rcl of ireg
| Psar_ri of ireg * Int.int
| Pshld_ri of ireg * ireg * Int.int
| Pror_ri of ireg * Int.int
| Pcmp_rr of ireg * ireg
| Pcmp_ri of ireg * Int.int
| Ptest_rr of ireg * ireg
| Ptest_ri of ireg * Int.int
| Pcmov of testcond * ireg * ireg
| Psetcc of testcond * ireg
| Paddd_ff of freg * freg
| Psubd_ff of freg * freg
| Pmuld_ff of freg * freg
| Pdivd_ff of freg * freg
| Pnegd of freg
| Pabsd of freg
| Pcomisd_ff of freg * freg
| Pxorpd_f of freg
| Padds_ff of freg * freg
| Psubs_ff of freg * freg
| Pmuls_ff of freg * freg
| Pdivs_ff of freg * freg
| Pnegs of freg
| Pabss of freg
| Pcomiss_ff of freg * freg
| Pxorps_f of freg
| Pjmp_l of label
| Pjmp_s of ident * signature
| Pjmp_r of ireg * signature
| Pjcc of testcond * label
| Pjcc2 of testcond * testcond * label
| Pjmptbl of ireg * label list
| Pcall_s of ident * signature
| Pcall_r of ireg * signature
| Pret
| Pmov_rm_a of ireg * addrmode
| Pmov_mr_a of addrmode * ireg
| Pmovsd_fm_a of freg * addrmode
| Pmovsd_mf_a of addrmode * freg
| Plabel of label
| Pallocframe of coq_Z * Int.int * Int.int
| Pfreeframe of coq_Z * Int.int * Int.int
| Pbuiltin of external_function * preg list * preg list
| Pannot of external_function * annot_param list
and annot_param =
| APreg of preg
| APstack of memory_chunk * coq_Z

type code = instruction list

type coq_function = { fn_sig : signature; fn_code : code }

(** val fn_code : coq_function -> code **)

let fn_code x = x.fn_code

type fundef = coq_function AST.fundef

type program = (fundef, unit) AST.program

(** val preg_of : mreg -> preg **)

let preg_of = function
| AX -> IR EAX
| BX -> IR EBX
| CX -> IR ECX
| DX -> IR EDX
| SI -> IR ESI
| DI -> IR EDI
| BP -> IR EBP
| X0 -> FR XMM0
| X1 -> FR XMM1
| X2 -> FR XMM2
| X3 -> FR XMM3
| X4 -> FR XMM4
| X5 -> FR XMM5
| X6 -> FR XMM6
| X7 -> FR XMM7
| FP0 -> ST0

