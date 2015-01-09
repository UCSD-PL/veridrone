open BinInt
open BinNums
open CminorSel
open Compopts
open Coqlib
open Datatypes
open Floats
open Integers
open Op
open SelectOp
open Zpower

val find_div_mul_params :
  nat -> coq_Z -> coq_Z -> coq_Z -> (coq_Z * coq_Z) option

val divs_mul_params : coq_Z -> (coq_Z * coq_Z) option

val divu_mul_params : coq_Z -> (coq_Z * coq_Z) option

val divu_mul : coq_Z -> coq_Z -> expr

val divuimm : expr -> Int.int -> expr

type divu_cases =
| Coq_divu_case1 of Int.int
| Coq_divu_default of expr

val divu_match : expr -> divu_cases

val divu : expr -> expr -> expr

val mod_from_div : expr -> Int.int -> expr

val moduimm : expr -> Int.int -> expr

type modu_cases =
| Coq_modu_case1 of Int.int
| Coq_modu_default of expr

val modu_match : expr -> modu_cases

val modu : expr -> expr -> expr

val divs_mul : coq_Z -> coq_Z -> expr

val divsimm : expr -> Int.int -> expr

type divs_cases =
| Coq_divs_case1 of Int.int
| Coq_divs_default of expr

val divs_match : expr -> divs_cases

val divs : expr -> expr -> expr

val modsimm : expr -> Int.int -> expr

type mods_cases =
| Coq_mods_case1 of Int.int
| Coq_mods_default of expr

val mods_match : expr -> mods_cases

val mods : expr -> expr -> expr

val divfimm : expr -> float -> expr

type divf_cases =
| Coq_divf_case1 of float
| Coq_divf_default of expr

val divf_match : expr -> divf_cases

val divf : expr -> expr -> expr

val divfsimm : expr -> float32 -> expr

type divfs_cases =
| Coq_divfs_case1 of float32
| Coq_divfs_default of expr

val divfs_match : expr -> divfs_cases

val divfs : expr -> expr -> expr

