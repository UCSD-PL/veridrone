open AST
open BinNums
open Datatypes
open Kildall
open Lattice
open List0
open Maps
open RTL
open Registers

(** val reg_option_live : reg option -> Regset.t -> Regset.t **)

let reg_option_live or0 lv =
  match or0 with
  | Some r -> Regset.add r lv
  | None -> lv

(** val reg_sum_live : (reg, ident) sum -> Regset.t -> Regset.t **)

let reg_sum_live ros lv =
  match ros with
  | Coq_inl r -> Regset.add r lv
  | Coq_inr s -> lv

(** val reg_list_live : reg list -> Regset.t -> Regset.t **)

let rec reg_list_live rl lv =
  match rl with
  | [] -> lv
  | r1 :: rs -> reg_list_live rs (Regset.add r1 lv)

(** val transfer : coq_function -> node -> Regset.t -> Regset.t **)

let transfer f pc after =
  match PTree.get pc f.fn_code with
  | Some i ->
    (match i with
     | Inop s -> after
     | Iop (op, args, res, s) ->
       if Regset.mem res after
       then reg_list_live args (Regset.remove res after)
       else after
     | Iload (chunk, addr, args, dst, s) ->
       if Regset.mem dst after
       then reg_list_live args (Regset.remove dst after)
       else after
     | Istore (chunk, addr, args, src, s) ->
       reg_list_live args (Regset.add src after)
     | Icall (sig0, ros, args, res, s) ->
       reg_list_live args (reg_sum_live ros (Regset.remove res after))
     | Itailcall (sig0, ros, args) ->
       reg_list_live args (reg_sum_live ros Regset.empty)
     | Ibuiltin (ef, args, res, s) ->
       reg_list_live args (Regset.remove res after)
     | Icond (cond, args, ifso, ifnot) -> reg_list_live args after
     | Ijumptable (arg, tbl) -> Regset.add arg after
     | Ireturn optarg -> reg_option_live optarg Regset.empty)
  | None -> Regset.empty

module RegsetLat = LFSet(Regset)

module DS = Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward)

(** val analyze : coq_function -> Regset.t PMap.t option **)

let analyze f =
  DS.fixpoint f.fn_code successors_instr (transfer f)

(** val last_uses_at : Regset.t PMap.t -> node -> instruction -> reg list **)

let last_uses_at live pc i =
  let l = PMap.get pc live in
  let lu = filter (fun r -> negb (Regset.mem r l)) (instr_uses i) in
  (match instr_defs i with
   | Some r -> if Regset.mem r l then lu else r :: lu
   | None -> lu)

(** val last_uses : coq_function -> reg list PTree.t **)

let last_uses f =
  match analyze f with
  | Some live -> PTree.map (last_uses_at live) f.fn_code
  | None -> PTree.empty

