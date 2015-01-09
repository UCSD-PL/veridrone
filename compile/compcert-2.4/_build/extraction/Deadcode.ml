open AST
open BinNums
open Datatypes
open Errors
open Integers
open Kildall
open Lattice
open Maps
open Memdata
open NeedDomain
open NeedOp
open Op
open RTL
open Registers
open ValueAnalysis
open ValueDomain

(** val add_need_all : reg -> nenv -> nenv **)

let add_need_all r ne =
  NE.set r All ne

(** val add_need : reg -> nval -> nenv -> nenv **)

let add_need r nv ne =
  NE.set r (nlub nv (NE.get r ne)) ne

(** val add_needs_all : reg list -> nenv -> nenv **)

let rec add_needs_all rl ne =
  match rl with
  | [] -> ne
  | r1 :: rs -> add_need_all r1 (add_needs_all rs ne)

(** val add_needs : reg list -> nval list -> nenv -> nenv **)

let rec add_needs rl nvl ne =
  match rl with
  | [] -> ne
  | r1 :: rs ->
    (match nvl with
     | [] -> add_needs_all rl ne
     | nv1 :: nvs -> add_need r1 nv1 (add_needs rs nvs ne))

(** val add_ros_need_all : (reg, ident) sum -> nenv -> nenv **)

let add_ros_need_all ros ne =
  match ros with
  | Coq_inl r -> add_need_all r ne
  | Coq_inr s -> ne

(** val add_opt_need_all : reg option -> nenv -> nenv **)

let add_opt_need_all or0 ne =
  match or0 with
  | Some r -> add_need_all r ne
  | None -> ne

(** val kill : reg -> nenv -> nenv **)

let kill r ne =
  NE.set r Nothing ne

(** val is_dead : nval -> bool **)

let is_dead = function
| Nothing -> true
| _ -> false

(** val is_int_zero : nval -> bool **)

let is_int_zero = function
| NeedDomain.I n -> Int.eq n Int.zero
| _ -> false

(** val transfer_builtin :
    VA.t -> external_function -> reg list -> reg -> NE.t -> nmem -> NA.t **)

let transfer_builtin app ef args res0 ne nm =
  match ef with
  | EF_vload chunk ->
    (match args with
     | [] -> ((add_needs_all args (kill res0 ne)), nmem_all)
     | a1 :: l ->
       (match l with
        | [] ->
          ((add_needs_all args (kill res0 ne)),
            (nmem_add nm (aaddr app a1) (size_chunk chunk)))
        | r :: l0 -> ((add_needs_all args (kill res0 ne)), nmem_all)))
  | EF_vstore chunk ->
    (match args with
     | [] -> ((add_needs_all args (kill res0 ne)), nmem_all)
     | a1 :: l ->
       (match l with
        | [] -> ((add_needs_all args (kill res0 ne)), nmem_all)
        | a2 :: l0 ->
          (match l0 with
           | [] ->
             ((add_need_all a1
                (add_need a2 (store_argument chunk) (kill res0 ne))), nm)
           | r :: l1 -> ((add_needs_all args (kill res0 ne)), nmem_all))))
  | EF_vload_global (chunk, id, ofs) ->
    (match args with
     | [] ->
       ((add_needs_all args (kill res0 ne)),
         (nmem_add nm (Gl (id, ofs)) (size_chunk chunk)))
     | r :: l -> ((add_needs_all args (kill res0 ne)), nmem_all))
  | EF_vstore_global (chunk, id, ofs) ->
    (match args with
     | [] -> ((add_needs_all args (kill res0 ne)), nmem_all)
     | a1 :: l ->
       (match l with
        | [] -> ((add_need a1 (store_argument chunk) (kill res0 ne)), nm)
        | r :: l0 -> ((add_needs_all args (kill res0 ne)), nmem_all)))
  | EF_memcpy (sz, al) ->
    (match args with
     | [] -> ((add_needs_all args (kill res0 ne)), nmem_all)
     | dst :: l ->
       (match l with
        | [] -> ((add_needs_all args (kill res0 ne)), nmem_all)
        | src :: l0 ->
          (match l0 with
           | [] ->
             if nmem_contains nm (aaddr app dst) sz
             then ((add_needs_all args (kill res0 ne)),
                    (nmem_add (nmem_remove nm (aaddr app dst) sz)
                      (aaddr app src) sz))
             else (ne, nm)
           | r :: l1 -> ((add_needs_all args (kill res0 ne)), nmem_all))))
  | EF_annot (txt, targs) -> ((add_needs_all args (kill res0 ne)), nm)
  | EF_annot_val (txt, targ) -> ((add_needs_all args (kill res0 ne)), nm)
  | _ -> ((add_needs_all args (kill res0 ne)), nmem_all)

(** val transfer : coq_function -> VA.t PMap.t -> node -> NA.t -> NA.t **)

let transfer f approx pc after = match after with
| (ne, nm) ->
  (match PTree.get pc f.fn_code with
   | Some i ->
     (match i with
      | Inop s -> after
      | Iop (op, args, res0, s) ->
        let nres = nreg ne res0 in
        if is_dead nres
        then after
        else if is_int_zero nres
             then ((kill res0 ne), nm)
             else ((add_needs args (needs_of_operation op nres)
                     (kill res0 ne)), nm)
      | Iload (chunk, addr, args, dst, s) ->
        let ndst = nreg ne dst in
        if is_dead ndst
        then after
        else if is_int_zero ndst
             then ((kill dst ne), nm)
             else ((add_needs_all args (kill dst ne)),
                    (nmem_add nm (aaddressing (PMap.get pc approx) addr args)
                      (size_chunk chunk)))
      | Istore (chunk, addr, args, src, s) ->
        let p = aaddressing (PMap.get pc approx) addr args in
        if nmem_contains nm p (size_chunk chunk)
        then ((add_needs_all args (add_need src (store_argument chunk) ne)),
               (nmem_remove nm p (size_chunk chunk)))
        else after
      | Icall (sig0, ros, args, res0, s) ->
        ((add_needs_all args (add_ros_need_all ros (kill res0 ne))),
          nmem_all)
      | Itailcall (sig0, ros, args) ->
        ((add_needs_all args (add_ros_need_all ros NE.bot)),
          (nmem_dead_stack f.fn_stacksize))
      | Ibuiltin (ef, args, res0, s) ->
        transfer_builtin (PMap.get pc approx) ef args res0 ne nm
      | Icond (cond, args, s1, s2) ->
        ((add_needs args (needs_of_condition cond) ne), nm)
      | Ijumptable (arg, tbl) -> ((add_need_all arg ne), nm)
      | Ireturn optarg ->
        ((add_opt_need_all optarg ne), (nmem_dead_stack f.fn_stacksize)))
   | None -> NA.bot)

module DS = Backward_Dataflow_Solver(NA)(NodeSetBackward)

(** val analyze : VA.t PMap.t -> coq_function -> NA.t PMap.t option **)

let analyze approx f =
  DS.fixpoint f.fn_code successors_instr (transfer f approx)

(** val transf_instr :
    VA.t PMap.t -> NA.t PMap.t -> node -> instruction -> instruction **)

let transf_instr approx an pc instr = match instr with
| Iop (op, args, res0, s) ->
  let nres = nreg (fst (PMap.get pc an)) res0 in
  if is_dead nres
  then Inop s
  else if is_int_zero nres
       then Iop ((Ointconst Int.zero), [], res0, s)
       else if operation_is_redundant op nres
            then (match args with
                  | [] -> instr
                  | arg :: l -> Iop (Omove, (arg :: []), res0, s))
            else instr
| Iload (chunk, addr, args, dst, s) ->
  let ndst = nreg (fst (PMap.get pc an)) dst in
  if is_dead ndst
  then Inop s
  else if is_int_zero ndst
       then Iop ((Ointconst Int.zero), [], dst, s)
       else instr
| Istore (chunk, addr, args, src, s) ->
  let p = aaddressing (PMap.get pc approx) addr args in
  if nmem_contains (snd (PMap.get pc an)) p (size_chunk chunk)
  then instr
  else Inop s
| Ibuiltin (e, l, res0, s) ->
  (match e with
   | EF_memcpy (sz, al) ->
     (match l with
      | [] -> instr
      | dst :: l0 ->
        (match l0 with
         | [] -> instr
         | src :: l1 ->
           (match l1 with
            | [] ->
              if nmem_contains (snd (PMap.get pc an))
                   (aaddr (PMap.get pc approx) dst) sz
              then instr
              else Inop s
            | r :: l2 -> instr)))
   | _ -> instr)
| _ -> instr

(** val vanalyze : romem -> coq_function -> VA.t PMap.t **)

let vanalyze =
  ValueAnalysis.analyze

(** val transf_function : romem -> coq_function -> coq_function res **)

let transf_function rm f =
  let approx = vanalyze rm f in
  (match analyze approx f with
   | Some an ->
     OK { fn_sig = f.fn_sig; fn_params = f.fn_params; fn_stacksize =
       f.fn_stacksize; fn_code =
       (PTree.map (transf_instr approx an) f.fn_code); fn_entrypoint =
       f.fn_entrypoint }
   | None ->
     Error
       (msg
         ('N'::('e'::('e'::('d'::('e'::('d'::('n'::('e'::('s'::('s'::(' '::('a'::('n'::('a'::('l'::('y'::('s'::('i'::('s'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))))))))))))))))))

(** val transf_fundef : romem -> fundef -> fundef res **)

let transf_fundef rm fd =
  transf_partial_fundef (transf_function rm) fd

(** val transf_program : program -> program res **)

let transf_program p =
  transform_partial_program (transf_fundef (romem_for_program p)) p

