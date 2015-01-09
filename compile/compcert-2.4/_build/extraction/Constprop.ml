open AST
open Compopts
open ConstpropOp
open Coqlib
open Datatypes
open Integers
open Maps
open Op
open RTL
open Registers
open ValueAOp
open ValueAnalysis
open ValueDomain

(** val transf_ros : AE.t -> (reg, ident) sum -> (reg, ident) sum **)

let transf_ros ae ros = match ros with
| Coq_inl r ->
  (match areg ae r with
   | Ptr p ->
     (match p with
      | Gl (symb, ofs) -> if Int.eq ofs Int.zero then Coq_inr symb else ros
      | _ -> ros)
   | _ -> ros)
| Coq_inr s -> ros

(** val const_for_result : aval -> operation option **)

let const_for_result = function
| I n -> Some (Ointconst n)
| F n -> if generate_float_constants () then Some (Ofloatconst n) else None
| FS n -> if generate_float_constants () then Some (Osingleconst n) else None
| Ptr p ->
  (match p with
   | Gl (symb, ofs) -> Some (coq_Oaddrsymbol symb ofs)
   | Stk ofs -> Some (coq_Oaddrstack ofs)
   | _ -> None)
| _ -> None

(** val successor_rec : nat -> coq_function -> AE.t -> node -> node **)

let rec successor_rec n f ae pc =
  match n with
  | O -> pc
  | S n' ->
    (match PTree.get pc f.fn_code with
     | Some i ->
       (match i with
        | Inop s -> successor_rec n' f ae s
        | Icond (cond, args, s1, s2) ->
          (match resolve_branch (eval_static_condition cond (aregs ae args)) with
           | Some b -> successor_rec n' f ae (if b then s1 else s2)
           | None -> pc)
        | _ -> pc)
     | None -> pc)

(** val num_iter : nat **)

let num_iter =
  S (S (S (S (S (S (S (S (S (S O)))))))))

(** val successor : coq_function -> AE.t -> node -> node **)

let successor f ae pc =
  successor_rec num_iter f ae pc

(** val annot_strength_reduction :
    AE.t -> annot_arg list -> reg list -> annot_arg list * reg list **)

let rec annot_strength_reduction ae targs args =
  match targs with
  | [] -> (targs, args)
  | targ :: targs' ->
    (match targ with
     | AA_arg ty ->
       (match args with
        | [] ->
          let (targs'', args'') = annot_strength_reduction ae targs' args in
          ((targ :: targs''), args'')
        | arg :: args' ->
          let (targs'', args'') = annot_strength_reduction ae targs' args' in
          (match ty with
           | Tint ->
             (match areg ae arg with
              | I n -> (((AA_int n) :: targs''), args'')
              | _ -> (((AA_arg ty) :: targs''), (arg :: args'')))
           | Tfloat ->
             (match areg ae arg with
              | F n ->
                if generate_float_constants ()
                then (((AA_float n) :: targs''), args'')
                else (((AA_arg ty) :: targs''), (arg :: args''))
              | _ -> (((AA_arg ty) :: targs''), (arg :: args'')))
           | _ -> (((AA_arg ty) :: targs''), (arg :: args''))))
     | _ ->
       let (targs'', args'') = annot_strength_reduction ae targs' args in
       ((targ :: targs''), args''))

(** val builtin_strength_reduction :
    AE.t -> external_function -> reg list -> external_function * reg list **)

let builtin_strength_reduction ae ef args =
  match ef with
  | EF_vload chunk ->
    (match args with
     | [] -> (ef, args)
     | r1 :: l ->
       (match l with
        | [] ->
          (match areg ae r1 with
           | Ptr p ->
             (match p with
              | Gl (symb, n1) -> ((EF_vload_global (chunk, symb, n1)), [])
              | _ -> (ef, args))
           | _ -> (ef, args))
        | r :: l0 -> (ef, args)))
  | EF_vstore chunk ->
    (match args with
     | [] -> (ef, args)
     | r1 :: l ->
       (match l with
        | [] -> (ef, args)
        | r2 :: l0 ->
          (match l0 with
           | [] ->
             (match areg ae r1 with
              | Ptr p ->
                (match p with
                 | Gl (symb, n1) ->
                   ((EF_vstore_global (chunk, symb, n1)), (r2 :: []))
                 | _ -> (ef, args))
              | _ -> (ef, args))
           | r :: l1 -> (ef, args))))
  | EF_annot (text, targs) ->
    let (targs', args') = annot_strength_reduction ae targs args in
    ((EF_annot (text, targs')), args')
  | _ -> (ef, args)

(** val transf_instr :
    coq_function -> VA.t PMap.t -> romem -> node -> instruction ->
    instruction **)

let transf_instr f an rm pc instr =
  match PMap.get pc an with
  | VA.Bot -> instr
  | VA.State (ae, am) ->
    (match instr with
     | Iop (op, args, res, s) ->
       let aargs = aregs ae args in
       let a = eval_static_operation op aargs in
       let s' = successor f (AE.set res a ae) s in
       (match const_for_result a with
        | Some cop -> Iop (cop, [], res, s')
        | None ->
          let (op', args') = op_strength_reduction op args aargs in
          Iop (op', args', res, s'))
     | Iload (chunk, addr, args, dst, s) ->
       let aargs = aregs ae args in
       let a = loadv chunk rm am (eval_static_addressing addr aargs) in
       (match const_for_result a with
        | Some cop -> Iop (cop, [], dst, s)
        | None ->
          let (addr', args') = addr_strength_reduction addr args aargs in
          Iload (chunk, addr', args', dst, s))
     | Istore (chunk, addr, args, src, s) ->
       let aargs = aregs ae args in
       let (addr', args') = addr_strength_reduction addr args aargs in
       Istore (chunk, addr', args', src, s)
     | Icall (sig0, ros, args, res, s) ->
       Icall (sig0, (transf_ros ae ros), args, res, s)
     | Itailcall (sig0, ros, args) ->
       Itailcall (sig0, (transf_ros ae ros), args)
     | Ibuiltin (ef, args, res, s) ->
       let (ef', args') = builtin_strength_reduction ae ef args in
       Ibuiltin (ef', args', res, s)
     | Icond (cond, args, s1, s2) ->
       let aargs = aregs ae args in
       (match resolve_branch (eval_static_condition cond aargs) with
        | Some b -> if b then Inop s1 else Inop s2
        | None ->
          let (cond', args') = cond_strength_reduction cond args aargs in
          Icond (cond', args', s1, s2))
     | Ijumptable (arg, tbl) ->
       (match areg ae arg with
        | I n ->
          (match list_nth_z tbl (Int.unsigned n) with
           | Some s -> Inop s
           | None -> instr)
        | _ -> instr)
     | _ -> instr)

(** val transf_function : romem -> coq_function -> coq_function **)

let transf_function rm f =
  let an = analyze rm f in
  { fn_sig = f.fn_sig; fn_params = f.fn_params; fn_stacksize =
  f.fn_stacksize; fn_code = (PTree.map (transf_instr f an rm) f.fn_code);
  fn_entrypoint = f.fn_entrypoint }

(** val transf_fundef : romem -> fundef -> fundef **)

let transf_fundef rm fd =
  transf_fundef (transf_function rm) fd

(** val transf_program : program -> program **)

let transf_program p =
  let rm = romem_for_program p in transform_program (transf_fundef rm) p

