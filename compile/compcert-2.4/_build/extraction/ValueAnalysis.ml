open AST
open BinInt
open BinNums
open Compopts
open Datatypes
open Globalenvs
open Kildall
open List0
open Liveness
open Maps
open Op
open RTL
open Registers
open ValueAOp
open ValueDomain

(** val areg : aenv -> reg -> aval **)

let areg ae r =
  AE.get r ae

(** val aregs : aenv -> reg list -> aval list **)

let aregs ae rl =
  map (areg ae) rl

(** val mafter_public_call : amem **)

let mafter_public_call =
  mtop

(** val mafter_private_call : amem -> amem **)

let mafter_private_call am_before =
  { am_stack = am_before.am_stack; am_glob = PTree.empty; am_nonstack =
    Nonstack; am_top = (plub am_before.am_stack.ab_summary Nonstack) }

(** val transfer_call : aenv -> amem -> reg list -> reg -> VA.t' **)

let transfer_call ae am args res =
  if (&&) (pincl am.am_nonstack Nonstack)
       (forallb (fun r -> vpincl (areg ae r) Nonstack) args)
  then VA.State ((AE.set res (Ifptr Nonstack) ae), (mafter_private_call am))
  else VA.State ((AE.set res coq_Vtop ae), mafter_public_call)

type builtin_kind =
| Builtin_vload of memory_chunk * aval
| Builtin_vstore of memory_chunk * aval * aval
| Builtin_memcpy of coq_Z * coq_Z * aval * aval
| Builtin_annot
| Builtin_annot_val of aval
| Builtin_default

(** val classify_builtin :
    external_function -> reg list -> aenv -> builtin_kind **)

let classify_builtin ef args ae =
  match ef with
  | EF_vload chunk ->
    (match args with
     | [] -> Builtin_default
     | a1 :: l ->
       (match l with
        | [] -> Builtin_vload (chunk, (areg ae a1))
        | r :: l0 -> Builtin_default))
  | EF_vstore chunk ->
    (match args with
     | [] -> Builtin_default
     | a1 :: l ->
       (match l with
        | [] -> Builtin_default
        | a2 :: l0 ->
          (match l0 with
           | [] -> Builtin_vstore (chunk, (areg ae a1), (areg ae a2))
           | r :: l1 -> Builtin_default)))
  | EF_vload_global (chunk, id, ofs) ->
    (match args with
     | [] -> Builtin_vload (chunk, (Ptr (Gl (id, ofs))))
     | r :: l -> Builtin_default)
  | EF_vstore_global (chunk, id, ofs) ->
    (match args with
     | [] -> Builtin_default
     | a1 :: l ->
       (match l with
        | [] -> Builtin_vstore (chunk, (Ptr (Gl (id, ofs))), (areg ae a1))
        | r :: l0 -> Builtin_default))
  | EF_memcpy (sz, al) ->
    (match args with
     | [] -> Builtin_default
     | a1 :: l ->
       (match l with
        | [] -> Builtin_default
        | a2 :: l0 ->
          (match l0 with
           | [] -> Builtin_memcpy (sz, al, (areg ae a1), (areg ae a2))
           | r :: l1 -> Builtin_default)))
  | EF_annot (text, targs) -> Builtin_annot
  | EF_annot_val (text, targ) ->
    (match args with
     | [] -> Builtin_default
     | a1 :: l ->
       (match l with
        | [] -> Builtin_annot_val (areg ae a1)
        | r :: l0 -> Builtin_default))
  | _ -> Builtin_default

(** val transfer_builtin :
    aenv -> amem -> romem -> external_function -> reg list -> reg -> VA.t' **)

let transfer_builtin ae am rm ef args res =
  match classify_builtin ef args ae with
  | Builtin_vload (chunk, aaddr0) ->
    let a =
      if va_strict ()
      then vlub (loadv chunk rm am aaddr0) (vnormalize chunk (Ifptr Glob))
      else vnormalize chunk coq_Vtop
    in
    VA.State ((AE.set res a ae), am)
  | Builtin_vstore (chunk, aaddr0, av) ->
    let am' = storev chunk am aaddr0 av in
    VA.State ((AE.set res itop ae), (mlub am am'))
  | Builtin_memcpy (sz, al, adst, asrc) ->
    let p = loadbytes am rm (aptr_of_aval asrc) in
    let am' = storebytes am (aptr_of_aval adst) sz p in
    VA.State ((AE.set res itop ae), am')
  | Builtin_annot -> VA.State ((AE.set res itop ae), am)
  | Builtin_annot_val av -> VA.State ((AE.set res av ae), am)
  | Builtin_default -> transfer_call ae am args res

(** val transfer : coq_function -> romem -> node -> aenv -> amem -> VA.t **)

let transfer f rm pc ae am =
  match PTree.get pc f.fn_code with
  | Some i ->
    (match i with
     | Iop (op, args, res, s) ->
       let a = eval_static_operation op (aregs ae args) in
       VA.State ((AE.set res a ae), am)
     | Iload (chunk, addr, args, dst, s) ->
       let a =
         loadv chunk rm am (eval_static_addressing addr (aregs ae args))
       in
       VA.State ((AE.set dst a ae), am)
     | Istore (chunk, addr, args, src, s) ->
       let am' =
         storev chunk am (eval_static_addressing addr (aregs ae args))
           (areg ae src)
       in
       VA.State (ae, am')
     | Icall (sig0, ros, args, res, s) -> transfer_call ae am args res
     | Itailcall (sig0, ros, args) -> VA.Bot
     | Ibuiltin (ef, args, res, s) -> transfer_builtin ae am rm ef args res
     | Ireturn arg -> VA.Bot
     | _ -> VA.State (ae, am))
  | None -> VA.Bot

(** val transfer' :
    coq_function -> reg list PTree.t -> romem -> node -> VA.t -> VA.t **)

let transfer' f lastuses rm pc = function
| VA.Bot -> VA.Bot
| VA.State (ae, am) ->
  (match transfer f rm pc ae am with
   | VA.Bot -> VA.Bot
   | VA.State (ae', am') ->
     let ae'' =
       match PTree.get pc lastuses with
       | Some regs -> eforget regs ae'
       | None -> ae'
     in
     VA.State (ae'', am'))

module DS = Dataflow_Solver(VA)(NodeSetForward)

(** val mfunction_entry : amem **)

let mfunction_entry =
  { am_stack = (ablock_init Pbot); am_glob = PTree.empty; am_nonstack =
    Nonstack; am_top = Nonstack }

(** val analyze : romem -> coq_function -> VA.t PMap.t **)

let analyze rm f =
  let lu = last_uses f in
  let entry = VA.State ((einit_regs f.fn_params), mfunction_entry) in
  (match DS.fixpoint f.fn_code successors_instr (transfer' f lu rm)
           f.fn_entrypoint entry with
   | Some res -> res
   | None -> PMap.init (VA.State (AE.top, mtop)))

(** val store_init_data : ablock -> coq_Z -> init_data -> ablock **)

let store_init_data ab p = function
| Init_int8 n -> ablock_store Mint8unsigned ab p (I n)
| Init_int16 n -> ablock_store Mint16unsigned ab p (I n)
| Init_int32 n -> ablock_store Mint32 ab p (I n)
| Init_int64 n -> ablock_store Mint64 ab p (L n)
| Init_float32 n ->
  ablock_store Mfloat32 ab p
    (if propagate_float_constants () then FS n else ftop)
| Init_float64 n ->
  ablock_store Mfloat64 ab p
    (if propagate_float_constants () then F n else ftop)
| Init_space n -> ab
| Init_addrof (symb, ofs) -> ablock_store Mint32 ab p (Ptr (Gl (symb, ofs)))

(** val store_init_data_list :
    ablock -> coq_Z -> init_data list -> ablock **)

let rec store_init_data_list ab p = function
| [] -> ab
| id :: idl' ->
  store_init_data_list (store_init_data ab p id)
    (Z.add p (Genv.init_data_size id)) idl'

(** val alloc_global : romem -> (ident * (fundef, unit) globdef) -> romem **)

let alloc_global rm = function
| (id, g) ->
  (match g with
   | Gfun f -> PTree.remove id rm
   | Gvar v ->
     if (&&) v.gvar_readonly (negb v.gvar_volatile)
     then PTree.set id
            (store_init_data_list (ablock_init Pbot) Z0 v.gvar_init) rm
     else PTree.remove id rm)

(** val romem_for_program : program -> romem **)

let romem_for_program p =
  fold_left alloc_global p.prog_defs PTree.empty

(** val avalue : VA.t -> reg -> aval **)

let avalue a r =
  match a with
  | VA.Bot -> Vbot
  | VA.State (ae, am) -> AE.get r ae

(** val aaddr : VA.t -> reg -> aptr **)

let aaddr a r =
  match a with
  | VA.Bot -> Pbot
  | VA.State (ae, am) -> aptr_of_aval (AE.get r ae)

(** val aaddressing : VA.t -> addressing -> reg list -> aptr **)

let aaddressing a addr args =
  match a with
  | VA.Bot -> Pbot
  | VA.State (ae, am) ->
    aptr_of_aval (eval_static_addressing addr (aregs ae args))

