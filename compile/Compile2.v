Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.lib.Integers.
Require Import Coq.Reals.Rdefinitions.
Require Import List.
Import ListNotations.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.Tactics.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Traversable. (* for sequence function *)
Require Import ExtLib.Data.List.
Require Import compcert.flocq.Core.Fcore_defs.
Require Import compcert.flocq.Appli.Fappli_IEEE.
Require Import compcert.flocq.Appli.Fappli_IEEE_bits.
Locate ident.
Local Close Scope HP_scope.
Delimit Scope SrcLang_scope with SL.
Local Open Scope SrcLang_scope.

Locate mkprogram.

(* Term, sans the next operator *)
Inductive NowTerm : Type :=
| VarNowN : Var -> NowTerm
| NatN : nat -> NowTerm
(*| RealN : Rdefinitions.R -> NowTerm*)
| FloatN : Floats.float -> NowTerm
| PlusN : NowTerm -> NowTerm -> NowTerm
| MinusN : NowTerm -> NowTerm -> NowTerm
| MultN : NowTerm -> NowTerm -> NowTerm.

(* peeled from Haskell, because it's beautiful *)
Definition app {A B: Type} (f : A -> B) (x : A) : B := f x.
Notation "f $ x" := (app f x) (at level 99, right associativity).

(* peeled from Syntax.v *)
Infix "+" := (PlusN) : SrcLang_scope.
Infix "-" := (MinusN) : SrcLang_scope.
Notation "-- x" := (MinusN (FloatN 0) x)
                     (at level 0) : SrcLang_scope.
Infix "*" := (MultN) : SrcLang_scope.

(* convenient coercions between number formats *)
Definition nat_to_int (n : nat) : int :=
  Int.repr $ Z.of_nat n.

Definition nat_to_float (n : nat) : Floats.float :=
  Floats.Float.of_int $ nat_to_int n.

Coercion nat_to_int : nat >-> int.
Coercion nat_to_float : nat >-> Floats.float.
Coercion Pos.of_nat : nat >-> positive.

Fixpoint pow (t : NowTerm) (n : nat) :=
  match n with
  | O => FloatN 1
  | S n => MultN t (pow t n)
  end.
Notation "t ^^ n" := (pow t n) (at level 10) : SrcLang_scope.

(* we probably need to define more convenience methods/notations
   for this representation *)
Fixpoint denowify (nt : NowTerm) : Term :=
  match nt with
    | VarNowN v => VarNowT v
    | NatN n => NatT n
    | FloatN f => RealT $ B2R _ _ f
    | PlusN t1 t2 => PlusT (denowify t1) (denowify t2)
    | MinusN t1 t2 => MinusT (denowify t1) (denowify t2)
    | MultN t1 t2 => MultT (denowify t1) (denowify t2)
  end.

(* Formula, sans the things we don't need to worry about
   compiling, and without and and or *)
Inductive FlatFormula :=
| FTRUE : FlatFormula
| FFALSE : FlatFormula
| FComp : NowTerm -> NowTerm -> CompOp -> FlatFormula.

(* Comparisons *)
Notation "t1 > t2" := (FComp t1 t2 Gt) : SrcLang_scope.
Notation "t1 >= t2" := (FComp t1 t2 Ge) : SrcLang_scope.
Notation "t1 < t2" := (FComp t1 t2 Lt) : SrcLang_scope.
Notation "t1 <= t2" := (FComp t1 t2 Le) : SrcLang_scope.
Notation "t1 = t2" := (FComp t1 t2 Eq) : SrcLang_scope.
Notation "x <= y <= z" :=
  (And (FComp x y Le) (FComp y z Le)) : SrcLang_scope.

(* Convert a formula to a flat one *)
(*Definition flatten_formula (tla : Formula) : option FlatFormula :=
  match tla with
    | TRUE => Some FTRUE
    | FALSE => Some FFALSE
    | Comp a b c => Some (FComp a b c)
    | _ => None
  end.*)

Definition deflatten_formula (ff : FlatFormula) : Formula :=
  match ff with
    | FTRUE => TRUE
    | FFALSE => FALSE
    | FComp a b c => Comp (denowify a) (denowify b) c
  end.

(* Captures the structure we want each term in our IR to have
   Basically, a list of simultaneous assignments, and a
   list of conditions guarding (all of) those assigments.
   Our program will be a list of these statements. *)

(* eventually this will be our IR, using "unknown" to account for possibility
   of e.g. rounding errors *)

(*
Record progr_stmt : Set :=
  mk_progr_stmt {
      conds : list FlatFormula;
      yes_assns : list (Var * NowTerm);
      unknown_assns : list (Var * NowTerm)
    }.
*)

Record progr_assn : Set :=
  mk_progr_assn {
      pa_dest : Var;
      pa_source : NowTerm
    }.

(* for now we omit "unknown" case for simplicity *)
Record progr_stmt : Set :=
  mk_progr_stmt {
      ps_conds : list FlatFormula;
      ps_assns : list progr_assn
    }.

Notation "a !!= b" := (mk_progr_assn a b) (at level 40) : SrcLang_scope.

Notation "'PIF' cs 'PTHEN' yas" :=
  (mk_progr_stmt cs yas) (at level 60) : SrcLang_scope.

(*
Notation "'PIF' cs 'PTHEN' yas 'PUNKNOWN' unas" := 
  (mk_progr_stmt cs yas unas) (at level 59).
*)
Check (PIF nil PTHEN nil).

Definition progr : Set := list progr_stmt.

(* definition of trace *)
Require Import compcert.common.Events.
Require Import compcert.cfrontend.ClightBigstep.

(* Fold a list with its first element as starting accumulator
   Takes function and list, as well as default element to return if list is nil *)
Definition self_foldr {A : Type} (f : A -> A -> A) (l : list A) (dflt : A) : A :=
  match l with
    | nil => dflt
    | h :: t =>
      List.fold_right f h t
  end.

Definition progr_stmt_to_tla (ps : progr_stmt) : Formula :=
  match ps with
    | mk_progr_stmt conds assns =>
      let convert_assn (assn : progr_assn) :=
          match assn with
            | mk_progr_assn var term => Comp (VarNextT var) (denowify term) Eq
          end
      in
      let conjuncts :=
          List.app (List.map convert_assn assns) (List.map deflatten_formula conds) in
      self_foldr And conjuncts FALSE
  end.

Definition progr_to_tla (pr : progr) : Formula :=
  let disjuncts :=
      List.map progr_stmt_to_tla pr in
  self_foldr Or disjuncts FALSE.

Require Import compcert.lib.Integers.

Local Open Scope string_scope.

Definition derp : progr :=
  ([PIF (FTRUE  ::
        (NatN 1 = NatN 1) :: nil)
   PTHEN ["ab" !!= FloatN 1]])%SL.

(* This hides the nastiness of the definition of B2R, but I don't think it's a long term solution
   In the long run we're going to have to figure out how to deal with converting from real numbers
   into floating point. There's no easy way to go back. *)
Opaque B2R.
Eval compute in (progr_to_tla derp).

(* bool type in C, briefly *)
Locate Tint.
Definition c_bool : type :=
  Tint IBool Signed noattr.

Definition c_float : type :=
  Tfloat F64 noattr.

(* "And" operator in C, briefly *)
Definition c_and (e1 e2 : expr) : expr :=
  Ebinop Oand e1 e2 c_bool.

(* "true" constant in C, briefly *)
Definition c_true : expr.
  refine (Econst_int (Int.mkint 1 _) c_bool).
  compute. auto.
Qed.

(* "false" constant in C, briefly *)  
Definition c_false : expr.
  refine (Econst_int (Int.mkint 0 _) c_bool).
  compute. auto.
Qed.

(* This is going to give us "backwards" place-values for string indices
   but it's not a big deal as long as we do it consistently. *)
(* Also, please don't use null characters or empty strings, these are likely to cause
   problems *)
(*Fixpoint tlavar2N (tlav : Var) : N :=
  match tlav with
    | EmptyString => 0%N
    | String ch rest => 
      let place := N_of_ascii ch in
      (place + 256 * (tlavar2N rest))%N
  end.*)

(*Definition tlavar2c (tlav : Var) : AST.ident :=
  N.succ_pos (tlavar2N tlav).

Definition cvar2tla (id : AST.ident) : Var :=
  Nvar2tla (Pos.pred_N id).*)

(* varmap-state *)
Definition VMS := state (list Var).

(* Utility function for doing lookup in a variable map
   If found, returns the same map and the index of the variable
   Otherwise, returns a new map with variable appended, and new index *)

Import MonadNotation.
Local Open Scope monad.
Require Import String.
(* monadic, but well-formed recursion is not evident *)
(*
Fixpoint lookup_or_add (v : Var) : VMS positive :=
  vm <- get;;
  match vm with
    | nil => put [v];;
             ret 1
    | v1 :: vm' =>
      if (string_dec v v1) then ret 1
      else
        put vm';;
        idx <- lookup_or_add v;;
        vm'' <- get;;
        put (v1 :: vm'');;
        ret (idx + 1)
  end.
 *)

Fixpoint lookup_or_add' (v : Var) (varmap : list Var) : (positive * list Var) :=
  match varmap with
    | nil => (1%positive, v :: nil)
    | v1 :: varmap' =>
      if (string_dec v v1) then
        (1%positive, varmap)
      else
  (* if we can't find it at head, look in tail, then increment index *)
        let (idx, vm') := lookup_or_add' v varmap' in
        ((idx + 1)%positive, v1 :: vm')
  end.

Definition lookup_or_add (v : Var) : VMS positive :=
  vm <- get;;
  let (idx, vm') := lookup_or_add' v vm in
  put vm';;
  ret idx.

(* Helper routines for converting from source language to C *)
Fixpoint nowTerm_to_clight (nt : NowTerm) : VMS expr :=
  match nt with
    | VarNowN var =>
      idx <- lookup_or_add var;;
      ret $ Evar idx c_float
    | NatN n =>
      ret $ Econst_float (nat_to_float n) c_float
    | FloatN f =>
      ret $ Econst_float f c_float
    | PlusN nt1 nt2 =>
      clnt1 <- nowTerm_to_clight nt1;;
      clnt2 <- nowTerm_to_clight nt2;;
      ret $ Ebinop Oadd clnt1 clnt2 c_float
    | MinusN nt1 nt2 =>
      clnt1 <- nowTerm_to_clight nt1;;
      clnt2 <- nowTerm_to_clight nt2;;
      ret $ Ebinop Osub clnt1 clnt2 c_float
    | MultN nt1 nt2 =>
      clnt1 <- nowTerm_to_clight nt1;;
      clnt2 <- nowTerm_to_clight nt2;;
      ret $ Ebinop Omul clnt1 clnt2 c_float
  end.

Definition progr_assn_to_clight (assn : progr_assn) : VMS statement :=
  match assn with
    | mk_progr_assn dst src =>
      dst_idx <- lookup_or_add dst;;
      rhs <- nowTerm_to_clight src;;
      ret $ Sassign (Evar dst_idx c_float) rhs
  end.

Definition compOp_to_binop (cmp : CompOp) : binary_operation :=
  match cmp with
    | Gt => Ogt
    | Ge => Oge
    | Lt => Olt
    | Le => Ole
    | Eq => Oeq
  end.

Definition flatFormula_to_clight (ff : FlatFormula) : VMS expr :=
  match ff with
    | FTRUE => ret c_true
    | FFALSE => ret c_false
    | FComp nt1 nt2 cmp =>
      clnt1 <- nowTerm_to_clight nt1;;
      clnt2 <- nowTerm_to_clight nt2;;
      ret $ Ebinop (compOp_to_binop cmp) clnt1 clnt2 c_bool
  end.

(* TODO define mapM function. I don't want to take the time right now to figure
   out its fully general type signature... *)

(* converts a single progr_stmt to an "if" statement in Clight *)
(* in the process, builds up a table mapping source-language variable names
   to target-language positive indices *)
Definition progr_stmt_to_clight (ps : progr_stmt) : VMS statement :=
  match ps with
    | mk_progr_stmt conds assns =>      
      let convd_conds := map flatFormula_to_clight conds in
      let convd_assns := map progr_assn_to_clight assns in
      cconds <- sequence convd_conds;;
      cassns <- sequence convd_assns;;
      let if_condition :=
          self_foldr (fun l r => Ebinop Oand l r c_bool) cconds c_false
      in
      let if_body :=
          self_foldr Ssequence cassns Sskip
      in
      ret $ Sifthenelse if_condition if_body Sskip
  end.  

(*
Definition progr_stmt_to_clight (ps : progr_stmt) (varmap : list Var) : (statement * list Var) :=
  match ps with
    | mk_progr_stmt conds assns =>
      let convert_assn (assn : progr_assn) : statement :=
          match assn with
            | mk_progr_assn dst src => Sassign dst src
          end
      in
      let convert_cond (cond : FlatFormula
      let condition := self_foldr c_and (List.map convert_cond conds) c_true in
      let body := self_foldr Ssequence (List.map convert_assn assns) Sskip in
      Sifthenelse condition body Sskip
  end.
*)

(* needed for correctly packing into the function record *)
(* for now we cheat because all our variables are floats. In the long run we
   may not be able to get away with this and may need to start including types
   in the var-map *)
Fixpoint varmap_to_typed_idents (vm : list Var) (p : positive) : list (AST.ident * type) :=
  match vm with
    | nil => nil
    | _ :: vm' =>
      (p, c_float) :: varmap_to_typed_idents vm' (p + 1)%positive
  end.  

(* this function probably exists somewhere else *)
Definition ltail {A : Type} (l : list A) : list A :=
  match l with
    | nil => nil
    | _ :: t => t
  end.

(* almost there - first, define a helper function that computes the program
   within the state monad *)
Definition progr_to_clight' (pr : progr) : VMS program :=
  prog_stmts <- sequence $ map progr_stmt_to_clight pr;;
  vm <- get;;
  let prog_body := self_foldr Ssequence prog_stmts Sskip in
  (* now we need to pack the program structure appropriately *)
  let funrec :=
      {| (* no return now; that may change *)
         fn_return := Tvoid;
         fn_callconv := AST.cc_default;
         (* no params right now; that may change *)
         fn_params := nil;
         (* main is number 1 so rest of vars must start at 2 *)
         fn_vars := varmap_to_typed_idents (ltail vm) 2%positive;
         fn_temps := nil;
         fn_body := prog_body
      |}
  in
  let globdefs :=
      [(1%positive, AST.Gfun (Internal funrec))]
  in
  let main_id := 1%positive in
  ret $ AST.mkprogram globdefs main_id.

Definition progr_to_clight (pr : progr) : (program) :=
  let pVMS := progr_to_clight' pr in
  let init_state := ["__main"] in
  evalState pVMS init_state.

(* Convert string into list of chars *)
Require Import String.
Check String.String.
Fixpoint str_to_nats (s : String.string) : list nat :=
  match s with
    | String.String a s' =>
      (nat_of_ascii a) :: (str_to_nats s')
    | EmptyString => nil
  end.

Eval compute in (str_to_nats "abcd").
Definition test11 := str_to_nats "abcd".

(* Convert var list for easier input into pretty printer
   Which expects a hash table from positive -> string.
   We do the hashtable conversion in ML. *)

Fixpoint convert_var_list' (l : list Var) (p : positive) : list (positive * (list nat)) :=
  match l with
    | nil => nil
    | h :: t =>
      (p, str_to_nats h) :: convert_var_list' t (p + 1)%positive
  end.

Definition convert_var_list (l : list Var) : list (positive * (list nat)) :=
  convert_var_list' l 1%positive.

(* Emit program and converted version of its var list *)
Definition prepare_pretty_print (pr : progr) : (program * list (positive * list nat)) :=
  let (prog, vars) := runState (progr_to_clight' pr) ["__main"] in
  (prog, convert_var_list vars).

(* You have to unpack and repack because I have no idea how to unpack Coq pairs in Ocaml >:( *)
(*Definition cfst := @fst (positive * list nat).
Definition csnd := @snd (positive * list nat).*)

Definition hi t :=
  evalState (nowTerm_to_clight t).

Check hi.

Definition ex_derp_prog := fst (prepare_pretty_print derp).
Definition ex_derp_vars := snd (prepare_pretty_print derp).
Definition coqmap := map.
(* Package everything upto extract it all at once *)
Definition extract_derp := (ex_derp_prog, ex_derp_vars, coqmap).
Extraction "derp.ml" extract_derp.

Check fold_right.

Eval compute in (progr_to_clight derp).
Print binary_float.
Check Econst_float.

Check bigstep_semantics.
Locate bigstep_semantics.
Print bigstep_semantics.
Print Smallstep.bigstep_semantics.
(* for now, assume output program not divergent *)
(* these take a default state to fill in if compcert trace contains
   a state that's meaningless in TLA *)
Axiom trans_trace_fin : compcert.common.Events.trace -> state -> TLA.Semantics.trace.
Axiom trans_trace_inf : compcert.common.Events.traceinf -> state -> TLA.Semantics.trace.

(* to support non-divergent programs we just need to change this to trace*)
(* statement that if a progr compiles to a divergent C program, the (infinite) trace
   will be identical to the TLA version of the trace *)
Theorem compile_correct : forall (p : progr) (tri : compcert.common.Events.traceinf)
                                 (s : state),
                            bigstep_program_diverges (progr_to_clight p) tri ->
                            eval_formula (progr_to_tla p) (trans_trace_inf tri s).

                            
(* Theorem compile_correct2: 
                            bigstep_program_terminates
                              (progr_to_clight p) (trans_trace_fin tr) retcode /\ *)
                            
