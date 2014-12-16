Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.lib.Integers.
Require Import Coq.Reals.Rdefinitions.
Require Import List.
Import ListNotations.

Require Import TLA.Syntax.
Require Import TLA.Semantics.
(* not importing these for now because of list notation conflicts *)
(*Require Import TLA.Lib.*)
(*Require Import TLA.Tactics.*)
Require Import String.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import compcert.flocq.Core.Fcore_defs.

Local Close Scope HP_scope.
Delimit Scope SrcLang_scope with SL.
Local Open Scope SrcLang_scope.


(* Term, sans the next operator *)
Inductive NowTerm : Type :=
| VarNowN : Var -> NowTerm
| NatN : nat -> NowTerm
| RealN : Rdefinitions.R -> NowTerm
| PlusN : NowTerm -> NowTerm -> NowTerm
| MinusN : NowTerm -> NowTerm -> NowTerm
| MultN : NowTerm -> NowTerm -> NowTerm.

(* peeled from Syntax.v *)
Infix "+" := (PlusN) : SrcLang_scope.
Infix "-" := (MinusN) : SrcLang_scope.
Notation "-- x" := (MinusN (RealN R0) x)
                     (at level 0) : SrcLang_scope.
Infix "*" := (MultN) : SrcLang_scope.
Fixpoint pow (t : NowTerm) (n : nat) :=
  match n with
  | O => RealN 1
  | S n => MultN t (pow t n)
  end.
Notation "t ^^ n" := (pow t n) (at level 10) : SrcLang_scope.

(* we probably need to define more convenience methods/notations
   for this representation *)
Fixpoint denowify (nt : NowTerm) : Term :=
  match nt with
    | VarNowN v => VarNowT v
    | NatN n => NatT n
    | RealN r => RealT r
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

Check List.fold_right.

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
  [PIF [FTRUE; NatN 1 = NatN 1]
   PTHEN ["ab" !!= RealN 1]].
     
Eval compute in (progr_to_tla derp).

(* bool type in C, briefly *)
Definition c_bool : type :=
  Tint IBool Signed noattr.

(* "And" operator in C, briefly *)
Definition c_and (e1 e2 : expr) : expr :=
  Ebinop Oand e1 e2 c_bool.

(* "true" constant in C, briefly *)
Definition c_true : expr.
  refine (Econst_int (Int.mkint 1 _) c_bool).
  compute. auto.
Qed.  

(* Utility function for doing lookup in a variable map
   If found, returns the same map and the index of the variable
   Otherwise, returns a new map with variable appended, and new index *)
Local Open Scope positive.
Fixpoint lookup_or_add (v : Var) (varmap : list Var) : (positive * list Var) :=
  match varmap with
    | nil => (1, v :: nil)
    | v1 :: varmap' =>
      if (string_dec v v1) then
        (1, varmap)
      else
  (* if we can't find it at head, look in tail, then increment index *)
        let (idx, vm') := lookup_or_add v varmap' in
        (idx + 1, v1 :: vm')
  end.

(* converts a single progr_stmt to an "if" statement in Clight *)
(* in the process, builds up a table mapping source-language variable names
   to target-language positive indices *)
(* we probably need a state monad at this point... *)
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

Axiom progr_to_clight : progr -> program.
Check bigstep_semantics.
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
                            
