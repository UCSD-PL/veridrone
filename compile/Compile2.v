Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Ctypes.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.Tactics.
Require Import String.
Require Import List.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.EitherMonad.

Require Import compcert.flocq.Core.Fcore_defs.

Local Open Scope string_scope.

Print TLA.Syntax.Term.

(* Term, sans the next operator *)
Inductive NowTerm : Type :=
| VarNowN : Var -> NowTerm
| NatN : nat -> NowTerm
| RealN : Rdefinitions.R -> NowTerm
| PlusN : NowTerm -> NowTerm -> NowTerm
| MinusN : NowTerm -> NowTerm -> NowTerm
| MultN : NowTerm -> NowTerm -> NowTerm.

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
Record progr_stmt : Set :=
  mk_progr_stmt {
      assns : list (Var * Term);
      conds : list FlatFormula
    }.

Definition progr : Set := list progr_stmt.

(* definition of trace *)
Require Import compcert.common.Events.
Require Import compcert.cfrontend.ClightBigstep.

Definition progr_stmt_to_tla (ps : progr_stmt) : Formula :=
  match ps with
    | mk_progr_stmt assns conds =>
      let convert_assn (var_term : Var * Term) :=
          let (var, term) := var_term in
          Comp (VarNextT var) term Eq
      in
      let conjuncts :=
          List.app (List.map convert_assn assns) (List.map deflatten_formula conds) in
      match conjuncts with
        | nil => FALSE   (* if program statement is empty, it is an empty disjunct -> FALSE *)
        | c :: cs => 
          List.fold_right And c cs
      end
  end.

Definition progr_to_tla (pr : progr) : Formula :=
  let disjuncts :=
      List.map progr_stmt_to_tla pr in
  match disjuncts with
    | nil => FALSE    (* if there is no program, there should be no behavior *)
    | d :: ds =>
      List.fold_right Or d ds
  end.

Import ListNotations.

Definition derp : progr :=
  (mk_progr_stmt (("ab", RealT 1) :: nil) (FTRUE :: (FComp (NatN 1) (NatN 1) Eq ) :: nil)) :: nil.
     
Eval compute in (progr_to_tla derp).

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
                            
