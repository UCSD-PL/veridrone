Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Import LibNotations.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import TLA.ArithFacts.
Require Import TLA.Substitution.
Require Import Coq.Reals.Rdefinitions.

Open Scope HP_scope.
Open Scope string_scope.

Section Ctrl.

  (* Upper bound on velocity. *)
  Variable ub : R.
  (* Max time between executions of the
     controller. *)
  Variable d : R.
  Hypothesis d_gt_0 : (d > 0)%R.

  (* The continuous dynamics of the system *)
  Definition Evolve : Formula :=
    Continuous (["v"' ::= "a",
                 "a"' ::= 0,
                 "t"' ::= --1]).

  Definition Ctrl : Formula :=
       ("A"*d + "v" <= ub /\ "a"! = "A")
    \/ ("a"! <= 0).

  Definition Next : Formula :=
       (Evolve /\ "t"! >= 0)
    \/ (Ctrl /\ "t"! = d /\ Unchanged (["v"])).

  Definition Init : Formula :=
    "v" <= ub /\ "v" + "a"*d <= ub /\ 0 <= "t" <= d.

  Definition Sys : Formula :=
    Init /\ []Next.

  Definition Safe : Formula :=
    "v" <= ub.

  Definition IndInv : Formula :=
       ("a" <  0 --> Safe)
    /\ ("a" >= 0 --> "a"*"t" + "v" <= ub)
    /\ 0 <= "t" <= d.

  Theorem safety :
    |- Sys --> []Safe.
  Proof.
    apply imp_trans with (F2:=[]IndInv).
    - unfold Sys. apply imp_trans with (F2:=IndInv /\ []Next).
      + simpl; intuition; solve_nonlinear.
      + apply inv_discr_ind.
        * compute; tauto.
        * apply or_next.
          { unfold Evolve. prove_inductive. }
          { solve_nonlinear. }
    - apply always_imp. solve_nonlinear.
  Qed.

End Ctrl.
