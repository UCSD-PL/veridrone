Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import Modules.AbstractOneDimCtrl.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

Module Params <: CtrlParameters.

  Variable d : R.
  Hypothesis Hd : (d > 0)%R.

  Definition ub := d%R.
  Definition ubX : Term := d.
  Definition ubX_st : is_st_term ubX = true := eq_refl _.

End Params.

Import Params.

Module AbstractCtrl := AbstractOneDimCtrl(Params).

Section Ctrl.

  Variable dinv : R.
  Hypothesis Hdinv : (@eq R (d * dinv) 1)%R.

  Definition Read : Formula :=
    "T"! = "t" /\ "H"! = "h".

  Definition Evolve : Formula :=
    Continuous (["h"' ::= "v",
                 "v"' ::= 0,
                 "t"' ::= 1,
                 "H"' ::= 0,
                 "T"' ::= 0]).

  Definition Ctrl : Formula :=
       (--d <= "H" /\ "v"! = --"H"*dinv)
    \/ ("H" < --d /\ "v"! = 1).

  Definition Next : Formula :=
       (Evolve /\ "t"! <= "T" + d)
    \/ (Ctrl /\ Read /\ Unchanged (["h", "t"])).

  Definition Init : Formula :=
       "v" <= 1
    /\ "h" <= d
    /\ "h" + "v"*d <= d
    /\ "t" = "T"
    /\ "H" = "h".

  Definition Safe : Formula :=
    "h" <= d.

  Lemma refinement :
    |- (Init /\ []Next)
         --> (AbstractCtrl.Init /\ []AbstractCtrl.Next).
  Proof.
    pose Hd.
    apply and_right.
    - apply and_left1.
      solve_linear;
        repeat match goal with
                 | [ H : @eq R _ _ |- _ ] =>
                   rewrite H
               end; solve_linear.
      rewrite <- Rmult_1_l.
      solve_nonlinear.
    - apply and_left2. apply always_imp.
      repeat apply or_left.
      + unfold Evolve. apply or_right1.
        repeat apply and_right.
        * apply and_left1. apply imp_id.
        * apply and_left2. apply imp_id.
        * match goal with
            | [ |- context [Continuous ?deqs] ] =>
              apply unchanged_continuous with (eqs:=deqs)
          end; solve_linear.
      + apply or_right2.
        solve_linear;
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H
                 end; solve_linear;
          unfold ub in *; solve_linear.
        * rewrite Rmult_assoc. rewrite Rmult_comm in Hdinv.
          rewrite Hdinv. solve_linear.
        * rewrite Rmult_assoc. rewrite Rmult_comm in Hdinv.
          rewrite Hdinv. solve_linear.
        * rewrite Rmult_assoc. rewrite Rmult_comm in Hdinv.
          rewrite Hdinv. solve_linear.
        * rewrite Rmult_assoc. rewrite Rmult_comm in Hdinv.
          rewrite Hdinv. solve_linear.
  Qed.

  Lemma safety :
    |- (Init /\ []Next) --> []Safe.
  Proof.
    apply imp_trans
    with (F2:=AbstractCtrl.Init /\ []AbstractCtrl.Next).
    - apply refinement.
    - apply AbstractCtrl.safety.
  Qed.

End Ctrl.