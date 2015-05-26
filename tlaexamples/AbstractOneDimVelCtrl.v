Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Import LibNotations.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

Module Type CtrlParameters.

  Parameter ub : R.
  Parameter ubX : Term.
  Parameter ubX_st : is_st_term ubX = true.
  Parameter d : R.
  Parameter Hd : (d > 0)%R.

End CtrlParameters.

Module AbstractOneDimCtrl (Import Params : CtrlParameters).

  Definition Evolve : Formula :=
    Continuous (["h"' ::= "v",
                 "v"' ::= 0,
                 "t"' ::= 1,
                 "H"' ::= 0,
                 "T"' ::= 0]).
Open Scope HP_scope.
  Definition Read : Formula :=
    "T"! = "t" /\ "H"! = "h".

  Definition Ctrl : Formula :=
    ("h" <= ub /\ ("h"-"H" <= ubX \/ "h"-"H" <= 0))
      --> ("h" + "v"!*d <= ub /\
           "v"!*d <= next_term ubX).

  Definition Next : Formula :=
       (Evolve /\ "t"! <= "T" + d /\
        ubX = next_term ubX)
    \/ (Ctrl /\ Read /\
        Unchanged (["h", "t"])).

  Definition Init : Formula :=
    "h" <= ub /\
    "h" + "v"*d <= ub /\
    "v"*d <= ubX /\
    "T" = "t" /\
    "H" = "h".

  Definition Ind_Inv : Formula :=
    "h"-"H" = "v"*("t"-"T") /\
    "v"*d <= ubX /\
    "H" + ("v"*d) <= ub /\
    "H" <= ub /\
    0 <= "t"-"T" <= d.

  Definition Safe : Formula :=
    "h" <= ub.

  Lemma ind_inv_init : |- Init --> Ind_Inv.
  Proof.
    pose proof (Hd).
    solve_linear;
    repeat match goal with
      | [ H : @eq R _ _ |- _ ] =>
        rewrite H
    end; solve_linear.
  Qed.

  Lemma ind_inv_safe : |- Ind_Inv --> Safe.
  Proof.
    pose proof (Hd).
    solve_linear;
    solve_nonlinear.
  Qed.

  Lemma safety :
    |- (Init /\ []Next) --> []Safe.
  Proof.
    apply imp_trans with (F2:=Ind_Inv /\ []Next).
    - apply and_right.
      + apply and_left1. apply ind_inv_init.
      + apply and_left2. apply imp_id.
    - apply imp_trans with (F2:=[]Ind_Inv).
      + apply inv_discr_ind;
        try solve [simpl; rewrite ubX_st; intuition].
        unfold Next, Evolve. pose proof Hd.
        Time prove_inductive.
        * match goal with
            | [ |- context [Continuous ?deqs] ] =>
              apply unchanged_continuous with (eqs:=deqs)
          end; solve_linear.
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H
                 end; solve_linear.
        * solve_linear;
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H
                 end; solve_linear.
        * solve_linear.
          destruct (Rle_dec (hd tr "v") R0);
            solve_nonlinear.
        * solve_linear.
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H
                 end.
          destruct (Rle_dec (hd tr "v") R0);
            solve_nonlinear.
        * solve_linear. 
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H
                 end.
          destruct (Rle_dec (hd tr "v") R0);
            solve_nonlinear.
      + apply always_imp. apply ind_inv_safe.
  Qed.

End AbstractOneDimCtrl.