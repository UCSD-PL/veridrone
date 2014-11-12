Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.


Section AbstractOneDimCtrl.

  Variable ub : R.
  Variable ubX : Term.
  Hypothesis ubX_st : is_st_term ubX = true.
  Variable d : R.
  (* The following hypothesis is not necessary
     for the safety property, but it's necessary
     for ensuring that non-Zeno behaviors are
     possible. *)
  Hypothesis Hd : (d > 0)%R.

  Definition Evolve : Formula :=
    Continuous (["x"' ::= "v",
                 "v"' ::= 0,
                 "t"' ::= 1,
                 "T"' ::= 0,
                 "X"' ::= 0]).

  Definition Read : Formula :=
    "T"! = "t" /\ "X"! = "x".

  Definition Ctrl : Formula :=
    ("x" <= ub /\ ("x"-"X" <= ubX \/ "x"-"X" <= 0))
      --> ("x" + "v"!*d <= ub /\
           "v"!*d <= next_term ubX).

  Definition Next : Formula :=
       (Evolve /\ "t"! <= "T" + d /\
        ubX = next_term ubX)
    \/ (Ctrl /\ Read /\
        Unchanged (["x", "t"])).

  Definition Init : Formula :=
    "x" <= ub /\
    "x" + "v"*d <= ub /\
    "v"*d <= ubX /\
    "T" = "t" /\
    "X" = "x".

  Definition Ind_Inv : Formula :=
    "x"-"X" = "v"*("t"-"T") /\
    "v"*d <= ubX /\
    "X" + ("v"*d) <= ub /\
    "X" <= ub /\
    0 <= "t"-"T" <= d.

  Definition Safe : Formula :=
    "x" <= ub.

  Lemma ind_inv_init : |- Init --> Ind_Inv.
  Proof.
    solve_linear;
    repeat match goal with
      | [ H : @eq R _ _ |- _ ] =>
        rewrite H
    end; solve_linear.
  Qed.

  Lemma ind_inv_safe : |- Ind_Inv --> Safe.
  Proof.
    solve_linear; solve_nonlinear.
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
        try solve [simpl; rewrite ubX_st; auto].
        unfold Next, Evolve.
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