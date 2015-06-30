Require Import Z3.Tactic.
Require Import Coq.Strings.String.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Goal forall A B : Prop, A /\ B -> B.
Proof.
  intros.
  z3 solve.
  tauto.
Qed.

Local Open Scope R_scope.

Goal forall x : R, x < 0 -> x + x < x.
Proof.
  intros.
  z3 solve.
Abort.

Goal forall x : R, ~(x = -1).
Proof.
  intros.
  Fail z3 solve.
Abort.

Goal forall x : R, ~(x = 1).
Proof.
  intros.
  Fail z3 solve.
Abort.