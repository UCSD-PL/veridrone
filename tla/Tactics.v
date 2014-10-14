Require Import Coq.micromega.Psatz.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import Rdefinitions.

Ltac solve_linear :=
  simpl; intros; unfold eval_comp in *;
  simpl in *; intuition; try psatzl R.