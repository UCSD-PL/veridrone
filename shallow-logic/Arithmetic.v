Require Import Coq.Classes.RelationClasses.
Require Import Setoid Relation_Definitions.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rtrigo_def.

Global Instance Reflexive_Rge : Reflexive Rge.
Proof.
  red. intro. apply Req_ge. reflexivity.
Qed.

Global Instance Reflexive_Rle : Reflexive Rle.
Proof.
  red. intro. apply Req_ge. reflexivity.
Qed.
Global Instance Transitive_Rge : Transitive Rge.
Proof.
  red. intros. eapply Rge_trans; eauto.
Qed.

Global Instance Transitive_Rle : Transitive Rle.
Proof.
  red. intros. eapply Rle_trans; eauto.
Qed.

Local Open Scope R.

Add Parametric Relation : R Rle
reflexivity proved by Rle_refl
transitivity proved by Rle_trans
as Rle_setoid_relation.

Add Parametric Morphism : Rplus with
signature Rle ++> Rle ++> Rle as Rplus_Rle_mor.
intros ; apply Rplus_le_compat ; assumption.
Qed.

Add Parametric Morphism : Rminus with
signature Rle ++> Rle --> Rle as Rminus_Rle_mor.
intros ; unfold Rminus ;
apply Rplus_le_compat;
[assumption | apply Ropp_le_contravar ; assumption].
Qed.

Lemma x_plus_1_le_exp :
  forall (x : R), x + 1 <= exp x.
Admitted.
