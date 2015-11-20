Require Import Coq.Classes.Morphisms.
Require Import Logic.Syntax.
Require Import Logic.Semantics.
Require Import Logic.BasicProofRules.
Require Import Logic.Automation.

Global Instance Proper_Comp :
  Proper (term_equiv ==> term_equiv ==> eq ==> lentails) Comp.
Proof.
  morphism_intro. breakAbstraction.
  subst. unfold eval_comp; simpl.
  intuition congruence.
Qed.
Global Instance Proper_Comp_lequiv :
  Proper (term_equiv ==> term_equiv ==> eq ==> lequiv) Comp.
Proof.
  morphism_intro.
  split; breakAbstraction;
  subst; unfold eval_comp; simpl;
  intuition congruence.
Qed.
Global Instance Proper_PlusT :
  Proper (term_equiv ==> term_equiv ==> term_equiv) PlusT.
Proof.
  morphism_intro; unfold term_equiv in *;
  simpl; intuition congruence.
Qed.
Global Instance Proper_MinusT :
  Proper (term_equiv ==> term_equiv ==> term_equiv) MinusT.
Proof.
  morphism_intro; unfold term_equiv in *;
  simpl; intuition congruence.
Qed.
Global Instance Proper_MultT :
  Proper (term_equiv ==> term_equiv ==> term_equiv) MultT.
Proof.
  morphism_intro; unfold term_equiv in *;
  simpl; intuition congruence.
Qed.
Global Instance Proper_InvT :
  Proper (term_equiv ==> term_equiv) InvT.
Proof.
  morphism_intro; unfold term_equiv in *;
  simpl; intuition congruence.
Qed.
Global Instance Proper_CosT :
  Proper (term_equiv ==> term_equiv) CosT.
Proof.
  morphism_intro; unfold term_equiv in *;
  simpl; intuition congruence.
Qed.
Global Instance Proper_SinT :
  Proper (term_equiv ==> term_equiv) SinT.
Proof.
  morphism_intro; unfold term_equiv in *;
  simpl; intuition congruence.
Qed.
Global Instance Proper_SqrtT :
  Proper (term_equiv ==> term_equiv) SqrtT.
Proof.
  morphism_intro; unfold term_equiv in *;
  simpl; intuition congruence.
Qed.
Global Instance Proper_ArctanT :
  Proper (term_equiv ==> term_equiv) ArctanT.
Proof.
  morphism_intro; unfold term_equiv in *;
  simpl; intuition congruence.
Qed.
