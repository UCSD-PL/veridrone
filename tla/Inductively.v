Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import TLA.Tactics.
Require Import Coq.Classes.Morphisms.

Local Open Scope HP_scope.

Definition Inductively (P A : Formula) : Formula :=
  [](P //\\ A -->> next P).

Lemma Inductively_Inv :
  forall P A,
    is_st_formula P ->
    P //\\ []A //\\ Inductively P A |-- []P.
Proof.
  unfold Inductively. intros.
  rewrite Always_and. eapply discr_indX.
  - auto.
  - charge_assumption.
  - charge_assumption.
  - charge_tauto.
Qed.

Lemma Inductively_And : forall P Q E,
    Inductively P (Q //\\ E) //\\
    Inductively Q (P //\\ E)
    |-- Inductively (P //\\ Q) E.
Proof.
  unfold Inductively. intros.
  transitivity
    ([](P //\\ (Q //\\ E) -->> next P) //\\
       [](Q //\\ (P //\\ E) -->> next Q)).
  - charge_tauto.
  - rewrite Always_and.
    tlaRevert. eapply Always_imp.
    charge_tauto.
Qed.

Lemma Inductively_Or : forall P Q S1 S2,
    Inductively P S1 //\\
    Inductively Q S2
    |-- Inductively (P \\// Q) ((P //\\ S1) \\// (Q //\\ S2)).
Proof.
  unfold Inductively.
  intros.
  tlaRevert. tlaRevert.
  rewrite <- curry. rewrite Always_and.
  apply Always_imp. simpl. restoreAbstraction.
  charge_intro. charge_intro.
  rewrite <- landA.
  tlaRevert. apply landL1.
  charge_intros. decompose_hyps; charge_tauto.
Qed.

(** TODO: Using [eq] here is a hack that we should fix! **)
Lemma Proper_Inductively
: Proper (eq ==> lequiv ==> lequiv)%signature Inductively.
Proof.
 red. do 2 red. unfold Inductively. intros.
 apply Proper_Always.
 eapply limpl_lequiv_m.
 { rewrite H. rewrite H0. reflexivity. }
 { subst. reflexivity. }
Qed.

Lemma Proper_Inductively_entails
: Proper (eq ==> lentails --> lentails)%signature Inductively.
Proof.
 red. do 2 red. unfold Inductively. intros.
 eapply Proper_Always_entails. subst.
 red in H0. rewrite H0. reflexivity.
Qed.

Lemma Inductively_equiv
  : forall a b : Formula,
    is_st_formula a -> is_st_formula b ->
    a -|- b ->
    forall c d : Formula,
      c -|- d ->
      Inductively a c -|- Inductively b d.
Proof.
  unfold Inductively. intros.
  apply Proper_Always.
  rewrite H2; clear H2.
  eapply limpl_lequiv_m.
  { rewrite H1. reflexivity. }
  { split; eapply next_st_formula_entails; eauto; eapply H1. }
Qed.

Lemma Inductively_entails
  : forall a b : Formula,
    is_st_formula a -> is_st_formula b ->
    b -|- a ->
    forall c d : Formula,
      d |-- c ->
      Inductively a c |-- Inductively b d.
Proof.
  unfold Inductively. intros.
  eapply Proper_Always_entails.
  rewrite H2; clear H2.
  eapply limpl_lentails_m.
  { red. rewrite H1. reflexivity. }
  { eapply next_st_formula_entails; eauto; eapply H1. }
Qed.

Lemma Inductively_Or' : forall G P Q S1 S2,
    G |-- Inductively P S1 ->
    G |-- Inductively Q S2 ->
    G |-- Inductively (P \\// Q) ((P //\\ S1) \\// (Q //\\ S2)).
Proof.
  intros. charge_apply (Inductively_Or P Q S1 S2).
  charge_tauto.
Qed.

Close Scope HP_scope.