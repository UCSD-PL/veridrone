Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import TLA.Tactics.
Require Import Coq.Classes.Morphisms.

Local Open Scope HP_scope.

Definition Preserves (P : StateFormula) (A : ActionFormula) : Formula :=
  A -->> (P -->> next P).

Global Instance Proper_Preserves_lequiv :
  Proper (eq ==> lequiv ==> lequiv) Preserves.
Proof.
  morphism_intro. unfold Preserves.
  subst. rewrite H0. reflexivity.
Qed.

Global Instance Proper_Preserves_lentails :
  Proper (eq ==> lentails --> lentails) Preserves.
Proof.
  morphism_intro. unfold Preserves.
  subst. rewrite H0. reflexivity.
Qed.

Theorem Preserves_Or
  : forall (P Q : StateFormula) (S1 S2 : ActionFormula),
    Preserves P S1 //\\ Preserves Q S2
              |-- Preserves (P \\// Q) (P //\\ S1 \\// Q //\\ S2).
Proof.
  unfold Preserves.
  simpl; restoreAbstraction.
  intros.
  charge_intro.
  charge_assert (next P \\// next Q); [ | charge_intros; charge_assumption ].
  charge_cases; solve [ charge_left; charge_use; charge_tauto
                      | charge_right; charge_use; charge_tauto ].
Qed.

Lemma Preserves_Inv_simple
: forall (P : StateFormula) (A : ActionFormula),
    is_st_formula P ->
    |-- Preserves P A ->
    P //\\ []A |-- []P.
Proof.
  intros.
  eapply discr_indX.
  - assumption.
  - charge_assumption.
  - charge_assumption.
  - unfold Preserves in *.
    charge_tauto.
Qed.

Lemma Preserves_Inv
: forall (P X : StateFormula) (A : ActionFormula) (G : Formula),
    is_st_formula P ->
    G |-- [] X ->
    X |-- Preserves P A ->
    G |-- P //\\ []A -->> []P.
Proof.
  intros.
  rewrite landC. rewrite curry.
  charge_intros.
  eapply discr_indX.
  - assumption.
  - rewrite H0. rewrite Always_and. charge_assumption.
  - charge_assumption.
  - unfold Preserves in *.
    charge_tauto.
Qed.

Lemma Preserves_And_simple : forall P Q A B,
    Preserves P A //\\
    Preserves Q B
    |-- Preserves (P //\\ Q) (A //\\ B).
Proof.
  unfold Preserves. intros.
  charge_tauto.
Qed.

Lemma Preserves_And
  : forall (P Q : StateFormula) (A B : ActionFormula),
    Preserves P (Q //\\ A) //\\ Preserves Q (P //\\ B)
    |-- Preserves (P //\\ Q) (A //\\ B).
Proof.
  unfold Preserves. intros.
  charge_tauto.
Qed.

Lemma Preserves_intro
  : forall (I P G : Formula) (A : ActionFormula),
    G //\\ P |-- Preserves I A ->
    G |-- Preserves I (P //\\ A).
Proof.
  unfold Preserves. intros.
  charge_intros. charge_apply H.
  charge_tauto.
Qed.

Lemma Preserves_equiv
: forall a b : StateFormula,
    is_st_formula a -> is_st_formula b ->
    a -|- b ->
    forall c d : Formula,
      c -|- d ->
      Preserves a c -|- Preserves b d.
Proof.
  unfold Preserves. intros.
  rewrite H2; clear H2.
  eapply limpl_lequiv_m.
  { reflexivity. }
  { split;
    [ rewrite H1 at 1; rewrite (next_st_formula_entails a b)
    | rewrite <- H1 at 1; rewrite (next_st_formula_entails b a) ];
    try reflexivity; auto; eapply H1. }
Qed.

Lemma Preserves_entails
  : forall a b : Formula,
    is_st_formula a -> is_st_formula b ->
    b -|- a ->
    forall c d : Formula,
      d |-- c ->
      Preserves a c |-- Preserves b d.
Proof.
  unfold Preserves. intros.
  rewrite H2; clear H2.
  eapply limpl_lentails_m.
  { red. reflexivity. }
  { rewrite H1 at 1.
    rewrite (next_st_formula_entails a b); eauto. eapply H1. }
Qed.

Definition Inductively (P : StateFormula) (A : ActionFormula) : Formula :=
  []Preserves P A.

Lemma Inductively_Inv :
  forall P A,
    is_st_formula P ->
    P //\\ []A //\\ Inductively P A |-- []P.
Proof.
  unfold Inductively, Preserves. intros.
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
  unfold Inductively, Preserves. intros.
  rewrite Always_and. always_imp_tac.
  charge_tauto.
Qed.

Lemma Inductively_Or : forall P Q S1 S2,
    Inductively P S1 //\\
    Inductively Q S2
    |-- Inductively (P \\// Q) ((P //\\ S1) \\// (Q //\\ S2)).
Proof.
  unfold Inductively, Preserves.
  intros.
  tlaRevert. tlaRevert.
  rewrite <- curry. rewrite Always_and.
  apply Always_imp. simpl. restoreAbstraction.
  charge_intro. charge_intro.
  charge_cases; charge_tauto.
Qed.

Lemma Proper_Inductively
: Proper (eq ==> lequiv ==> lequiv)%signature Inductively.
Proof.
 red. do 2 red. unfold Inductively, Preserves. intros.
 apply Proper_Always_lequiv.
 eapply limpl_lequiv_m.
 { assumption. }
 { subst. reflexivity. }
Qed.

Lemma Proper_Inductively_entails
: Proper (eq ==> lentails --> lentails)%signature Inductively.
Proof.
 red. do 2 red. unfold Inductively, Preserves. intros.
 eapply Proper_Always_entails. subst.
 red in H0. rewrite H0. reflexivity.
Qed.

Lemma Inductively_equiv
: forall a b : StateFormula,
    is_st_formula a -> is_st_formula b ->
    a -|- b ->
    forall c d : Formula,
      c -|- d ->
      Inductively a c -|- Inductively b d.
Proof.
  unfold Inductively, Preserves. intros.
  apply Proper_Always_lequiv.
  rewrite H2; clear H2.
  eapply limpl_lequiv_m.
  { reflexivity. }
  { split;
    [ rewrite H1 at 1; rewrite (next_st_formula_entails a b)
    | rewrite <- H1 at 1; rewrite (next_st_formula_entails b a) ];
    try reflexivity; auto; eapply H1. }
Qed.

Lemma Inductively_entails
  : forall a b : Formula,
    is_st_formula a -> is_st_formula b ->
    b -|- a ->
    forall c d : Formula,
      d |-- c ->
      Inductively a c |-- Inductively b d.
Proof.
  unfold Inductively, Preserves. intros.
  eapply Proper_Always_entails.
  rewrite H2; clear H2.
  eapply limpl_lentails_m.
  { red. reflexivity. }
  { rewrite H1 at 1.
    rewrite (next_st_formula_entails a b); eauto. eapply H1. }
Qed.

Lemma Inductively_Or' : forall G P Q S1 S2,
    G |-- Inductively P S1 ->
    G |-- Inductively Q S2 ->
    G |-- Inductively (P \\// Q) ((P //\\ S1) \\// (Q //\\ S2)).
Proof.
  intros. charge_apply (Inductively_Or P Q S1 S2).
  charge_tauto.
Qed.
