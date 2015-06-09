Require Import Coq.Classes.Morphisms.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.RIneq.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.BasicProofRules.
Require Import TLA.Automation.

(* A library of useful TLA formulas, built
   from TLA primitives. *)

Open Scope HP_scope.
Open Scope string_scope.

(* Action formula expressing that all variables
   in xs are unchanged. *)
Fixpoint Unchanged (xs:list Var) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (x! = x) //\\ (Unchanged xs)
  end.

Fixpoint UnchangedT (xs:list Term) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (next_term x = x) //\\ (UnchangedT xs)
  end.

(* Formula taking the maximum of two terms. *)
Definition Max (a b : Term)
           (c : Term -> Formula) : Formula :=
  (a >= b -->> (c a)) //\\ (a <= b -->> c b).

(* State formula expressing that the values of all
   variables in xs in the current state are equal
   to their value in st. *)
Fixpoint VarsAgree (xs:list Var) (st:state) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (x = st x) //\\ (VarsAgree xs st)
  end.

(* Action formula expressing that the values of all
   variables in xs in the next state are equal to
   their value in st. *)
Fixpoint AVarsAgree (xs:list Var) (st:state) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (x! = st x) //\\ (AVarsAgree xs st)
  end.

(* Our shallow encoding of continuous evolutions. *)
Definition Evolution := state->Formula.

(* Expresses the property that a differentiable formula
   is a solution to a list of differential equations
   in the range 0 to r. *)
Definition solves_diffeqs (f : R -> state)
           (cp : Evolution) (r : R)
           (is_derivable : forall x, derivable (fun t => f t x)) :=
    forall z, (R0 <= z <= r)%R ->
              eval_formula (cp (fun x => derive (fun t => f t x) (is_derivable x) z))
                           (Stream.forever (f z)).

(* Prop expressing that f is a solution to diffeqs in
   [0,r]. *)
Definition is_solution (f : R -> state)
           (cp:Evolution) (r : R) :=
  exists is_derivable,
    (* f is a solution to diffeqs *)
    solves_diffeqs f cp r is_derivable.

(* Action formula expressing that a transition
   is consistent with the system of differential
   equations represented by cp. *)
Definition Continuous (cp:Evolution) : Formula :=
  Exists r : R,
  Exists f : R -> state,
         (r > 0)
    //\\ (PropF (is_solution f cp r))
    //\\ (Embed (fun st st' => f R0 = st /\ f r = st')).

Global Instance Proper_Continuous_entails
  : Proper ((pointwise_relation _ lentails) ==> lentails) Continuous.
Proof.
  do 5 red.
  simpl. destruct tr; simpl.
  destruct 1. destruct H0.
  exists x0. intuition.
  eexists; split; eauto.
  split; eauto.
  unfold is_solution in *. destruct H0. exists x2.
  unfold solves_diffeqs in *.
  intros.
  specialize (H0 _ H3).
  eapply H. assumption.
Qed.

Global Instance Proper_Continuous_equiv
  : Proper ((pointwise_relation _ lequiv) ==> lequiv) Continuous.
Proof.
  morphism_intro.
  eapply lequiv_to_iff.
  intros. simpl.
  apply exists_iff; intros.
  apply exists_iff; intros.
  eapply and_iff; try tauto; intros.
  eapply and_iff; try tauto; intros.
  unfold is_solution.
  apply exists_iff; intros.
  unfold solves_diffeqs.
  apply forall_iff; intros.
  apply impl_iff; try tauto; intros.
  red in H.
  rewrite H.
  eapply Proper_eval_formula; reflexivity.
Qed.

Require Import ExtLib.Tactics.

Lemma VarRenameMap_derivable : forall f m,
    (forall x, Ranalysis1.derivable (fun t => f t x)) ->
    forall x,
      Ranalysis1.derivable
        (fun t => subst_state (VarRenameMap m) (f t) x).
Proof.
  intros.
  induction m.
  - simpl. auto.
  - simpl. destruct a. simpl.
    destruct (String.string_dec x v).
    + subst. apply H.
    + auto.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma subst_VarRenameMap_derive_distr :
  forall m f z pf1 pf2,
    subst_state (VarRenameMap m)
          (fun x =>
             Ranalysis1.derive (fun t : R => f t x) (pf1 x) z) =
    fun x =>
      Ranalysis1.derive (fun t : R =>
                           subst_state (VarRenameMap m) (f t) x) (pf2 x)
                        z.
Proof.
  intros. apply functional_extensionality.
  intros. generalize (pf2 x). clear pf2.
  induction m; intros.
  - simpl. apply Ranalysis4.pr_nu_var. auto.
  - destruct a. simpl in *.
    destruct (String.string_dec x v).
    + subst. apply Ranalysis4.pr_nu_var.
      auto.
    + erewrite IHm. auto.
Qed.

Theorem Continuous_rename : forall (r : list (Var * Var)) c,
    Continuous (fun st' => Rename (VarRenameMap r) (c (subst_state (VarRenameMap r) st')))
    |-- Rename (VarRenameMap r) (Continuous c).
Proof.
  breakAbstraction. intros.
  forward_reason.
  exists x. exists (fun t => subst_state (VarRenameMap r) (x0 t)).
  split; auto.
  split.
  { clear - H0.
    unfold is_solution in *.
    destruct H0.
    exists (VarRenameMap_derivable _ _ x1).
    unfold solves_diffeqs in *.
    intros. specialize (H _ H0).
    simpl in *.
    eapply Proper_eval_formula; [ | | eassumption ].
    { match goal with
      | |- (_ ?X -|- _ ?Y) => assert (X = Y)
      end.
      { eapply FunctionalExtensionality.functional_extensionality.
        intros. clear.
        erewrite subst_VarRenameMap_derive_distr.
        reflexivity. }
      { rewrite H1. reflexivity. } }
    { rewrite Stream.stream_map_forever; eauto with typeclass_instances.
      reflexivity. } }
  split.
  { rewrite H1. clear.
    rewrite (Stream.trace_eta tr). simpl. reflexivity. }
  { rewrite H2.
    rewrite (Stream.trace_eta tr). simpl.
    rewrite (Stream.trace_eta (Stream.tl tr)). simpl. reflexivity. }
Qed.

Close Scope string_scope.
Close Scope HP_scope.
