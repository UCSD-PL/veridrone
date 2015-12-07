Require Import Charge.Logics.ILogic.
Require Import ChargeTactics.Tactics.
Require Import SLogic.Stream.
Require Import SLogic.Logic.
Require Import SLogic.Instances.

Section with_state.

  Variable state : Type.

  Let StateProp := StateProp state.
  Let ActionProp := ActionProp state.
  Let TraceProp := TraceProp state.

  Let next := @next state.
  Let starts := @starts state.
  Let always := @always state.
  Let eventually := @eventually state.

  Local Transparent ILInsts.ILFun_Ops.
  Local Transparent ILInsts.ILPre_Ops.

  (** Always Facts **)

  Lemma always_and : forall P Q,
      always P //\\ always Q -|- always (P //\\ Q).
  Proof.
    unfold always, Logic.always. simpl.
    split; repeat red.
    { intuition. }
    { intros; split; apply H. }
  Qed.

  Lemma always_or : forall P Q,
      always P \\// always Q |-- always (P \\// Q).
  Proof.
    unfold always, Logic.always. simpl.
    repeat red; intuition.
  Qed.

  Lemma always_impl : forall P Q,
      always (P -->> Q) |-- always P -->> always Q.
  Proof.
    unfold always, Logic.always. simpl.
    repeat red; intuition.
  Qed.

  Lemma always_tauto
    : forall G P, |-- P -> G |-- always P.
  Proof.
    compute; intuition.
  Qed.

  (* Facts about currently and starts *)
  Lemma currently_entails : forall (A B : StateProp),
      currently (A -->> B) |-- currently A -->> currently B.
  Proof.
    unfold currently. simpl. auto.
  Qed.

  Lemma starts_post :
    forall (P : ActionProp) (Q : StateProp),
      (forall st, P st |-- Q) ->
      |-- starts P -->> starts (post Q).
  Proof.
    unfold starts, post, Logic.starts.
    simpl; intros; eauto.
  Qed.

  Lemma and_forall : forall {T} (F G : T -> Prop),
      ((forall x, F x) /\ (forall x, G x)) <->
      (forall x, F x /\ G x).
  Proof. intros. clear. firstorder. Qed.

  Lemma starts_and :
    forall P Q, starts P //\\ starts Q -|- starts (P //\\ Q).
  Proof.
    intros. apply and_forall. intros.
    unfold starts, Logic.starts.
    simpl. intuition.
  Qed.

  Lemma starts_or :
    forall P Q, starts P \\// starts Q -|- starts (P \\// Q).
  Proof.
    unfold starts, Logic.starts; simpl; intros;
    split; simpl; eauto.
  Qed.

  Lemma starts_impl :
    forall P Q, starts P -->> starts Q -|- starts (P -->> Q).
  Proof.
    unfold starts, Logic.starts; simpl; intros;
    split; simpl; intros; eauto.
  Qed.

  Lemma starts_ex : forall T (P : T -> _),
      Exists x : T, starts (P x) -|- starts (lexists P).
  Proof.
    unfold starts; simpl; intros; split; simpl; eauto.
  Qed.

  Lemma starts_all : forall T (P : T -> _),
      Forall x : T, starts (P x) -|- starts (lforall P).
  Proof.
    unfold starts; simpl; intros; split; simpl; eauto.
  Qed.

  Lemma starts_tauto : forall (P : ActionProp),
      |-- P ->
      |-- starts P.
  Proof.
    compute. auto.
  Qed.

  (** This is standard discrete induction over time **)
  Lemma dind_lem : forall (P : TraceProp),
      |-- P -->> always (P -->> next P) -->> always P.
  Proof.
    unfold always, Logic.always, next, Logic.next.
    intros. do 3 red.
    intros. red. simpl.
    intros. induction n.
    { assumption. }
    { unfold tl in *. apply H1 in IHn.
      unfold nth_suf in *.
      erewrite Proper_trace_eq_iff.
      { exact IHn. }
      { unfold trace_eq. simpl. intros.
        rewrite <- plus_n_Sm. reflexivity. } }
  Qed.

  Theorem discrete_induction
    : forall G P T,
      G |-- always T ->
      G |-- P ->
      G |-- always (P -->> T -->> next P) ->
      G |-- always P.
  Proof.
    intros G P T. intros.
    generalize (dind_lem P).
    intros.
    charge_apply H2.
    charge_split.
    { assumption. }
    { apply Lemmas.lcut with (R:=G).
      { charge_assumption. }
      { rewrite H at 1. rewrite H1.
        rewrite <- Lemmas.uncurry.
        rewrite landC. rewrite Lemmas.uncurry.
        rewrite always_impl. charge_tauto. } }
  Qed.

End with_state.

Section simulations.
  Context {T U : Type}.
  Variable f : U -> T.

  Let focusS := @focusS T U f.
  Let focusA := @focusA T U f.
  Let focusT := @focusT T U f.

  Theorem focusT_now :
    forall P, focusT (starts (currently P)) -|-
              starts (currently (focusS P)).
  Proof. reflexivity. Qed.

  Theorem focusT_starts :
    forall P, focusT (starts P) -|- starts (focusA P).
  Proof. reflexivity. Qed.

End simulations.

Section temporal_exists.

  Context {T U : Type}.

  Let texists := @texists T U.

  Local Transparent ILInsts.ILFun_Ops.
  Local Transparent ILInsts.ILPre_Ops.

  Theorem texistsL :
    forall (P : TraceProp U) (Q : TraceProp (T * U)),
      Q |-- focusT snd P ->
      texists Q |-- P.
  Proof.
    intros. unfold texists.
    simpl. intros.
    destruct H0.
    eapply H in H0. auto.
  Qed.

  Definition exactTrace (tr : trace T) : TraceProp T :=
    trace_eq eq tr.

  Theorem texistsR :
    forall (P : TraceProp U) (Q : TraceProp (T * U)),
      (exists tr' : trace T,
          focusT snd P //\\ focusT fst (exactTrace tr')
          |-- Q) ->
      P |-- texists Q.
  Proof.
    intros. unfold texists.
    simpl. intros.
    destruct H.
    exists x. eapply H.
    split.
    { assumption. }
    { unfold focusT. simpl. unfold fmap_trace. simpl.
      reflexivity. }
  Qed.

End temporal_exists.