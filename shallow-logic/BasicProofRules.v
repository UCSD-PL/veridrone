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

  (* Facts about pre and starts *)
  Lemma pre_entails : forall (A B : StateProp),
      pre (A -->> B) |-- pre A -->> pre B.
  Proof.
    unfold pre. simpl. auto.
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
  Context {T U V : Type}.
  Variable f : U -> T.
  Variable g : T -> V.

  Theorem focusS_compose :
    forall P,
      focusS f (focusS g P) -|- focusS (fun u => g (f u)) P.
  Proof. reflexivity. Qed.

  Theorem focusA_compose :
    forall P,
      focusA f (focusA g P) -|- focusA (fun u => g (f u)) P.
  Proof. reflexivity. Qed.

  Theorem focusT_compose :
    forall P,
      focusT f (focusT g P) -|- focusT (fun u => g (f u)) P.
  Proof. reflexivity. Qed.

  Let focusS := focusS f (V:=Prop).
  Let focusA := focusA f (V:=Prop).
  Let focusT := focusT f (V:=Prop).

  Theorem focusT_now :
    forall P, focusT (starts (pre P)) -|-
              starts (pre (focusS P)).
  Proof. reflexivity. Qed.

  Theorem focusT_starts :
    forall P, focusT (starts P) -|- starts (focusA P).
  Proof. reflexivity. Qed.

End simulations.

Section temporal_exists.

  Context {T U : Type}.

  Local Transparent ILInsts.ILFun_Ops.
  Local Transparent ILInsts.ILPre_Ops.

  (* This is rule E2 from the original TLA paper. *)
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

  (* This is rule E1 from the original TLA paper. *)
  Theorem texistsR :
    forall (Q : TraceProp (T * U)) (f : StateVal U T),
      focusT (fun u => (f u, u)) Q |-- texists Q.
  Proof.
    intros Q f. unfold texists, Logic.texists, focusT.
    simpl. intros tr Hfocus.
    exists (fun n => f (tr n)).
    assumption.
  Qed.

  (* Here is the old texistsR rule. *)
  (*
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
  *)

End temporal_exists.

Local Transparent ILInsts.ILFun_Ops.
Local Transparent ILInsts.ILPre_Ops.

Lemma focusT_snd_texists :
  forall (V T U : Type) (P : TraceProp (V * U)),
    texists (focusT (fun p => (fst p, snd (snd p))) P) |--
    focusT (snd (A:=T)) (texists (T:=V) P).
Proof.
  intros. unfold focusT, texists. simpl. intros.
  destruct H as [tr' H].
  eexists. exact H.
Qed.

(* This is the proof rule described informally at
   the beginning of section 8.3.2 of the original
   TLA paper. *)
Theorem refinement_mapping :
  forall (T U V : Type) (Q : TraceProp (T * U))
         (P : TraceProp (V * U))
         (f : StateVal (T * U) V),
    Q |-- focusT (fun tu => (f tu, snd tu)) P ->
    texists Q |-- texists P.
Proof.
  intros. apply texistsL. rewrite <- focusT_snd_texists.
  rewrite <- texistsR. rewrite H.
  rewrite focusT_compose. instantiate (1:=f). reflexivity.
Qed.
