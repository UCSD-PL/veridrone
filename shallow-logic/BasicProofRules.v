Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import ChargeTactics.Tactics.
Require Import SLogic.Stream.
Require Import SLogic.Logic.
Require Import SLogic.Instances.
Require Import SLogic.LTLNotation.

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
  Variables T U V : Type.
  Variable f : U -> T.
  Variable g : T -> V.

  Lemma focusS_compose :
    forall P,
      focusS f (focusS g P) -|- focusS (fun u => g (f u)) P.
  Proof. reflexivity. Qed.

  Lemma focusA_compose :
    forall P,
      focusA f (focusA g P) -|- focusA (fun u => g (f u)) P.
  Proof. reflexivity. Qed.

  Lemma focusT_compose :
    forall P,
      focusT f (focusT g P) -|- focusT (fun u => g (f u)) P.
  Proof. reflexivity. Qed.

  Lemma focusS_lift1 :
    forall (T U : Type) (op : T -> U) e,
    focusS f (lift1 op e) = lift1 op (focusS f e).
  Proof. reflexivity. Qed.

  Lemma focusS_lift2 :
    forall (T U V : Type) (op : T -> U -> V) e1 e2,
    focusS f (lift2 op e1 e2) =
    lift2 op (focusS f e1) (focusS f e2).
  Proof. reflexivity. Qed.

  Lemma focusS_lift3 :
    forall (T U V R : Type) (op : T -> U -> V -> R) e1 e2 e3,
    focusS f (lift3 op e1 e2 e3) =
    lift3 op (focusS f e1) (focusS f e2) (focusS f e3).
  Proof. reflexivity. Qed.

  Lemma focusA_lift1 :
    forall (T U : Type) (op : T -> U) e,
    focusA f (lift1 op e) = lift1 op (focusA f e).
  Proof. reflexivity. Qed.

  Lemma focusA_lift2 :
    forall (T U V : Type) (op : T -> U -> V) e1 e2,
    focusA f (lift2 op e1 e2) =
    lift2 op (focusA f e1) (focusA f e2).
  Proof. reflexivity. Qed.

  Lemma focusA_lift3 :
    forall (T U V R : Type) (op : T -> U -> V -> R) e1 e2 e3,
    focusA f (lift3 op e1 e2 e3) =
    lift3 op (focusA f e1) (focusA f e2) (focusA f e3).
  Proof. reflexivity. Qed.

  Lemma focusT_lift1 :
    forall (T U : Type) (op : T -> U) e,
    focusT f (lift1 op e) = lift1 op (focusT f e).
  Proof. reflexivity. Qed.

  Lemma focusT_lift2 :
    forall (T U V : Type) (op : T -> U -> V) e1 e2,
    focusT f (lift2 op e1 e2) =
    lift2 op (focusT f e1) (focusT f e2).
  Proof. reflexivity. Qed.

  Lemma focusT_lift3 :
    forall (T U V R : Type) (op : T -> U -> V -> R) e1 e2 e3,
    focusT f (lift3 op e1 e2 e3) =
    lift3 op (focusT f e1) (focusT f e2) (focusT f e3).
  Proof. reflexivity. Qed.

  Let focusS := focusS f (V:=Prop).
  Let focusA := focusA f (V:=Prop).
  Let focusT := focusT f (V:=Prop).

  (* TODO: what about focus and enabled? *)

  Lemma focusA_pre :
    forall P, focusA (pre P) = pre (focusS P).
  Proof. reflexivity. Qed.

  Lemma focusA_post :
    forall P, focusA (post P) = post (focusS P).
  Proof. reflexivity. Qed.

  Lemma focusT_starts :
    forall P, focusT (starts P) = starts (focusA P).
  Proof. reflexivity. Qed.

  Lemma focusS_ltrue :
    focusS ltrue = ltrue.
  Proof. reflexivity. Qed.

  Lemma focusA_ltrue :
    focusA ltrue = ltrue.
  Proof. reflexivity. Qed.

  Lemma focusT_ltrue :
    focusT ltrue = ltrue.
  Proof. reflexivity. Qed.

  Lemma focusS_lfalse :
    focusS lfalse = lfalse.
  Proof. reflexivity. Qed.

  Lemma focusA_lfalse :
    focusA lfalse = lfalse.
  Proof. reflexivity. Qed.

  Lemma focusT_lfalse :
    focusT lfalse = lfalse.
  Proof. reflexivity. Qed.

  Lemma focusS_and :
    forall P Q,
      focusS (P //\\ Q) = (focusS P //\\ focusS Q).
  Proof. reflexivity. Qed.

  Lemma focusA_and :
    forall P Q,
      focusA (P //\\ Q) = (focusA P //\\ focusA Q).
  Proof. reflexivity. Qed.

  Lemma focusT_and :
    forall P Q,
      focusT (P //\\ Q) = (focusT P //\\ focusT Q).
  Proof. reflexivity. Qed.

  Lemma focusS_or :
    forall P Q,
      focusS (P \\// Q) = (focusS P \\// focusS Q).
  Proof. reflexivity. Qed.

  Lemma focusA_or :
    forall P Q,
      focusA (P \\// Q) = (focusA P \\// focusA Q).
  Proof. reflexivity. Qed.

  Lemma focusT_or :
    forall P Q,
      focusT (P \\// Q) = (focusT P \\// focusT Q).
  Proof. reflexivity. Qed.

  Lemma focusS_impl :
    forall P Q,
      focusS (P -->> Q) = (focusS P -->> focusS Q).
  Proof. reflexivity. Qed.

  Lemma focusA_impl :
    forall P Q,
      focusA (P -->> Q) = (focusA P -->> focusA Q).
  Proof. reflexivity. Qed.

  Lemma focusT_impl :
    forall P Q,
      focusT (P -->> Q) = (focusT P -->> focusT Q).
  Proof. reflexivity. Qed.

  Lemma focusS_embed :
    forall P,
      focusS (embed P) = embed P.
  Proof. reflexivity. Qed.

  Lemma focusA_embed :
    forall P,
      focusA (embed P) = embed P.
  Proof. reflexivity. Qed.

  Lemma focusT_embed :
    forall P,
      focusT (embed P) = embed P.
  Proof. reflexivity. Qed.

  Lemma focusS_lforall :
    forall T P,
      focusS (lforall (T:=T) P) =
      lforall (fun t => focusS (P t)).
  Proof. reflexivity. Qed.

  Lemma focusA_lforall :
    forall T P,
      focusA (lforall (T:=T) P) =
      lforall (fun t => focusA (P t)).
  Proof. reflexivity. Qed.

  Lemma focusT_lforall :
    forall T P,
      focusT (lforall (T:=T) P) =
      lforall (fun t => focusT (P t)).
  Proof. reflexivity. Qed.

  Lemma focusS_lexists :
    forall T P,
      focusS (lexists (T:=T) P) =
      lexists (fun t => focusS (P t)).
  Proof. reflexivity. Qed.

  Lemma focusA_lexists :
    forall T P,
      focusA (lexists (T:=T) P) =
      lexists (fun t => focusA (P t)).
  Proof. reflexivity. Qed.

  Lemma focusT_lexists :
    forall T P,
      focusT (lexists (T:=T) P) =
      lexists (fun t => focusT (P t)).
  Proof. reflexivity. Qed.

  Lemma focusT_always :
    forall P,
      focusT (always P) = always (focusT P).
  Proof. reflexivity. Qed.

  Lemma focusT_eventually :
    forall P,
      focusT (eventually P) = eventually (focusT P).
  Proof. reflexivity. Qed.

End simulations.

Hint Rewrite -> focusS_compose focusA_compose focusT_compose
     focusS_lift1 focusS_lift2 focusS_lift3 focusA_lift1
     focusA_lift2 focusA_lift3 focusT_lift1 focusT_lift2
     focusT_lift3 focusA_pre focusA_post focusT_starts
     focusS_ltrue focusA_ltrue focusT_ltrue focusS_lfalse
     focusA_lfalse focusT_lfalse focusS_and focusA_and
     focusT_and focusS_or focusA_or focusT_or focusS_impl
     focusA_impl focusT_impl focusS_embed focusA_embed
     focusT_embed focusS_lforall focusA_lforall focusT_lforall
     focusS_lexists focusA_lexists focusT_lexists
     focusT_always focusT_eventually :
  rw_focus.

Ltac rewrite_focus :=
  autorewrite with rw_focus.

Section temporal_exists.

  Context {T U : Type}.

  Local Transparent ILInsts.ILFun_Ops.
  Local Transparent ILInsts.ILPre_Ops.

  (* This is rule E2 from the original TLA paper. *)
  Theorem texistsL :
    forall (P : TraceProp U) (Q : TraceProp (T * U)),
      Q |-- focusT snd P ->
      texists _ Q |-- P.
  Proof.
    intros. unfold texists.
    simpl. intros.
    destruct H0.
    eapply H in H0. auto.
  Qed.

  (* This is rule E1 from the original TLA paper. *)
  Theorem texistsR :
    forall (Q : TraceProp (T * U)) (f : StateVal U T),
      focusT (fun u => (f u, u)) Q |-- texists _ Q.
  Proof.
    intros Q f. unfold texists, Logic.texists, focusT.
    simpl. intros tr Hfocus.
    exists (fun n => f (tr n)).
    assumption.
  Qed.

(*
  (* Here is the old texistsR rule. *)
  Definition exactTrace (tr : trace T) : TraceProp T :=
    trace_eq eq tr.

  Theorem texistsR' :
    forall (P : TraceProp U) (Q : TraceProp (T * U)),
      (exists tr' : trace T,
          focusT snd P //\\ focusT fst (exactTrace tr')
          |-- Q) ->
      P |-- texists T Q.
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

Section history_variables.

  Theorem add_history {T U} (P : TraceProp T) (x : StateVal T U)
  : P -|- TExists (list U) , focusT snd P
                        //\\ always (starts (lift2 eq
                                                   (post fst)
                                                   (lift2 cons (pre snd#x) (pre fst)))).
  Proof.
    split.
    - cbv beta iota zeta delta - [ Stream.hd Stream.tl plus Stream.nth_suf pre post fst snd trace ].
      intros.
      exists (fmap_trace (List.map x) (prefix t)).
      split.
      + exact H.
      + intros.
        clear. induction n.
        { compute. reflexivity. }
        { cbv beta iota zeta delta - [ fmap_trace List.map plus prefix ] in *.
          replace (S n + 0) with (n + 1) by omega.
          rewrite IHn; clear IHn.
          replace (S n + 1) with (S (S n)) by omega.
          replace (n + 0) with (n) by omega.
          replace (n + 1) with (S n) by omega.
          reflexivity. }
    - apply texistsL. charge_tauto.
  Qed.

End history_variables.

Local Transparent ILInsts.ILFun_Ops.
Local Transparent ILInsts.ILPre_Ops.

Lemma focusT_snd_texists :
  forall (V T U : Type) (P : TraceProp (V * U)),
    texists _ (focusT (fun p => (fst p, snd (snd p))) P) |--
    focusT (snd (A:=T)) (texists V P).
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
    texists _ Q |-- texists _ P.
Proof.
  intros. apply texistsL. rewrite <- focusT_snd_texists.
  rewrite <- texistsR. rewrite H.
  rewrite focusT_compose. instantiate (1:=f). reflexivity.
Qed.
