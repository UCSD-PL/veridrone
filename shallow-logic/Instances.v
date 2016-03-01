Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.CoFunctor.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILEmbed.
Require Import SLogic.Logic.

Section with_state.

  Variable state : Type.

  Let StateVal := StateVal state.
  Let ActionVal := ActionVal state.
  Let TraceVal := TraceVal state.

  Let StateProp := StateProp state.
  Let ActionProp := ActionProp state.
  Let TraceProp := TraceProp state.

  Global Instance ILogicOps_StateProp : ILogicOps StateProp :=
    @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogicOps_ActionProp :
    ILogicOps ActionProp :=
    @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogicOps_TraceProp :
    ILogicOps TraceProp :=
    @ILInsts.ILFun_Ops _ _ _.

  Global Instance ILogic_StateProp : ILogic StateProp := ILInsts.ILFun_ILogic _.
  Global Instance ILogic_ActionProp : ILogic ActionProp := ILInsts.ILFun_ILogic _.
  Global Instance ILogic_TraceProp : ILogic TraceProp := ILInsts.ILFun_ILogic _.

  Local Transparent ILInsts.ILFun_Ops.
  Local Transparent ILInsts.ILPre_Ops.

  Global Instance EmbedOp_Prop_StateProp :
    EmbedOp Prop StateProp :=
  { embed := fun P _ => P }.
  Global Instance Embed_Prop_StateProp : Embed Prop StateProp.
  Proof.
    constructor; simpl; intuition.
  Qed.

  Global Instance EmbedOp_Prop_ActionProp :
    EmbedOp Prop ActionProp :=
  { embed := fun P _ _ => P }.
  Global Instance Embed_Prop_ActionProp :
    Embed Prop ActionProp.
  Proof.
    constructor; simpl; intuition.
  Qed.

  Global Instance EmbedOp_Prop_TraceProp :
    EmbedOp Prop TraceProp :=
    { embed := fun P _ => P }.
  Global Instance Embed_Prop_TraceProp : Embed Prop TraceProp.
  Proof.
    constructor; simpl; intuition.
  Qed.

  Global Instance EmbedOp_StateVal_StateProp :
    EmbedOp (StateVal Prop) StateProp :=
  { embed := fun P => P }.
  Global Instance Embed_StateVal_StateProp :
    Embed (StateVal Prop) StateProp.
  Proof.
    constructor; simpl; intuition.
  Qed.

  Global Instance EmbedOp_ActionVal_ActionProp :
    EmbedOp (ActionVal Prop) ActionProp :=
  { embed := fun P => P }.
  Global Instance Embed_ActionVal_ActionProp :
    Embed (ActionVal Prop) ActionProp.
  Proof.
    constructor; simpl; intuition.
  Qed.

  (* These are the "obvious" definitions,
     needed to help Coq *)
  Global Instance Applicative_Trace
    : Applicative TraceVal :=
    { pure := fun _ x => fun _ => x
      ; ap := fun _ _ f x => fun tr => (f tr) (x tr)
    }.

  Global Instance Functor_Trace
    : Functor TraceVal :=
    { fmap := fun _ _ f x => ap (pure f) x }.


  Global Instance Applicative_Action
    : Applicative ActionVal :=
    { pure := fun _ x => fun _ _ => x
      ; ap := fun _ _ f x => fun st st' =>
                               (f st st') (x st st')
    }.

  Global Instance Functor_Action
    : Functor ActionVal :=
    { fmap := fun _ _ f x => ap (pure f) x }.

  Global Instance Applicative_State
    : Applicative StateVal :=
    { pure := fun _ x => fun _ => x
      ; ap := fun _ _ f x => fun st => (f st) (x st)
    }.

  Global Instance Functor_State
    : Functor StateVal :=
    { fmap := fun _ _ f x => ap (pure f) x }.

  Global Instance Proper_starts_lentails
    : Proper (lentails ==> lentails) starts.
  Proof.
    red. red. intros.
    unfold starts. red. simpl.
    red in H. red in H. red in H.
    intros.
    eapply H. eassumption.
  Qed.

  Global Instance Proper_starts_lequiv
    : Proper (lequiv ==> lequiv) starts.
  Proof.
    red. red. intros.
    unfold starts. red. simpl.
    split; intros; eapply H; eauto.
  Qed.

  Global Instance Proper_next_lequiv
    : Proper (lequiv ==> lequiv) next.
  Proof.
    red. red. intros.
    unfold next. red. simpl.
    split; intros; eapply H; eauto.
  Qed.

  Global Instance Proper_next_lentails
    : Proper (lentails ==> lentails) next.
  Proof.
    red. red. intros.
    unfold next. red. simpl.
    intros; eapply H; eauto.
  Qed.

  Global Instance Proper_trace_eq_iff T (P:TraceVal T) :
    Proper (Stream.trace_eq eq ==> eq) P.
  Proof.
    red. red. intros.
    apply FunctionalExtensionality.functional_extensionality
      in H. subst. reflexivity.
  Qed.

  Global Instance Proper_always_lequiv :
    Proper (lequiv ==> lequiv) always.
  Proof.
    unfold always, Logic.always.
    repeat red; intros; split; intros; repeat red; intros;
    apply H; auto.
  Qed.

  Global Instance Proper_always_lentails :
    Proper (lentails ==> lentails) always.
  Proof.
    repeat red; intros; repeat red; intros;
    apply H; auto.
  Qed.

End with_state.

Section cofunctors.

  Global Instance CoFunctor_StateProp : CoFunctor StateProp :=
  { cofmap := fun A B f => @focusS A B f _ }.

  Global Instance CoFunctor_TraceProp : CoFunctor TraceProp :=
  { cofmap := fun A B f => @focusT A B f _ }.

  Global Instance CoFunctor_ActionProp : CoFunctor ActionProp :=
  { cofmap := fun A B f => @focusA A B f _ }.

  Global Instance CoFunctor_StateVal {T} : CoFunctor (fun x => StateVal x T) :=
  { cofmap := fun A B f => @focusS A B f _ }.

  Global Instance CoFunctor_TraceVal {T} : CoFunctor (fun x => TraceVal x T) :=
  { cofmap := fun A B f => @focusT A B f _ }.

  Global Instance CoFunctor_ActionVal {T} : CoFunctor (fun x => ActionVal x T) :=
  { cofmap := fun A B f => @focusA A B f _ }.

End cofunctors.

Section temporal_exists.

  Context {T U : Type}.

  Let texists := @texists T U.

  Local Transparent ILInsts.ILFun_Ops.
  Local Transparent ILInsts.ILPre_Ops.

  Global Instance Proper_texists_lentails
  : Proper (lentails ==> lentails) texists.
  Proof.
    unfold texists. repeat red.
    intros. destruct H0. eexists. eapply H. eassumption.
  Qed.

  Global Instance Proper_texists_lequiv
  : Proper (lequiv ==> lequiv) texists.
  Proof.
    unfold texists.
    split; repeat red;
    destruct 1; eexists; eapply H; eauto.
  Qed.

End temporal_exists.