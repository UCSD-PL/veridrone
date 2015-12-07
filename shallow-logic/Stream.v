Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Coq.Lists.List.

Set Implicit Arguments.
Set Strict Implict.

Section with_state.

  Variable ST : Type.
  Variable ST_eq : ST -> ST -> Prop.

  (* A trace is an infinite stream of states. *)
  Definition trace : Type := nat -> ST.

  Definition trace_eq (tr1 tr2 : trace) :=
    forall n, ST_eq (tr1 n) (tr2 n).

  Definition hd (tr : trace) : ST := tr 0.

  Definition tl (tr : trace) : trace := fun n => tr (S n).

  Definition nth_suf (tr : trace) (n : nat) : trace :=
    fun m => tr (n + m).

  Global Instance Proper_hd : Proper (trace_eq ==> ST_eq) hd.
  Proof. do 2 red. intros. apply H. Qed.

  Global Instance Proper_tl :
    Proper (trace_eq ==> trace_eq) tl.
  Proof.
    do 2 red. intros. unfold tl, trace_eq in *.
    intros. specialize (H (S n)). auto.
  Qed.

  Global Instance Reflexive_trace_eq
         {Refl_r : Reflexive ST_eq} : Reflexive trace_eq.
  Proof. red. red. reflexivity. Qed.

  Global Instance Symmetric_trace_eq
         {Sym_r : Symmetric ST_eq} : Symmetric trace_eq.
  Proof. red. red. auto. Qed.

  Global Instance Transitive_trace_eq
         {Trans_r : Transitive ST_eq} : Transitive trace_eq.
  Proof. red. red. intros. etransitivity; eauto. Qed.

  Global Instance PreOrder_trace_eq (PO : PreOrder ST_eq)
  : PreOrder trace_eq.
  Proof.
    destruct PO.
    constructor.
    { eapply Reflexive_trace_eq. }
    { eapply Transitive_trace_eq. }
  Qed.

End with_state.

(* Functorial *)
Section functorial.
  Context {state1 state2 : Type}.
  Variable morphism : state2 -> state1.

  Definition fmap_trace (tr : @trace state2)
    :  @trace state1 :=
    fun n => morphism (tr n).

End functorial.

Theorem fmap_continue_compose :
  forall A B C (f : B -> C) (g : A -> B) (tr : trace _),
    trace_eq eq
             (fmap_trace f (fmap_trace g tr))
             (fmap_trace (fun x => f (g x)) tr).
Proof. reflexivity. Qed.

Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.

Instance Functor_trace : Functor trace :=
{ fmap := fun _ _ mor tr => fmap_trace mor tr }.

Definition forever {T} (v : T) : trace T := fun _ => v.

Definition trace_ap {T U : Type}
           (f : trace (T -> U)) (x : trace T) : trace U :=
  fun n => (f n) (x n).

Instance Applicative_trace : Applicative trace :=
{ pure := @forever
; ap := @trace_ap
}.

Definition trace_zip {T U V : Type}
           (f : T -> U -> V) (a : trace T) (b : trace U)
  : trace V :=
  ap (ap (pure f) a) b.

Arguments hd {ST} _.
Arguments tl {ST} _ _.

Section extra_trace_properties.
  Context {T U V : Type} (Rt : T -> T -> Prop)
          (Ru : U -> U -> Prop) (Rv : V -> V -> Prop).

  Lemma trace_eq_equiv : forall (a b c d : trace T),
      trace_eq Rt b c ->
      trace_eq eq a b ->
      trace_eq eq c d ->
      trace_eq Rt a d.
  Proof.
    intros. intro n.
    specialize (H0 n). specialize (H1 n).
    rewrite H0. rewrite <- H1. auto.
  Qed.

  Global Instance Proper_trace_eq :
    Proper (trace_eq eq ==> trace_eq eq ==> iff)
           (trace_eq Rt).
  Proof.
    do 3 red. split; intros.
    - eapply trace_eq_equiv; eauto. symmetry; eauto.
    - eapply trace_eq_equiv; eauto. symmetry; eauto.
  Qed.

  Lemma fmap_trace_eq : forall f g,
      (Rt ==> Ru)%signature f g ->
      forall (a d : trace U) (b c : trace T),
        trace_eq Rt b c ->
        trace_eq eq a (fmap f b) ->
        trace_eq eq (fmap g c) d ->
        trace_eq Ru a d.
  Proof.
    intros f g Hf. intros. intro n.
    specialize (H0 n). specialize (H1 n).
    rewrite H0. rewrite <- H1.
    apply Hf. auto.
  Qed.

  Global Instance Proper_fmap_trace_eq :
    Proper ((Rt ==> Ru) ==> trace_eq Rt ==> trace_eq Ru)
           (@fmap _ _ _ _).
  Proof.
    do 3 red. intros.
    eapply fmap_trace_eq; solve [ eassumption | reflexivity ].
  Qed.

  Lemma trace_eq_trace_zip (f g : T -> U -> V) :
    (Rt ==> Ru ==> Rv)%signature f g ->
    forall a b c d X Y,
      trace_eq Rt a b ->
      trace_eq Ru c d ->
      trace_eq eq X (trace_zip f a c) ->
      trace_eq eq (trace_zip g b d) Y ->
      trace_eq Rv X Y.
  Proof.
    intro Hfg. intros. intro n.
    specialize (H1 n). specialize (H2 n).
    rewrite H1. rewrite <- H2.
    apply Hfg; auto.
  Qed.

  Global Instance Proper_trace_zip :
    Proper ((Rt ==> Ru ==> Rv) ==> trace_eq Rt ==>
            trace_eq Ru ==> trace_eq Rv) trace_zip.
  Proof.
    do 4 red. intros.
    eapply trace_eq_trace_zip;
      solve [ eassumption | reflexivity ].
  Qed.

  Lemma fmap_trace_trace_zip_compose' {W}
        (Rw : W -> W -> Prop) (f f' : T -> U -> V)
        (g g' : V -> W) :
    (Rt ==> Ru ==> Rv)%signature f f' ->
    (Rv ==> Rw)%signature g g' ->
    forall a b c d X Y,
      trace_eq Rt a b ->
      trace_eq Ru c d ->
      trace_eq eq X (fmap_trace g (trace_zip f a c)) ->
      trace_eq eq (trace_zip (fun a b => g' (f' a b)) b d) Y ->
      trace_eq Rw X Y.
  Proof.
    intros Hf Hg. intros. intro n.
    specialize (H1 n). specialize (H2 n).
    rewrite H1. rewrite <- H2.
    apply Hg. apply Hf; auto.
  Qed.

End extra_trace_properties.

Theorem fmap_trace_trace_zip_compose {T U V W}
        (f : T -> U -> V) (g : V -> W) :
  forall a b,
    trace_eq eq (fmap_trace g (trace_zip f a b))
             (trace_zip (fun a b => g (f a b)) a b).
Proof.
  intros.
  eapply fmap_trace_trace_zip_compose'
  with (Rt := eq) (Ru := eq) (Rv :=eq);
    try solve [ eassumption | reflexivity ].
Qed.