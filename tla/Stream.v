Require Import Coq.Classes.Morphisms.

(* A behavior of TLA is an infinite stream
   of states. *)
Set Implicit Arguments.
Set Strict Implicit.

Section parametric.
  Variable A : Type.

  CoInductive stream :=
  | Cons : A -> stream -> stream.

  (* The head of a stream *)
  Definition hd (s:stream) : A :=
    match s with
    | Cons a _ => a
    end.

  (* The tail of a stream *)
  Definition tl (s:stream) : stream :=
    match s with
    | Cons _ s' => s'
    end.

  CoInductive stream_eq (r : A -> A -> Prop)
  : stream -> stream -> Prop :=
  | Cons_eq : forall xs ys,
      r (hd xs) (hd ys) ->
      stream_eq r (tl xs) (tl ys) ->
      stream_eq r xs ys.

  Theorem stream_eq_eta : forall r x y,
      stream_eq r x y <-> (r (hd x) (hd y) /\ stream_eq r (tl x) (tl y)).
  Proof.
    destruct x; destruct y; simpl; split; inversion 1; subst; eauto.
    constructor; eauto.
  Qed.

  (* The nth suffix of a stream *)
  Fixpoint nth_suf (n:nat) (s:stream) : stream :=
    match n with
    | O => s
    | S n => nth_suf n (tl s)
    end.

  Lemma nth_suf_tl : forall n (s:stream),
      nth_suf n (tl s) =
      tl (nth_suf n s).
  Proof.
    induction n; intro s; firstorder.
  Qed.

  Lemma nth_suf_Sn : forall n (s:stream),
      nth_suf (S n) s =
      tl (nth_suf n s).
  Proof.
    induction n; intro s; firstorder.
  Qed.
End parametric.

Section xxx.
  Context {T U : Type}.
  Variable f : T -> U.

  CoFixpoint stream_map (s : stream T) : stream U :=
    match s with
    | Cons s ss => Cons (f s) (stream_map ss)
    end.
End xxx.

Section xxx2.
  Context {T U : Type}.

  Global Instance Proper_stream_map rT rU
  : Proper ((rT ==> rU) ==> stream_eq rT ==> stream_eq rU) (@stream_map T U).
  Proof.
    red. red. red. unfold respectful.
    intros f g Hfg.
    cofix CIH.
    intros.
    destruct x; destruct y.
    eapply stream_eq_eta in H.
    destruct H.
    constructor.
    { eapply Hfg. eapply H. }
    { eapply CIH. eapply H0. }
  Qed.

End xxx2.

Arguments Cons {_} _ _.