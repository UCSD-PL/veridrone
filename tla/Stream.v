Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

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

  Lemma trace_eta : forall (tr : stream),
      tr = Cons (hd tr) (tl tr).
  Proof. destruct tr. reflexivity. Qed.

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

  Global Instance Reflexive_stream_eq (r : A -> A -> Prop) (Refl : Reflexive r)
    : Reflexive (stream_eq r).
  Proof.
    red. cofix CIH.
    intro. constructor. reflexivity. eapply CIH.
  Qed.

  Global Instance Symmetric_stream_eq (r : A -> A -> Prop) (Sym : Symmetric r)
  : Symmetric (stream_eq r).
  Proof.
    red. cofix CIH.
    intros. eapply stream_eq_eta in H. destruct H.
    constructor.
    { symmetry. tauto. }
    { eapply CIH. eapply H0. }
  Qed.

  Global Instance Transitive_stream_eq (r : A -> A -> Prop) (Trans : Transitive r)
    : Transitive (stream_eq r).
  Proof.
    red. cofix CIH.
    intros.
    eapply stream_eq_eta in H.
    eapply stream_eq_eta in H0.
    destruct H; destruct H0.
    constructor.
    { etransitivity; eassumption. }
    { eapply CIH; eassumption. }
  Qed.

  Lemma Proper_nth_suf_stream_eq (r : A -> A -> Prop)
    : Proper (eq ==> stream_eq r ==> stream_eq r) (nth_suf).
  Proof.
    red. red. intros; subst. red.
    induction y; simpl; eauto.
    intros. eapply IHy.
    eapply stream_eq_eta in H. tauto.
  Qed.

  Global Instance Cons_Proper :
    Proper (eq ==>
               stream_eq eq ==> stream_eq eq) Cons.
  Proof.
    repeat red.
    constructor; auto.
  Qed.

  CoFixpoint forever (v : A) : stream :=
    Cons v (forever v).

End parametric.

Section xxx.
  Context {T U : Type}.
  Variable f : T -> U.

  CoFixpoint stream_map (s : stream T) : stream U :=
    match s with
    | Cons s ss => Cons (f s) (stream_map ss)
    end.

  Lemma stream_map_nth_suf : forall n s r,
    Reflexive r ->
    stream_eq r (nth_suf n (stream_map s))
              (stream_map (nth_suf n s)).
  Proof.
    induction n; intros.
    - reflexivity.
    - destruct s. simpl in *.
      specialize (IHn s r H). auto.
  Qed.

End xxx.

Lemma stream_map_id : forall T (s:stream T) r,
  Reflexive r ->
  stream_eq r (stream_map (fun x => x) s) s.
Proof.
  cofix. intros. destruct s.
  constructor.
  - simpl. auto.
  - simpl. apply stream_map_id. auto.
Qed.

Lemma stream_map_compose :
  forall T U V (f : T -> U) (g : U -> V) r,
    Reflexive r ->
    forall (s:stream T),
      stream_eq r (stream_map g (stream_map f s))
                (stream_map (fun x => g (f x)) s).
Proof.
  intros. revert s. cofix.
  intros. destruct s.
  constructor.
  - auto.
  - simpl. auto.
Qed.

Lemma stream_map_cons : forall T U r (f : T -> U) x y,
    Reflexive r ->
    stream_eq r (stream_map f (Cons x y))
              (Cons (f x) (stream_map f y)).
Proof.
  intros.
  eapply stream_eq_eta. simpl. split; reflexivity.
Qed.


Section xxx2.
  Context {T U : Type}.
  Context {rT : T -> T -> Prop}.
  Context {rU : U -> U -> Prop}.

  Global Instance Proper_stream_map
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

  Lemma stream_map_tl : forall (f : T -> U) (s : stream T) r,
      Equivalence r ->
      stream_eq r (tl (stream_map f s)) (stream_map f (tl s)).
  Proof.
    intros. destruct s; reflexivity.
  Qed.

End xxx2.

Lemma tl_forever : forall T (x:T) r,
  Equivalence r ->
  stream_eq r (tl (forever x)) (forever x).
Proof. reflexivity. Qed.

Lemma stream_map_forever : forall T x (f:T->T) r,
  Equivalence r ->
  stream_eq r (stream_map f (forever x))
            (forever (f x)).
Proof.
  intros. cofix.
  constructor.
  - reflexivity.
  - auto.
Qed.

Arguments Cons {_} _ _.
