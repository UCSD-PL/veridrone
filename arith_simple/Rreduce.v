Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import Peano_dec.

Inductive Rexpr : Type :=
| Plus (_ _ : Rexpr)
| Mult (_ _ : Rexpr)
| Inv (_ : Rexpr)
| Opp (_ : Rexpr)
| Zero
| One
| Opaque : nat -> Rexpr.

Section denote.
  Variable ls : list R.

  Fixpoint RexprD (e : Rexpr) : R :=
    match e with
    | Zero => R0
    | One => R1
    | Opaque n => nth n ls R0
    | Inv r => Rinv (RexprD r)
    | Opp r => Ropp (RexprD r)
    | Plus l r => Rplus (RexprD l) (RexprD r)
    | Mult l r => Rmult (RexprD l) (RexprD r)
    end.

  Fixpoint Rexpr_eq (a b : Rexpr) : bool :=
    match a , b with
    | Plus a b , Plus c d =>
      if Rexpr_eq a c then Rexpr_eq b d else false
    | Mult a b , Mult c d =>
      if Rexpr_eq a c then Rexpr_eq b d else false
    | Inv a , Inv b => Rexpr_eq a b
    | Opp a , Opp b => Rexpr_eq a b
    | Zero , Zero => true
    | One , One => true
    | Opaque a , Opaque b => if eq_nat_dec a b then true else false
    | _ , _ => false
    end.

  Lemma Rexpr_eq_sound : forall a b, Rexpr_eq a b = true -> a = b.
  Proof.
    induction a; destruct b; simpl; intros; eauto; try congruence.
    { specialize (IHa1 b1).
      specialize (IHa2 b2).
      destruct (Rexpr_eq a1 b1); try congruence.
      rewrite IHa1; auto.
      rewrite IHa2; auto. }
    { specialize (IHa1 b1).
      specialize (IHa2 b2).
      destruct (Rexpr_eq a1 b1); try congruence.
      rewrite IHa1; auto.
      rewrite IHa2; auto. }
    { apply IHa in H. congruence. }
    { apply IHa in H. congruence. }
    { destruct (eq_nat_dec n n0); congruence. }
  Qed.

  Definition simplify_hd (r : Rexpr) : Rexpr :=
    match r with
    | Plus r Zero => r
    | Plus Zero r => r
    | Mult r Zero => Zero
    | Mult Zero r => Zero
    | Mult One r => r
    | Mult r One => r
    | Opp (Opp r) => r
(*     | Inv (Inv r) => r  NOT VALID if r = 0 *)
    | _ => r
    end.

  Require Import Coq.micromega.Psatz.

  Lemma simplify_hd_sound : forall r,
      RexprD r = RexprD (simplify_hd r).
  Proof.
    destruct r; simpl; auto.
    { destruct r1; destruct r2; simpl; auto; psatzl R. }
    { destruct r1; destruct r2; simpl; auto; psatzl R. }
    { destruct r; simpl; psatzl R. }
  Qed.

  Definition lcm_factor (l r : Rexpr) : Rexpr * Rexpr * Rexpr :=
    if Rexpr_eq l r then (l, One, One) else (simplify_hd (Mult l r), r, l).

  Lemma lcm_factor_sound : forall l r d lf rf,
      lcm_factor l r = (d, lf, rf) ->
      (RexprD d = RexprD lf * RexprD l /\
       RexprD d = RexprD rf * RexprD r)%R.
  Proof.
    unfold lcm_factor. intros.
    generalize (Rexpr_eq_sound l r).
    destruct (Rexpr_eq l r); intros.
    { inversion H; clear H; subst.
      specialize (H0 eq_refl). subst.
      simpl. split; psatzl R. }
    { clear H0.
      generalize (simplify_hd_sound (Mult l r)).
      generalize dependent (simplify_hd (Mult l r)).
      intros. inversion H; clear H; subst.
      simpl in *.
      rewrite <- H0. split; psatzl R. }
  Qed.

  Fixpoint simplify (r : Rexpr) : Rexpr * Rexpr :=
    match r with
    | Plus l r =>
      let (a,b) := simplify l in
      let (c,d) := simplify r in
      let '(den, lf, rf) := lcm_factor b d in
      (simplify_hd (Plus (simplify_hd (Mult lf a)) (simplify_hd (Mult rf c))),
       den)
    | Mult l r =>
      let (a,b) := simplify l in
      let (c,d) := simplify r in
      (simplify_hd (Mult a c), simplify_hd (Mult c d))
    | Inv r => let (a,b) := simplify r in (b,a)
    | Opp r => let (a,b) := simplify r in (Opp a, b)
    | Zero => (Zero, One)
    | One => (One, One)
    | Opaque v => (Opaque v, One)
    end.

  Theorem simplify_sound : forall r n d,
      simplify r = (n,d) ->
      (RexprD r = RexprD n * / RexprD d)%R.
  Proof.
    generalize simplify_hd_sound.
    generalize lcm_factor_sound.
    unfold simplify.
    generalize dependent simplify_hd.
    generalize dependent lcm_factor.
    induction r0; simpl; intros;
    repeat match goal with
           | H : forall x y, ?X = (_,_) -> _
           , H' : (match ?X with (_,_) => _ end) = _ |- _ =>
             destruct X; specialize (H _ _ eq_refl); try rewrite H
           end.
    { admit. }
    { inversion H1; clear H1; subst.
      repeat rewrite <- H0.
      simpl. (** NOT SOUND when the result is 0 **)
      admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
  Qed.
End denote.

(** this only works for equality, it needs to flip for inequalities *)
Fixpoint mult_common (l r : Rexpr) : Rexpr * Rexpr :=
  let (a,b) := simplify l in
  let (c,d) := simplify r in
  (simplify_hd (Mult a d), simplify_hd (Mult c b)).

Eval vm_compute in simplify (Mult One (Inv (Opaque 0))).
Eval vm_compute in simplify (Mult (Plus Zero One) (Inv (Opaque 0))).
Eval vm_compute in simplify (Plus (Mult (Plus Zero One) (Inv (Opaque 0)))
                                  (Mult (Plus Zero One) (Inv (Opaque 1)))).