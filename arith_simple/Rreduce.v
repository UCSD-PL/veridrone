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

  Fixpoint Rexpr_well_formed (r : Rexpr) : Prop :=
    match r with
    | Plus a b => Rexpr_well_formed a /\ Rexpr_well_formed b
    | Mult a b => Rexpr_well_formed a /\ Rexpr_well_formed b
    | Inv a => (RexprD a <> 0)%R /\ Rexpr_well_formed a
    | Opp a => Rexpr_well_formed a
    | _ => True
    end.

  Definition simplify_hd (r : Rexpr) : Rexpr :=
    match r with
    | Plus r Zero => r
    | Plus Zero r => r
    | Mult r Zero => Zero
    | Mult Zero r => Zero
    | Mult One r => r
    | Mult r One => r
    | Opp (Opp r) => r
    | Inv (Inv r) => r
    | _ => r
    end.

  Require Import Coq.micromega.Psatz.

  Lemma simplify_hd_sound : forall r,
      Rexpr_well_formed r ->
      RexprD (simplify_hd r) = RexprD r /\
      Rexpr_well_formed (simplify_hd r).
  Proof.
    destruct r; simpl; auto.
    { destruct r1; destruct r2; simpl; auto; split; solve [ tauto | psatzl R ]. }
    { destruct r1; destruct r2; simpl; auto; split; solve [ tauto | psatzl R ]. }
    { destruct r; simpl; intros; split; try solve [ tauto | psatzl R ].
      rewrite RIneq.Rinv_involutive; eauto. tauto. }
    { destruct r; simpl; split; solve [ tauto | psatzl R ]. }
  Qed.

  Definition lcm_factor (l r : Rexpr) : Rexpr * Rexpr * Rexpr :=
    if Rexpr_eq l r then (l, One, One) else (simplify_hd (Mult l r), r, l).

  Lemma lcm_factor_sound : forall l r d lf rf,
      lcm_factor l r = (d, lf, rf) ->
      Rexpr_well_formed l ->
      Rexpr_well_formed r ->
      (RexprD l <> 0)%R ->
      (RexprD r <> 0)%R ->
      (RexprD d = RexprD lf * RexprD l /\
       RexprD d = RexprD rf * RexprD r)%R /\
      Rexpr_well_formed d /\ Rexpr_well_formed lf /\ Rexpr_well_formed rf /\
      (RexprD d <> 0)%R /\ (RexprD lf <> 0)%R /\ (RexprD rf <> 0)%R.
  Proof.
    unfold lcm_factor. intros.
    generalize (Rexpr_eq_sound l r).
    destruct (Rexpr_eq l r); intros.
    { inversion H; clear H; subst.
      specialize (H4 eq_refl). subst.
      simpl. repeat split; try solve [ tauto | try psatzl R ]. }
    { clear H4.
      generalize (simplify_hd_sound (Mult l r)).
      generalize dependent (simplify_hd (Mult l r)).
      intros. inversion H; clear H; subst.
      simpl in *.
      destruct H4; [ tauto | ].
      rewrite <- H.
      repeat split; try tauto. psatzl R. rewrite H.
      eapply RIneq.Rmult_integral_contrapositive; tauto. }
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
      (simplify_hd (Mult a c), simplify_hd (Mult b d))
    | Inv r => let (a,b) := simplify r in (b,a)
    | Opp r => let (a,b) := simplify r in (Opp a, b)
    | Zero => (Zero, One)
    | One => (One, One)
    | Opaque v => (Opaque v, One)
    end.

  Lemma mult_both_eq : forall a b c : R,
      (c <> 0 ->
       a * c = b * c ->
       a = b)%R.
  Proof. intros. psatz R. Qed.


  Theorem simplify_sound : forall r n d,
      simplify r = (n,d) ->
      Rexpr_well_formed r ->
      (RexprD r = RexprD n * / RexprD d)%R /\
      Rexpr_well_formed n /\ Rexpr_well_formed d /\ (RexprD d <> 0)%R.
  Proof.
    unfold simplify.
    generalize simplify_hd_sound.
    generalize dependent simplify_hd.
    intros simplify_hd Hsimplify_hd_sound.
    generalize lcm_factor_sound.
    generalize dependent lcm_factor.
    intros lcm_factor Hlcm_factor_sound.
    induction r; simpl; intros;
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           | H : (_,_) = (_,_) |- _ => inversion H; clear H; subst
           | H : forall x y, ?X = (_,_) -> _
           , H' : (match ?X with (_,_) => _ end) = _ |- _ =>
             destruct X; specialize (H _ _ eq_refl);
             let Hx := fresh in destruct H as [ Hx ? ] ;
               [ tauto | try rewrite Hx ]
           | H : match lcm_factor ?X ?Y with (_,_) => _ end = _ |- _ =>
             generalize (Hlcm_factor_sound X Y) ;
               destruct (lcm_factor X Y) as [ [ ? ? ] ? ] ;
               let Hx := fresh in
               intro Hx ;
               destruct (Hx _ _ _ eq_refl) ;
               [ tauto | tauto | tauto | tauto | clear Hx ]
           | |- context [ simplify_hd ?X ] =>
             let Hx := fresh in
             destruct (Hsimplify_hd_sound X) as [ Hx ? ] ;
               [ simpl ; tauto
               | generalize dependent (simplify_hd X); intros ]
           | H : _ = _ |- _ => rewrite H in *
           end; try (split; [ simpl; try psatzl R
                            | try tauto ]).
    { simpl in *.
      rewrite H19; clear H19.
      rewrite H; clear H.
      eapply mult_both_eq. eapply H14.
      rewrite RIneq.Rmult_plus_distr_r.
      repeat rewrite Raxioms.Rmult_assoc.
      rewrite <- RIneq.Rinv_l_sym; eauto.
      rewrite <- H11 at 2.
      repeat rewrite <- Raxioms.Rmult_assoc.
      clear - H5 H9.
      symmetry. rewrite Raxioms.Rmult_comm.
      rewrite Raxioms.Rmult_1_l.
      f_equal.
      { repeat rewrite Raxioms.Rmult_assoc.
        rewrite Raxioms.Rmult_comm.
        f_equal.
        rewrite <- Raxioms.Rmult_assoc.
        rewrite Raxioms.Rmult_comm.
        rewrite <- Raxioms.Rmult_assoc.
        rewrite RIneq.Rinv_r; auto.
        psatzl R. }
      { repeat rewrite Raxioms.Rmult_assoc.
        rewrite Raxioms.Rmult_comm.
        f_equal.
        rewrite <- Raxioms.Rmult_assoc.
        rewrite Raxioms.Rmult_comm.
        rewrite <- Raxioms.Rmult_assoc.
        rewrite RIneq.Rinv_r; auto.
        psatzl R. } }
    { rewrite RIneq.Rinv_mult_distr; try assumption.
      psatzl R. }
    { repeat split; try assumption.
      simpl. eapply RIneq.Rmult_integral_contrapositive; tauto. }
    { eapply RIneq.Rmult_neq_0_reg in H0. destruct H0.
      rewrite RIneq.Rinv_mult_distr; eauto.
      rewrite RIneq.Rinv_involutive; eauto. psatzl R. }
    { eapply RIneq.Rmult_neq_0_reg in H0. destruct H0.
      tauto. }
    { simpl. split; auto; split; auto. psatzl R. }
    { simpl. split; auto; split; auto. psatzl R. }
    { simpl. split; auto; split; auto. psatzl R. }
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