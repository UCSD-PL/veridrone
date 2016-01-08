Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.Ranalysis4.
Require Import Coq.micromega.Psatz.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rtrigo_def.
Require Import Coq.Reals.Reals.
Require Import SLogic.Tactics.

Definition strict_increasing_bound
           (f : R -> R) (bound : R) : Prop :=
  forall x y, (bound <= x < y -> f x < f y)%R.

Definition decreasing_bound
           (f : R -> R) (bound : R) : Prop :=
  forall x y, (bound <= x <= y -> f y <= f x)%R.

Definition K_fun (f : R -> R) : Prop :=
  continuity f /\ strict_increasing_bound f R0 /\ f R0 = R0.

(* I couldn't find a definition in the standard library
   for the limit at infinity. *)
Definition limit_pos_inf (f : R -> R) (l : R) : Prop :=
  forall epsilon, (epsilon > 0)%R ->
    exists M, (M > 0)%R /\
      (forall x, x > M -> Rabs (f x - l) < epsilon)%R.

Definition unbounded (f : R -> R) : Prop :=
  (forall N, N > 0 ->
     exists M, (M > 0)%R /\
       forall x, x > M -> f(x) > N)%R.

Definition K_inf_fun (f : R -> R) : Prop :=
  K_fun f /\ unbounded f.

(* This is not the same as the definition of L functions
   from the Tabuada paper. In particular, we only require
   that the function be decreasing, not strictly decreasing.
   I think that if you require the function to be strictly
   decreasing, then there are no KLD functions. Moreover,
   I think that our definition of L function is the
   standard one from control theory. *)
Definition L_fun (f : R -> R) : Prop :=
  continuity f /\ decreasing_bound f R0 /\
  limit_pos_inf f R0.

Definition KL_fun (f : R -> R -> R) : Prop :=
  (forall t, (0 <= t)%R -> K_fun (fun c => f c t)) /\
  (forall c, (0 <= c)%R -> L_fun (fun t => f c t)).

Definition KLD_fun (f : R -> R -> R) : Prop :=
  KL_fun f /\
  forall (c : R),
    (0 <= c)%R ->
    f c 0%R = c /\
    forall (s t : R),
      (0 <= s)%R -> (0 <= t)%R ->
      (f c (s + t) = f (f c s) t)%R.

(* Now some useful properties of these functions. *)

Lemma K_fun_pos :
  forall f, K_fun f ->
            forall r, (0 <= r)%R ->
                      (0 <= f r)%R.
Proof.
  unfold K_fun, strict_increasing_bound. intros.
  destruct H as [? [Hincr HR0]].
  rewrite <- HR0. destruct H0.
  { specialize (Hincr R0 r). psatzl R. }
  { rewrite H0. psatzl R. }
Qed.

Lemma KL_fun_pos :
  forall f, KL_fun f ->
            forall r1 r2,
              (0 <= r1)%R -> (0 <= r2)%R ->
              (0 <= f r1 r2)%R.
Proof.
  unfold KL_fun. intros.
  destruct H as [HK ?].
  specialize (HK r2 H1).
  eapply K_fun_pos in HK; eauto.
Qed.

Lemma KLD_fun_pos :
  forall f, KLD_fun f ->
            forall r1 r2,
              (0 <= r1)%R -> (0 <= r2)%R ->
              (0 <= f r1 r2)%R.
Proof.
  unfold KLD_fun. intros.
  apply KL_fun_pos; tauto.
Qed.

Lemma KLD_fun_increasing_nonneg :
  forall f,
    KLD_fun f ->
    forall t, (0 <= t)%R ->
              strict_increasing_bound (fun x => f x t) R0.
Proof.
  intros. unfold KLD_fun, KL_fun, K_fun in *.
  intuition. specialize (H t).
  specialize_arith_hyp H. tauto.
Qed.

Lemma KLD_fun_0 :
  forall f,
    KLD_fun f ->
    forall t, (0 <= t)%R ->
              f R0 t = R0.
Proof.
  unfold KLD_fun, KL_fun, K_fun, L_fun. intros.
  intuition.
  (* This requires reasoning about infinite limits. *)
Admitted.

Lemma continuity_id :
  continuity id.
Proof.
  apply derivable_continuous; apply derivable_id.
Qed.

Lemma continuity_exp :
  continuity exp.
Proof.
  apply derivable_continuous; apply derivable_exp.
Qed.

(* TODO: move *)
(* Proves continuity facts of real-valued functions. *)
Ltac prove_continuity :=
  repeat first [ apply continuity_plus |
                 apply continuity_opp |
                 apply continuity_minus |
                 apply continuity_mult |
                 solve [apply continuity_const; congruence] |
                 apply continuity_scal |
                 apply continuity_inv |
                 apply continuity_div |
                 apply continuity_id |
                 apply continuity_exp |
                 apply Ranalysis4.Rcontinuity_abs ].

Lemma Rabs_involutive :
  forall r, Rabs (Rabs r) = Rabs r.
Proof.
  intros. apply Rabs_pos_eq; apply Rabs_pos.
Qed.

Local Open Scope R_scope.

Lemma K_fun_id :
  K_fun Ranalysis1.id.
Proof.
  split.
  { prove_continuity. }
  { unfold strict_increasing_bound, Ranalysis1.id.
    split; intros; psatzl R. }
Qed.

Lemma K_fun_mult :
  forall f1 f2,
    K_fun f1 -> K_fun f2 ->
    K_fun (fun x => f1 x * f2 x).
Proof.
  unfold K_fun; intros; split.
  { prove_continuity; tauto. }
  { unfold strict_increasing_bound in *. intuition.
    pose proof (H0 x y). pose proof (H2 x y).
    specialize_arith_hyp H3. specialize_arith_hyp H8.
    specialize (H0 0 x). specialize (H2 0 x).
    destruct H6.
    { specialize_arith_hyp H0. specialize_arith_hyp H2.
      psatz R. }
    { subst. psatz R. } }
Qed.

Lemma K_fun_scale :
  forall f c,
    K_fun f -> 0 < c ->
    K_fun (fun x => c * f x).
Proof.
  unfold K_fun. intros. split.
  { prove_continuity; tauto. }
  { unfold strict_increasing_bound in *. intuition. }
Qed.

Lemma K_inf_fun_id :
  K_inf_fun Ranalysis1.id.
Proof.
  split.
  { apply K_fun_id. }
  { unfold unbounded, id. intros. eauto. }
Qed.

Lemma K_inf_fun_scale :
  forall f c,
    K_inf_fun f -> 0 < c ->
    K_inf_fun (fun x => c * f x).
Proof.
  unfold K_inf_fun. intros. split.
  { apply K_fun_scale; tauto. }
  { unfold unbounded in *. intros.
    assert (/c > 0) by (apply Rinv_0_lt_compat; assumption).
    assert (N / c > 0) by (unfold Rdiv; psatz R).
    destruct H. specialize (H4 _ H3).
    destruct H4. destruct H4.
    exists x. split; auto. intros. specialize (H5 _ H6).
    apply Rlt_gt. apply (Rmult_lt_reg_l (/c)); [ psatzl R | ].
    rewrite <- Rmult_assoc. rewrite <- Rinv_l_sym; psatzl R. }
Qed.

Lemma KL_fun_abs_exp :
  forall a,
    0 < a ->
    KL_fun (fun d t => Rabs d * exp (-t * a)).
Proof.
  repeat split.
  { prove_continuity. }
  { unfold strict_increasing_bound. intros.
    pose proof (Exp_prop.exp_pos (-t * a)).
    repeat (rewrite Rabs_right;
            [ | solve [psatzl R ] ]).
    psatz R. }
  { rewrite Rabs_R0. psatzl R. }
  { prove_continuity.
    apply continuity_comp with (f1:=fun x => -x * a)
                                 (f2:=exp);
      prove_continuity. }
  { unfold decreasing_bound. intros.
    destruct H1. destruct H2.
    { pose proof (exp_increasing (-y * a) (-x * a)).
      pose proof (Rabs_pos c).
      assert (- y * a < - x * a) by psatz R.
      pose proof (exp_pos (-y * a)).
      intuition.
    (* I don't understand
             how this solves the goal. *) }
    { subst. intuition. } }
  { unfold limit_pos_inf. intros.
    admit. (* Need some limit lemmas. *) }
Qed.

Lemma KLD_fun_abs_exp :
  forall a,
    0 < a ->
    KLD_fun (fun d t => Rabs d * exp (-t * a)).
Proof.
  split.
  { apply KL_fun_abs_exp; assumption. }
  { repeat split.
    { intros.
      rewrite RIneq.Ropp_0. rewrite Rmult_0_l. rewrite exp_0.
      rewrite RIneq.Rmult_1_r.
      apply Rabs_pos_eq; assumption. }
    { intros. rewrite RIneq.Ropp_plus_distr.
      rewrite Rmult_plus_distr_r. rewrite Exp_prop.exp_plus.
      rewrite Rabs_mult. rewrite Rabs_involutive.
      rewrite Rabs_pos_eq with (x:=exp (-s * a));
        [ | left; apply Exp_prop.exp_pos ].
      psatzl R. } }
Qed.
