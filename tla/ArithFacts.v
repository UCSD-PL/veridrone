Require Import Coq.Reals.Reals.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.

(* Some obvious but useful real arithmetic
   facts. *)

Lemma Rmult_0_le : forall r1 r2,
  (0 <= r1 -> 0 <= r2 ->
   0 <= r1*r2)%R.
Proof. solve_nonlinear. Qed.

Lemma Rmult_0_lt : forall r1 r2,
  (0 < r1 -> 0 < r2 ->
   0 < r1*r2)%R.
Proof. solve_nonlinear. Qed.

Lemma pow_0_le : forall r,
  (0 <= r * (r * 1))%R.
Proof. solve_nonlinear. Qed.

Lemma Rmult_le_0 : forall r1 r2,
  (0 <= r1 -> r2 <= 0 ->
   r1 * r2 <= 0)%R.
Proof. solve_nonlinear. Qed.

Lemma Rle_sq_pos : forall r1 r2,
  (0 <= r1 -> 0 <= r2 -> r1 <= r2 ->
   r1*(r1*1) <= r2*(r2*1))%R.
Proof. solve_nonlinear. Qed.

Lemma Rmult_minus_distr_r : forall r1 r2 r3,
  (eq ((r1 - r2)*r3) (r1*r3 - r2*r3))%R.
Proof. solve_linear. Qed.

Lemma Rmult_le_compat_neg_r : forall r r1 r2 : R,
 (r <= 0)%R -> (r1 <= r2)%R -> (r2*r <= r1*r)%R.
Proof. solve_nonlinear. Qed.

Lemma Rmult_le_compat_pos_r : forall r r1 r2 : R,
 (r >= 0)%R -> (r1 <= r2)%R -> (r1*r <= r2*r)%R.
Proof. solve_nonlinear. Qed.

Lemma inv_le_0 : forall r,
  (r < 0 -> /r <= 0)%R.
Proof. solve_nonlinear. Qed.

Lemma inv_0_le : forall r,
  (0 < r -> 0 <= /r)%R.
Proof. solve_nonlinear. Qed.

Lemma Rmult_le_lt_0 : forall r1 r2,
  (0 < r1 -> 0 <= r1*r2 -> 0 <= r2)%R.
Proof. solve_nonlinear. Qed.

Lemma Rplus_le_algebra : forall r1 r2,
  (r1 - r2 <= 0 -> r1 <= r2)%R.
Proof. solve_linear. Qed.

Lemma Rmult_neg_le_algebra : forall r1 r2,
  (r2 < 0 -> r1*r2 >= 0 -> r1 <= 0)%R.
Proof. solve_nonlinear. Qed.

Lemma Rmult_neg_ge_algebra : forall r1 r2,
  (r2 < 0 -> r1*r2 <= 0 -> r1 >= 0)%R.
Proof. solve_nonlinear. Qed.

Lemma Rmult_pos_ge_algebra : forall r1 r2,
  (r2 > 0 -> r1*r2 >= 0 -> r1 >= 0)%R.
Proof. solve_nonlinear. Qed.

Lemma Rmult_pos_le_algebra : forall r1 r2,
  (r2 > 0 -> r1*r2 <= 0 -> r1 <= 0)%R.
Proof. solve_nonlinear. Qed.

Lemma Rmult_le_compat_3pos1:
  forall r1 r2 r3 r4 : R,
  (0 <= r2)%R -> (0 <= r3)%R ->
  (0 <= r4)%R -> (r1 <= r2)%R ->
  (r3 <= r4)%R -> (r1 * r3 <= r2 * r4)%R.
Proof. solve_nonlinear. Qed.

Lemma Rmult_le_compat_3pos2:
  forall r1 r2 r3 r4 : R,
  (0 <= r1)%R -> (0 <= r2)%R ->
  (0 <= r3)%R -> (r1 <= r2)%R ->
  (r3 <= r4)%R -> (r1 * r3 <= r2 * r4)%R.
Proof. solve_nonlinear. Qed.

Lemma Rplus_rewrite_l : forall r1 r2 r3 r4,
  (r1 <= r2 -> r2 + r3 <= r4 -> r1 + r3 <= r4)%R.
Proof. solve_linear. Qed.

Lemma Rplus_le_r : forall r1 r2,
  (0 <= r2 -> r1 <= r1 + r2)%R.
Proof. solve_linear. Qed.

Lemma Rplus_le_l : forall r1 r2,
  (r2 <= 0 -> r1 + r2 <= r1)%R.
Proof. solve_linear. Qed.

Lemma Rminus_le_algebra : forall r1 r2 r3,
  (r1 <= r2 + r3 -> r1 - r2 <= r3)%R.
Proof. solve_linear. Qed.

Lemma Rmult_le_algebra : forall r1 r2 r3,
  (r2 > 0 -> r1 <= r2*r3 -> r1 * (/r2) <= r3)%R.
Proof.
  intros.
  apply (Rmult_le_reg_r r2); solve_linear.
  rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym; solve_linear.
Qed.

Lemma Rmult_le_algebra2 : forall r1 r2 r3,
  (r2 > 0 -> r1 * r2 <= r3 -> r1 <= r3 * (/r2))%R.
Proof.
  intros.
  apply (RIneq.Rmult_le_reg_r r2); solve_linear.
  rewrite Raxioms.Rmult_assoc.
  rewrite <- RIneq.Rinv_l_sym; solve_linear.
Qed.

Lemma Rmult_lt_algebra : forall r1 r2 r3,
  (r2 > 0 -> r1 < r3 * r2 -> r1 * (/r2) < r3)%R.
Proof.
  intros.
  apply (RIneq.Rmult_lt_reg_r r2); solve_linear.
  rewrite Raxioms.Rmult_assoc.
  rewrite <- RIneq.Rinv_l_sym; solve_linear.
Qed.

Lemma Rmult_lt_algebra2 : forall r1 r2 r3,
  (r2 > 0 -> r1 * r2 < r3 -> r1 < r3 * (/r2))%R.
Proof.
  intros.
  apply (RIneq.Rmult_lt_reg_r r2); solve_linear.
  rewrite Raxioms.Rmult_assoc.
  rewrite <- RIneq.Rinv_l_sym; solve_linear.
Qed.

Lemma algebra1 : forall r1 r2 r3 r4,
  (r3 > 0 -> r1 <= r2 + r3*r4 -> (r1-r2)*/r3 <= r4)%R.
Proof.
  intros.
  apply Rminus_le_algebra in H0.
  apply Rmult_le_algebra in H0; auto.
Qed.

Lemma sqr_le_compat :
  forall r1 r2,
    (0 <= r1 -> 0 <= r2 ->
     r1 * r1 <= r2 * r2 ->
     r1 <= r2)%R.
Proof.
  intros; apply Rsqr_incr_0; solve_linear.
Qed.

Lemma sqr_lt_compat :
  forall r1 r2,
    (0 <= r1 -> 0 <= r2 ->
     r1 * r1 < r2 * r2 ->
     r1 < r2)%R.
Proof.
  intros; apply Rsqr_incrst_0; solve_linear.
Qed.

Lemma sin_atan : forall x,
  Rtrigo_def.sin (Ratan.atan x) =
  (x/R_sqrt.sqrt (1 + x*x))%R.
Admitted.

Lemma cos_atan : forall x,
  Rtrigo_def.cos (Ratan.atan x) =
  (1/R_sqrt.sqrt (1 + x*x))%R.
Admitted.

Lemma tan_increasing_1 :
  forall r1 r2,
    (-PI/2 < r1 < PI/2 ->
     -PI/2 < r2 < PI/2 ->
     tan r1 <= tan r2 ->
     r1 <= r2)%R.
Admitted.

Lemma cos_pos :
  forall x,
    (cos x > 0 ->
     -PI <= x <= PI ->
     -PI/2 < x < PI/2)%R.
Admitted.

Lemma rectangular_to_polar :
  forall (x y:R),
    { p : (R*R) |
      (0 <= fst p /\ -PI < snd p <= PI /\
       eq x ((fst p) * Rtrigo_def.cos (snd p)) /\
       eq y ((fst p) * Rtrigo_def.sin (snd p)))%R }.
Admitted.

Lemma atan_tan :
  forall x,
    (-PI/2 < x < PI/2 ->
     atan (tan x) = x)%R.
Proof.
  unfold atan. intros.
  destruct (pre_atan (tan x)).
  apply tan_is_inj; tauto.
Qed.

Lemma arctan_constraint_refinement :
  forall x y theta b,
    (-b <= y -> b < 0 ->
     -b*tan theta <= x <= b*tan theta ->
     -PI/2 < theta < 0 ->
     theta <= atan (x / y) <= -theta)%R.
Proof.
  intros.
  assert (tan theta < 0)%R
    by (apply tan_lt_0; solve_linear).
  split.
  { apply tan_increasing_1.
    { solve_linear. }
    { pose proof atan_bound as Hatan.
      match goal with
        |- context [atan ?e] => specialize (Hatan e)
      end. solve_linear. }
    { rewrite atan_right_inv.
      generalize dependent (tan theta).
      intuition. apply Rmult_le_algebra2; solve_linear.
      solve_nonlinear. } }
  { apply tan_increasing_1.
    { pose proof atan_bound as Hatan.
      match goal with
        |- context [atan ?e] => specialize (Hatan e)
      end. solve_linear. }
    { solve_linear. }
    { rewrite atan_right_inv.
      rewrite tan_neg.
      generalize dependent (tan theta).
      intuition. apply Rmult_le_algebra; solve_linear.
      eapply RIneq.Rle_trans; eauto.
      solve_nonlinear. } }
Qed.

Lemma mult_0_l_equiv :
  forall x,
    term_equiv (0*x) 0.
Proof. unfold term_equiv; solve_linear. Qed.
Lemma mult_0_r_equiv :
  forall x,
    term_equiv (x*0) 0.
Proof. unfold term_equiv; solve_linear. Qed.
Lemma plus_0_r_equiv :
  forall x,
    term_equiv (x+0) x.
Proof. unfold term_equiv; solve_linear. Qed.
Lemma plus_0_l_equiv :
  forall x,
    term_equiv (0+x) x.
Proof. unfold term_equiv; solve_linear. Qed.
Lemma minus_0_r_equiv :
  forall x,
    term_equiv (x-0) x.
Proof. unfold term_equiv; solve_linear. Qed.
Lemma minus_0_l_equiv :
  forall x,
    term_equiv (0%R-x) --x.
Proof. unfold term_equiv; solve_linear. Qed.

Local Open Scope HP_scope.
Lemma minus_eq :
  forall x y,
    --x = --y -|- x = y.
Proof. split; solve_linear. Qed.

Ltac tla_rewrite_0 :=
  repeat first
         [ rewrite mult_0_l_equiv
         | rewrite mult_0_r_equiv
         | rewrite plus_0_l_equiv
         | rewrite plus_0_r_equiv
         | rewrite minus_0_l_equiv
         | rewrite minus_0_r_equiv ].

Lemma Rmin_Lt :
  forall r1 r2 t,
    t <= Rbasic_fun.Rmin r1 r2 -|- t <= r1 //\\ t <= r2.
Proof.
  intros; split; unfold Rbasic_fun.Rmin; destruct_ite; solve_linear.
Qed.

Lemma leq_eq_refine :
  forall t1 t2,
    t1 = t2 |-- t1 <= t2.
Proof. solve_linear. Qed.

Lemma neg_eq :
  forall t1 t2,
    t1 = -- t2 -|- --t1 = t2.
Proof. split; solve_linear. Qed.

Require Import Coq.Classes.RelationClasses.
Require Import RIneq.
Global Instance Reflexive_Rge : Reflexive Rge.
Proof.
  red. intro. apply Req_ge. reflexivity.
Qed.

Global Instance Reflexive_Rle : Reflexive Rle.
Proof.
  red. intro. apply Req_ge. reflexivity.
Qed.

Require Import Setoid Relation_Definitions Reals.
Local Open Scope R.

Add Parametric Relation : R Rle
reflexivity proved by Rle_refl
transitivity proved by Rle_trans
as Rle_setoid_relation.

Add Parametric Morphism : Rplus with
signature Rle ++> Rle ++> Rle as Rplus_Rle_mor.
intros ; apply Rplus_le_compat ; assumption.
Qed.

Add Parametric Morphism : Rminus with
signature Rle ++> Rle --> Rle as Rminus_Rle_mor.
intros ; unfold Rminus ;
apply Rplus_le_compat;
[assumption | apply Ropp_le_contravar ; assumption].
Qed.
