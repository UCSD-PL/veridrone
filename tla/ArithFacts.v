Require Import Rdefinitions.
Require Import RIneq.
Require Import TLA.Tactics.

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

Lemma algebra1 : forall r1 r2 r3 r4,
  (r3 > 0 -> r1 <= r2 + r3*r4 -> (r1-r2)*/r3 <= r4)%R.
Proof.
  intros.
  apply Rminus_le_algebra in H0.
  apply Rmult_le_algebra in H0; auto.
Qed.

Require Import Coq.Classes.RelationClasses.
Require Import RIneq.
Instance Reflexive_Rge : Reflexive Rge.
Proof.
  red. intro. apply Req_ge. reflexivity.
Qed.

Instance Reflexive_Rle : Reflexive Rle.
Proof.
  red. intro. apply Req_ge. reflexivity.
Qed.
