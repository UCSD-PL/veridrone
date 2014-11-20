Require Import TLA.Tactics.
Require Import Rdefinitions.

Lemma Rmult_0_le : forall r1 r2,
  (0 <= r1 -> 0 <= r2 ->
   0 <= r1*r2)%R.
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