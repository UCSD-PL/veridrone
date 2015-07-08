Require Import Rdefinitions.
Require Import RIneq.
Require Import Coq.Reals.Rtrigo1.
Require Import TLA.TLA.
Require Import BasicProofRules.

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

Lemma tan_increasing_2 :
  forall r1 r2,
    (-PI/2 < r1 < PI/2 ->
     -PI/2 < r2 < PI/2 ->
     r1 <= r2 ->
     tan r1 <= tan r2)%R.
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
Lemma minus_eq :
  forall x y,
    --x = --y -|- x = y.
Proof. split; solve_linear. Qed.

Ltac tla_rewrite_0 :=
  repeat first
         [ rewrite mult_0_l_equiv |
           rewrite mult_0_r_equiv |
           rewrite plus_0_l_equiv |
           rewrite plus_0_r_equiv |
           rewrite minus_0_l_equiv |
           rewrite minus_0_r_equiv ].

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
Instance Reflexive_Rge : Reflexive Rge.
Proof.
  red. intro. apply Req_ge. reflexivity.
Qed.

Instance Reflexive_Rle : Reflexive Rle.
Proof.
  red. intro. apply Req_ge. reflexivity.
Qed.

Require Import Setoid Relation_Definitions Reals.
Open Scope R.

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

Close Scope R.