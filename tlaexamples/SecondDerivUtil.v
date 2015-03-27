Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Import TLA.TLA.
Require Import TLA.ArithFacts.

Open Scope HP_scope.
Open Scope string_scope.

(* The distance traveled starting with velocity
   v, acceleration a, traveling for time t. *)
Definition tdist (v:Term) (a:Term) (t:Term) : Term :=
  v*t + (/2)%R*a*t^^2.

(* Some useful lemmas about tdist. *)

Lemma tdist_incr : forall v1 v2 a1 a2 d1 d2,
  |-- v1 <= v2 -->> a1 <= a2 -->> d1 <= d2 -->>
      0 <= a2 -->> 0 <= d1 -->>
      0 <= tdist v2 a2 d2 -->>
      tdist v1 a1 d1 <= tdist v2 a2 d2.
Proof.
  breakAbstraction; simpl; unfold eval_comp; simpl; intros.
  repeat match goal with
         | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
           => generalize dependent (eval_term t s1 s2)
         end; intros;
  repeat match goal with
         | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
           => generalize dependent (eval_term t s1 s2)
         end; intros.
  match goal with
    |- (?e <= _)%R
    => destruct (Rle_dec 0 e)
  end; solve_linear.
  destruct H4;
    repeat match goal with
           | [ H : @eq R _ _ |- _ ] =>
             rewrite <- H
           end; solve_linear.
  apply Rle_trans with (r2:=((r3 + /2*r2*r0)*r0)%R);
    solve_linear.
  apply Rle_trans with (r2:=((r1 + /2*r*r4)*r4)%R);
    solve_linear.
  apply Rmult_le_compat; solve_linear.
  - eapply Rmult_le_lt_0; eauto; solve_linear.
  - solve_nonlinear.
Qed.

Lemma tdist_vel_neg : forall v a t,
  |-- 0 <= t -->> v <= 0 -->> v + a*t <= 0 -->>
     tdist v a t <= 0.
Proof. solve_nonlinear. Qed.

Lemma tdist_neg : forall v1 v2 a1 a2 d1 d2,
  |-- v1 <= v2 -->> a1 <= a2 -->> d1 <= d2 -->>
     0 <= a2 -->> 0 <= d1 -->>
     tdist v2 a2 d2 <= 0 -->>
     tdist v1 a1 d1 <= 0.
Proof.
  breakAbstraction; simpl; unfold eval_comp; simpl; intros.
  repeat match goal with
           | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
             => generalize dependent (eval_term t s1 s2)
         end; intros;
  repeat match goal with
           | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
             => generalize dependent (eval_term t s1 s2)
           end; intros.
  match goal with
      |- (?e <= _)%R
      => destruct (Rle_dec 0 e)
  end; solve_linear.
  destruct H4;
    repeat match goal with
             | [ H : @eq R _ _ |- _ ] =>
               rewrite <- H
           end; solve_linear.
  apply Rle_trans with (r2:=((r3 + /2*r2*r0)*r0)%R);
    solve_linear.
  apply Rle_trans with (r2:=((r1 + /2*r*r4)*r4)%R);
    solve_linear.
  apply Rmult_le_compat; solve_linear.
  - eapply Rmult_le_lt_0; eauto; solve_linear.
  - solve_nonlinear.
Qed.

(* Generic parameters of the height shims. *)
Module Type SdistParams.

  (* Our breaking acceleration. *)
  Variable amin : R.
  Hypothesis amin_lt_0 : (amin < 0)%R.

End SdistParams.

(* Definitions for implementing the height shims
   in the source language. *)
Module SdistUtil (Import Params : SdistParams).

  (* The distance traveled before stopping when
     applying acceleration amin, starting with
     velocity v. *)
  Definition sdist (v:Term) : Term :=
    (v^^2)*(--(/2)%R)*(/amin)%R.

  (* Some useful lemmas about sdist. *)

  Lemma tdist_sdist_incr : forall v1 v2 a1 a2 d1 d2,
      |-- v1 <= v2 -->> a1 <= a2 -->> d1 <= d2 -->>
          0 <= a2 -->> 0 <= d1 -->>
          0 <= v1 + a1*d1 -->>
          tdist v1 a1 d1 + sdist (v1 + a1*d1) <=
          tdist v2 a2 d2 + sdist (v2 + a2*d2).
  Proof.
    pose proof amin_lt_0.
    breakAbstraction; unfold eval_comp; simpl; intros.
    repeat match goal with
             | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
               => generalize dependent (eval_term t s1 s2)
           end; intros;
    repeat match goal with
             | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
               => generalize dependent (eval_term t s1 s2)
           end; intros.
    apply Rplus_le_algebra.
    apply Rmult_neg_le_algebra with (r2:=amin);
      auto.
    rewrite Rminus_0_l.
    apply Rmult_pos_ge_algebra with (r2:=(2)%R);
      solve_linear.
    R_simplify; simpl; solve_linear.
    solve_nonlinear.
  Qed.

  Lemma sdist_tdist : forall v t,
    |-- tdist v amin t <= sdist v.
  Proof.
    pose proof amin_lt_0.
    breakAbstraction; simpl; unfold eval_comp; simpl;
    intros.
    apply Rplus_le_algebra.
    apply Rmult_neg_le_algebra with (r2:=amin);
      auto.
    apply Rmult_neg_ge_algebra with (r2:=(-4)%R);
      solve_linear.
    R_simplify; solve_linear.
    solve_nonlinear.
  Qed.

  Lemma sdist_tdist_tdist : forall v t,
    |-- tdist v amin t + sdist (v + amin*t) <= sdist v.
  Proof.
    pose proof amin_lt_0.
    breakAbstraction; simpl; unfold eval_comp; simpl;
    intros.
    apply Rplus_le_algebra.
    apply Rmult_neg_le_algebra with (r2:=amin);
      auto.
    apply Rmult_neg_ge_algebra with (r2:=(-4)%R);
      solve_linear.
    R_simplify; solve_linear.
  Qed.

  Lemma sdist_incr : forall v1 v2,
    |-- 0 <= v1 <= v2 -->>
        sdist v1 <= sdist v2.
  Proof.
    pose proof amin_lt_0.
    breakAbstraction; simpl; unfold eval_comp; simpl;
    intros. do 2 rewrite (Rmult_assoc _ (0 - / 2) (/ amin))%R.
    apply Rmult_le_compat; solve_linear.
    - apply Rmult_0_le; solve_linear.
    - assert (/ amin < 0)%R by solve_linear.
      solve_linear.
    - apply Rmult_le_compat; solve_linear.
  Qed.

End SdistUtil.
