Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Tactics.
Require Import TLA.ArithFacts.
Require Import AbstractIndAccCtrl.
Require Import Rdefinitions.
Require Import RIneq.

Open Scope HP_scope.

Module Type UtilParams.

  Parameter amin : R.
  Parameter Hamin : (amin < 0)%R.

  Parameter ub : R.
  Parameter d : R.
  Parameter Hd : (d > 0)%R.

End UtilParams.

Module Util (Import Params : UtilParams).

  Definition amininv : R := (/amin)%R.

  Definition sdist (v:Term) : Term :=
    v^^2*(/2)%R*(--amininv).

  Lemma tdist_sdist_incr : forall v1 v2 a1 a2 d1 d2,
    |- v1 <= v2 --> a1 <= a2 --> d1 <= d2 -->
       0 <= a2 --> 0 <= d1 -->
       0 <= v1 + a1*d1 -->
       tdist v1 a1 d1 + sdist (v1 + a1*d1) <=
       tdist v2 a2 d2 + sdist (v2 + a2*d2).
  Proof.
    simpl; unfold eval_comp; simpl; intros.
    unfold amininv. pose proof Hamin.
    repeat match goal with
             | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
               => generalize dependent (eval_term t s1 s2)
           end; intros;
    repeat match goal with
             | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
               => generalize dependent (eval_term t s1 s2)
           end; intros.
    apply Rplus_le_algebra.
    apply Rmult_neg_le_algebra with (r2:=amin); auto.
    apply Rmult_pos_ge_algebra with (r2:=2%R); solve_linear.
    R_simplify; simpl; solve_linear.
    solve_nonlinear.
  Qed.

  Lemma sdist_incr : forall v1 v2,
    |- 0 <= v1 <= v2 -->
       sdist v1 <= sdist v2.
  Proof.
    pose proof Hamin.
    simpl; unfold eval_comp; simpl;
    unfold amininv; intros.
    apply Rmult_le_compat; solve_linear.
    - apply Rmult_0_le; solve_linear.
      apply pow_0_le.

    - rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat_l.
      solve_linear.
    - apply Rmult_le_compat; solve_linear.
      + apply Rmult_0_le; solve_linear.
      + apply Rle_sq_pos; solve_linear.
  Qed.

  Lemma sdist_tdist : forall v t,
    |- tdist v amin t <= sdist v.
  Proof.
    pose proof Hamin.
    simpl; unfold eval_comp; simpl;
    unfold amininv; intros.
    apply Rplus_le_algebra.
    apply Rmult_neg_le_algebra with (r2:=amin); auto.
    apply Rmult_pos_ge_algebra with (r2:=2%R); solve_linear.
    R_simplify; solve_linear.
    solve_nonlinear.
  Qed.

  Definition CtrlTerm (H V:Term) (a1 a2:Term) (t1 t2:R)
    : Term :=
    H + tdist V a1 t1 +
    tdist (V + a1*d) a2 t2 +
    sdist (V + a1*d + a2*t2).

  Definition CtrlTermUB (H V:Term) (a1 a2:Term) (t1 t2:R)
    : Formula :=
    CtrlTerm H V a1 a2 t1 t2 <= ub.

  Lemma CtrlTerm_incr : forall H V a1 a2 (t:R),
    |- t <= d --> a1 >= 0 --> a2 >= 0 -->
       0 <= V + a1*d + a2*t -->
       CtrlTerm H V a1 a2 d t <= CtrlTerm H V a1 a2 d d.
  Proof.
    pose proof Hd. pose proof Hamin.
    simpl; unfold eval_comp; simpl;
    unfold amininv. intros.
    repeat rewrite Rplus_assoc.
    apply Rplus_le_compat_l.
    R_simplify; solve_linear.
    apply Rmult_le_compat_neg_r; solve_linear.
    - apply inv_le_0; solve_linear; 
      apply Rmult_le_0.
    - unfold Rminus. repeat rewrite Rplus_assoc.
      apply Rplus_le_compat_l.
      R_simplify; simpl.
      solve_nonlinear.
  Qed.

End Util.

Lemma tdist_incr : forall v1 v2 a1 a2 d1 d2,
  |- v1 <= v2 --> a1 <= a2 --> d1 <= d2 -->
     0 <= a2 --> 0 <= d1 -->
     0 <= tdist v2 a2 d2 -->
     tdist v1 a1 d1 <= tdist v2 a2 d2.
Proof.
  simpl; unfold eval_comp; simpl; intros.
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
  destruct H3;
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
  |- 0 <= t --> v < 0 --> v + a*t < 0 -->
     tdist v a t <= 0.
Proof. solve_nonlinear. Qed.

Lemma tdist_neg : forall v1 v2 a1 a2 d1 d2,
  |- v1 <= v2 --> a1 <= a2 --> d1 <= d2 -->
     0 <= a2 --> 0 <= d1 -->
     tdist v2 a2 d2 <= 0 -->
     tdist v1 a1 d1 <= 0.
Proof.
  simpl; unfold eval_comp; simpl; intros.
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
  destruct H3;
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

Lemma tdist_pos_vel_pos : forall v a t,
  |- 0 <= a --> 0 < t -->
     0 <= tdist v a t -->
     0 <= v + a*t.
Proof. solve_nonlinear. Qed.

Lemma tdist_bound : forall v a t1 t2,
  |- 0 <= t1 <= t2 -->
     (tdist v a t1 <= tdist v a t2 \/
      tdist v a t1 <= tdist v 0 t2 \/
      tdist v a t1 <= 0).
Proof.
  simpl; unfold eval_comp; simpl; intros.
  destruct (Rle_dec 0 (eval_term a (hd tr) (hd (tl tr)))).
  - destruct (Rle_dec 0 (eval_term (tdist v a t2)
                                   (hd tr) (hd (tl tr))));
    simpl in *.
    + left; apply (tdist_incr v v a a t1 t2);
      solve_linear.
    + right; right;
      apply (tdist_neg v v a a t1 t2);
      solve_linear.
  - destruct (Rle_dec 0 (eval_term v (hd tr) (hd (tl tr)))).
    + right; left;
      apply Rplus_le_compat; solve_linear.
      R_simplify; simpl.
      rewrite Rmult_0_l.
      apply Rmult_pos_le_algebra with (r2:=2%R);
        solve_linear.
      R_simplify; simpl.
      rewrite Rmult_comm.
      apply Rmult_le_0.
      apply pow_0_le.
      solve_linear.
    + right; right;
      rewrite <- Rplus_0_r.
      apply Rplus_le_compat.
      * rewrite Rmult_comm.
        apply Rmult_le_0;
          solve_linear.
      * repeat rewrite Rmult_assoc.
        apply Rmult_le_0; solve_linear.
        rewrite Rmult_comm.
        apply Rmult_le_0;
          apply pow_0_le ||
                solve_linear.
Qed.

Lemma vbound : forall a t1 t2,
  |- 0 <= t1 <= t2 -->
     (a*t1 <= a*t2 \/ a*t1 <= 0).
Proof. solve_nonlinear. Qed.

Close Scope HP_scope.
