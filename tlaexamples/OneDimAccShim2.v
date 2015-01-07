Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Import LibNotations.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import TLA.ArithFacts.
Require Import TLA.Substitution.
Require Import Modules.AbstractIndAccCtrl.
Require Import Modules.AbstractOneDimAccCtrl3.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

Module Params <: CtrlParameters.

  Variable ub : R.
  Variable d : R.
  Hypothesis Hd : (d > 0)%R.

  Variable amin : R.
  Hypothesis Hamin : (amin < 0)%R.

  Variable amax : R.
  Hypothesis Hamax : (amax > 0)%R.

End Params.

Import Params.

Module AbstractCtrl := AbstractAccDimCtrl2(Params).

Import AbstractCtrl.

Definition Read : Formula :=
  "T"! = "t" /\ "H"! = "h" /\ "V"! = "v".

Definition Evolve : Formula :=
  Continuous (["h"' ::= "v",
               "v"' ::= "a",
               "a"' ::= 0,
               "t"' ::= 1,
               "H"' ::= 0,
               "T"' ::= 0,
               "V"' ::= 0]).

Definition CtrlTerm (t1 t2:R) (a1 a2:Term) : Term :=
  "H" + tdist "V" a1 t1 +
  tdist ("V" + a1*d) a2 t2 +
  sdist ("V" + a1*d + a2*t2).

Definition SafeCtrl : Formula :=
     ("a" >= 0 /\ tdist "V" "a" d >= 0 /\ "A" >= 0 /\
      CtrlTerm d d "a" "A" <= ub)
  \/ ("a" >= 0 /\ tdist "V" "a" d < 0 /\ "A" >= 0 /\
      CtrlTerm 0 d "a" "A" <= ub)
  \/ ("a" < 0 /\ tdist "V" 0 d >= 0 /\ "A" >= 0 /\
      CtrlTerm d d 0 "A" <= ub)
  \/ ("a" < 0 /\ tdist "V" 0 d < 0 /\ "A" >= 0 /\
      CtrlTerm 0 d 0 "A" <= ub)
  \/ ("a" >= 0 /\ tdist "V" "a" d >= 0 /\ "A" < 0 /\
      CtrlTerm d d "a" 0 <= ub)
  \/ ("a" >= 0 /\ tdist "V" "a" d < 0 /\ "A" < 0 /\
      CtrlTerm 0 d "a" 0 <= ub)
  \/ ("a" < 0 /\ tdist "V" 0 d >= 0 /\ "A" < 0 /\
      CtrlTerm d d 0 0 <= ub)
  \/ ("a" < 0 /\ tdist "V" 0 d < 0 /\ "A" < 0 /\
      CtrlTerm 0 d 0 0 <= ub).

Definition Ctrl : Formula :=
     (SafeCtrl /\ "A" <= amax /\ "a"! = "A")
  \/ ("a"! = amin).

Lemma Rmult_minus_distr_r : forall r1 r2 r3,
  (eq ((r1 - r2)*r3) (r1*r3 - r2*r3))%R.
Proof. solve_linear. Qed.

Lemma Rmult_le_compat_neg_r : forall r r1 r2 : R,
 (r <= 0)%R -> (r1 <= r2)%R -> (r2*r <= r1*r)%R.
Proof. solve_nonlinear. Qed.

Lemma inv_le_0 : forall r,
  (r < 0 -> /r <= 0)%R.
Proof. solve_nonlinear. Qed.

Lemma inv_0_le : forall r,
  (0 < r -> 0 <= /r)%R.
Proof. solve_nonlinear. Qed.

Lemma CtrlTerm_incr1 : forall (t:R) a1 a2,
  |- t <= d --> a1 >= 0 --> a2 >= 0 -->
     0 <= "V" + a1*d + a2*t -->
     CtrlTerm d t a1 a2 <= CtrlTerm d d a1 a2.
Proof.
  pose proof Hd. pose proof Hamin.
  pose proof Hamax.
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

Definition Next : Formula :=
     (Evolve /\ "t"! <= "T" + d)
  \/ (Ctrl /\ Read /\ Unchanged (["h", "v", "t"])).

Definition Init : Formula := AbstractCtrl.Ind_Inv.

Definition Safe : Formula :=
  "h" <= ub.

Lemma Rmult_le_lt_0 : forall r1 r2,
  (0 < r1 -> 0 <= r1*r2 -> 0 <= r2)%R.
Proof. solve_nonlinear. Qed.

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

Lemma Rplus_le_algebra : forall r1 r2,
  (r1 - r2 <= 0 -> r1 <= r2)%R.
Proof. solve_linear. Qed.

Lemma Rmult_neg_le_algebra : forall r1 r2,
  (r2 < 0 -> r1*r2 >= 0 -> r1 <= 0)%R.
Proof. solve_nonlinear. Qed.

Lemma Rmult_pos_ge_algebra : forall r1 r2,
  (r2 > 0 -> r1*r2 >= 0 -> r1 >= 0)%R.
Proof. solve_nonlinear. Qed.

Lemma Rmult_pos_le_algebra : forall r1 r2,
  (r2 > 0 -> r1*r2 <= 0 -> r1 <= 0)%R.
Proof. solve_nonlinear. Qed.

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

Lemma Rmult_0_lt : forall r1 r2,
  (0 < r1 -> 0 < r2 ->
   0 < r1*r2)%R.
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

Lemma refinement :
  |- (Init /\ []Next)
       --> (AbstractCtrl.Init /\ []AbstractCtrl.Next).
Proof.
  pose proof Hd. pose proof Hamax. pose proof Hamin.
  apply and_right.
  - apply and_left1. apply imp_id.
  - apply and_left2. apply always_imp.
    repeat apply or_left.
    + unfold Evolve. apply or_right1.
      repeat apply and_right.
      * apply and_left1. apply imp_id.
      * apply and_left2. apply imp_id.
    + apply or_right2.
      apply and_right.
      * apply and_left1.
        { unfold AbstractCtrl.Ctrl.
          repeat first [ apply imp_right |
                         apply forall_right; intro |
                         repeat apply and_right ];
          match goal with
            |- (|- ?G) => simpl G
          end.
          - solve_linear.
          - solve_linear; rewrite_next_st.
            + eapply Rle_trans; eauto.
              rewrite_real_zeros.
              repeat rewrite Rplus_assoc.
              match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
              end.
              eapply Rle_trans; eauto.
              rewrite_real_zeros.
              repeat rewrite Rplus_assoc;
                repeat apply Rplus_le_compat_l.
              pose proof (tdist_sdist_incr "v" ("V" + "a"*d)
                                           "A" "A" x d tr)
                as Htdist.
              simpl in *; unfold eval_comp in *; simpl in *;
              repeat rewrite Rplus_assoc in *.
              apply Htdist; solve_linear.
            + eapply Rle_trans; eauto.
              rewrite_real_zeros.
              repeat rewrite Rplus_assoc.
              match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
              end.
              eapply Rle_trans; eauto.
              repeat rewrite Rplus_assoc;
                repeat apply Rplus_le_compat_l.
              pose proof (tdist_sdist_incr "v" ("V" + "a"*d)
                                           "A" "A" x d tr)
                   as Htdist.
              simpl in *; unfold eval_comp in *; simpl in *;
              repeat rewrite Rplus_assoc in *.
              apply Htdist; solve_linear.
            + eapply Rle_trans; eauto.
              rewrite_real_zeros.
              repeat rewrite Rplus_assoc.
              match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
              end.
              eapply Rle_trans; eauto.
              rewrite_real_zeros.
              repeat rewrite Rplus_assoc;
                repeat apply Rplus_le_compat_l.
              pose proof (tdist_sdist_incr "v" "V"
                                           "A" "A" x d tr)
                as Htdist.
              simpl in *; unfold eval_comp in *; simpl in *;
              repeat rewrite Rplus_assoc in *.
              apply Htdist; solve_linear.
            + eapply Rle_trans; eauto.
              rewrite_real_zeros.
              repeat rewrite Rplus_assoc.
              match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
              end.
              eapply Rle_trans; eauto.
              rewrite_real_zeros.
              repeat rewrite Rplus_assoc;
                repeat apply Rplus_le_compat_l.
              pose proof (tdist_sdist_incr "v" "V"
                                           "A" "A" x d tr)
                as Htdist.
              simpl in *; unfold eval_comp in *; simpl in *;
              repeat rewrite Rplus_assoc in *.
              apply Htdist; solve_linear.
            + eapply Rle_trans; eauto.
              rewrite_real_zeros.
              repeat rewrite Rplus_assoc.
              match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
              end.
              eapply Rle_trans; eauto.
              repeat rewrite Rplus_assoc;
                repeat apply Rplus_le_compat_l.
              pose proof (tdist_sdist_incr "v" ("V" + "a"*d)
                                           "A" 0 x d tr)
                as Htdist.
              simpl in *; unfold eval_comp in *; simpl in *;
              repeat rewrite Rplus_assoc in *.
              revert Htdist. rewrite_real_zeros. intros.
              apply Htdist; solve_linear.
            + eapply Rle_trans; eauto.
              rewrite_real_zeros.
              repeat rewrite Rplus_assoc.
              match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
              end.
              eapply Rle_trans; eauto.
              repeat rewrite Rplus_assoc;
                repeat apply Rplus_le_compat_l.
              pose proof (tdist_sdist_incr "v" ("V" + "a"*d)
                                           "A" 0 x d tr)
                as Htdist.
              simpl in *; unfold eval_comp in *; simpl in *;
              repeat rewrite Rplus_assoc in *.
              revert Htdist. rewrite_real_zeros. intros.
              apply Htdist; solve_linear.
            + eapply Rle_trans; eauto.
              rewrite_real_zeros.
              repeat rewrite Rplus_assoc.
              match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
              end.
              eapply Rle_trans; eauto.
              rewrite_real_zeros.
              repeat rewrite Rplus_assoc;
                repeat apply Rplus_le_compat_l.
              pose proof (tdist_sdist_incr "v" "V"
                                           "A" 0 x d tr)
                as Htdist.
              simpl in *; unfold eval_comp in *; simpl in *;
              repeat rewrite Rplus_assoc in *.
              revert Htdist. rewrite_real_zeros. intros.
              apply Htdist; solve_linear.
            + eapply Rle_trans; eauto.
              rewrite_real_zeros.
              repeat rewrite Rplus_assoc.
              match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
              end.
              eapply Rle_trans; eauto.
              rewrite_real_zeros.
              repeat rewrite Rplus_assoc;
                repeat apply Rplus_le_compat_l.
              pose proof (tdist_sdist_incr "v" "V"
                                           "A" 0 x d tr)
                as Htdist.
              simpl in *; unfold eval_comp in *; simpl in *;
              repeat rewrite Rplus_assoc in *.
              revert Htdist. rewrite_real_zeros. intros.
              apply Htdist; solve_linear.
            + assert (0 <= hd tr "v")%R.
              * match goal with
                  | [ H : _ |- _ ]
                      => eapply Rle_trans; [ apply H | ];
                         apply Rplus_le_algebra; R_simplify;
                         rewrite Rmult_comm;
                         apply Rmult_le_0; solve_linear
                end.
              * intuition. unfold amininv in *.
                eapply Rle_trans; eauto.
                R_simplify; solve_linear.
          - solve_linear; rewrite_next_st.
            + assert (hd tr "v" < 0)%R.
              * { apply Rle_lt_trans
                  with (r2:=(hd tr "v"+hd tr "A"*x)%R); auto.
                  assert (0 <= hd tr "A"*x)%R.
                  - apply Rmult_0_le; solve_linear.
                  - solve_linear. }
              * intuition. eapply Rle_trans; eauto.
                apply Rplus_le_l.
                apply (tdist_vel_neg "v" "A" x);
                  solve_linear.
            + assert (hd tr "v" < 0)%R.
              * { apply Rle_lt_trans
                  with (r2:=(hd tr "v"+hd tr "A"*x)%R); auto.
                  assert (0 <= hd tr "A"*x)%R.
                  - apply Rmult_0_le; solve_linear.
                  - solve_linear. }
              * intuition. eapply Rle_trans; eauto.
                apply Rplus_le_l.
                apply (tdist_vel_neg "v" "A" x);
                  solve_linear.
            + assert (hd tr "v" < 0)%R.
              * { apply Rle_lt_trans
                  with (r2:=(hd tr "v"+hd tr "A"*x)%R); auto.
                  assert (0 <= hd tr "A"*x)%R.
                  - apply Rmult_0_le; solve_linear.
                  - solve_linear. }
              * intuition. eapply Rle_trans; eauto.
                apply Rplus_le_l.
                apply (tdist_vel_neg "v" "A" x);
                  solve_linear.
            + assert (hd tr "v" < 0)%R.
              * { apply Rle_lt_trans
                  with (r2:=(hd tr "v"+hd tr "A"*x)%R); auto.
                  assert (0 <= hd tr "A"*x)%R.
                  - apply Rmult_0_le; solve_linear.
                  - solve_linear. }
              * intuition. eapply Rle_trans; eauto.
                apply Rplus_le_l.
                apply (tdist_vel_neg "v" "A" x);
                  solve_linear.
            + eapply Rle_trans; eauto.
              repeat rewrite Rplus_assoc.
              match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
              end.
              eapply Rle_trans; eauto.
              repeat rewrite Rplus_assoc;
                repeat apply Rplus_le_compat_l.
              pose proof (tdist_incr "v" ("V"+"a"*d)
                                     "A" 0 x d tr)
                   as Htdist.
              simpl in *; unfold eval_comp in *; simpl in *;
              repeat rewrite Rplus_assoc in *.
              repeat match type of Htdist with
                       | ?Hyp -> _ => let H := fresh "H" in
                                      assert Hyp as H
                                        by solve_linear;
                                        specialize (Htdist H);
                                        clear H
                     end.
              assert (0 <= hd tr "V" + hd tr "a"*d)%R.
              * apply (tdist_pos_vel_pos "V" "a" d);
                solve_linear.
              * { assert (0 <= (hd tr "V"+hd tr "a"*d)*d +
                               / 2 * 0 * (d * (d * 1)))%R.
                  - rewrite_real_zeros.
                    apply Rmult_0_le; solve_linear.
                  - intuition.
                    assert (0 <=
                            (hd tr "V"+(hd tr "a"*d+0*d))*
                            ((hd tr "V"+(hd tr "a"*d+0*d))*1)
                            * / 2 * (0 - amininv))%R.
                    + apply Rmult_0_le.
                      * apply Rmult_0_le; solve_linear.
                        apply pow_0_le.
                      * unfold amininv. rewrite Rminus_0_l.
                        solve_linear.
                    + solve_linear. }
            + destruct (Rlt_dec (hd tr "v") R0).
              * intuition. eapply Rle_trans; eauto.
                apply Rplus_le_l.
                apply (tdist_vel_neg "v" "A" x);
                  solve_linear.
              * eapply Rle_trans; eauto.
                repeat rewrite Rplus_assoc.
                match goal with
                  | [ _ : Rle ?x ?e1 |-
                      Rle (Rplus ?x ?e2) ?e3 ]
                    => assert (Rle (Rplus x e2) (Rplus e1 e2))
                      by (try apply Rplus_le_compat;
                          try apply Rle_refl; auto)
                end.
                eapply Rle_trans; eauto.
                repeat rewrite Rplus_assoc;
                  repeat apply Rplus_le_compat_l.
                pose proof (tdist_incr "v" ("V"+"a"*d)
                                     "A" 0 x d tr)
                   as Htdist.
                simpl in *; unfold eval_comp in *; simpl in *;
                repeat rewrite Rplus_assoc in *.
                repeat match type of Htdist with
                         | ?Hyp -> _ => let H := fresh "H" in
                                        assert Hyp as H
                                          by solve_linear;
                                        specialize (Htdist H);
                                        clear H
                       end.
                { assert (0 <= (hd tr "V"+hd tr "a"*d)*d +
                               / 2 * 0 * (d * (d * 1)))%R.
                  - rewrite_real_zeros.
                    apply Rmult_0_le; solve_linear.
                  - intuition.
                    assert (0 <=
                            (hd tr "V"+(hd tr "a"*d+0*d))*
                            ((hd tr "V"+(hd tr "a"*d+0*d))*1)
                            * / 2 * (0 - amininv))%R.
                    + apply Rmult_0_le.
                      * apply Rmult_0_le; solve_linear.
                        apply pow_0_le.
                      * unfold amininv. rewrite Rminus_0_l.
                        solve_linear.
                    + solve_linear. }
            + eapply Rle_trans; eauto.
              repeat rewrite Rplus_assoc.
              match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
              end.
              eapply Rle_trans; eauto.
              repeat rewrite Rplus_assoc;
                repeat apply Rplus_le_compat_l.
              pose proof (tdist_incr "v" "V"
                                     "A" 0 x d tr)
                   as Htdist.
              simpl in *; unfold eval_comp in *; simpl in *;
              repeat rewrite Rplus_assoc in *.
              repeat match type of Htdist with
                       | ?Hyp -> _ => let H := fresh "H" in
                                      assert Hyp as H
                                        by solve_linear;
                                        specialize (Htdist H);
                                        clear H
                     end.
              rewrite_real_zeros.
              assert (0<=hd tr "V"*(hd tr "V"*1)*
                         /2*(0-amininv))%R.
              * { apply Rmult_0_le.
                  - apply Rmult_0_le; solve_linear.
                    apply pow_0_le.
                  - unfold amininv. rewrite Rminus_0_l.
                    solve_linear. }
              * solve_linear.
            + assert (hd tr "v" < 0)%R.
              * apply Rle_lt_trans
                with (r2:=(hd tr "V")%R); solve_linear.
                revert H15 H2 H7.
                repeat match goal with
                         | [ H : _ |- _ ]
                           => clear H
                       end; rewrite_real_zeros; intros.
                unfold InvParams.d in *.
                solve_nonlinear.
              * intuition. eapply Rle_trans; eauto.
                apply Rplus_le_l.
                apply (tdist_vel_neg "v" "A" x);
                  solve_linear.
            + destruct (Rlt_dec (hd tr "v") R0).
              * intuition. eapply Rle_trans; eauto.
                apply Rplus_le_l.
                apply (tdist_vel_neg "v" amin x);
                  solve_linear.
              * assert (0 <= hd tr "v")%R by solve_linear.
                intuition. eapply Rle_trans; eauto.
                unfold amininv. apply Rplus_le_algebra.
                R_simplify; simpl; solve_linear.
                { apply Rmult_le_0.
                  - solve_nonlinear.
                  - apply inv_le_0. solve_linear. }
          - repeat apply and_assoc_left.
            apply and_left2. apply and_left2.
            apply imp_trans
            with (F2:=tdist "v" "a"! x <= tdist "v" "a"! d).
            + simpl; intros;
              apply (tdist_incr "v" "v" "a"! "a"! x d);
              solve_linear.
            + solve_linear.
          - repeat apply and_assoc_left.
            apply and_left2. apply and_left2.
            apply imp_trans
            with (F2:=tdist "v" "a"! x <= tdist "v" 0 d).
            + simpl; intros;
              apply (tdist_incr "v" "v" "a"! 0 x d);
              solve_linear.
            + solve_linear.
          - repeat apply and_assoc_left.
            apply and_left2. apply and_left2.
            simpl; unfold eval_comp; simpl; intros.
            apply Rplus_le_l. intuition.
            + apply (tdist_neg "v" "v" "a"! "a"! x d);
              solve_linear.
            + apply (tdist_neg "v" "v" "a"! 0 x d);
              solve_linear.
          - repeat apply and_assoc_left.
            apply and_left2. apply and_left2.
            solve_linear.
          - repeat apply and_assoc_left.
            apply and_left2. apply and_left2.
            solve_linear. apply Rplus_le_l.
            solve_nonlinear. }
      * solve_linear.
Qed.

Lemma safety :
  |- (Init /\ []Next) --> []Safe.
Proof.
  apply imp_trans
  with (F2:=AbstractCtrl.Init /\ []AbstractCtrl.Next).
  - apply refinement.
  - apply imp_trans
    with (F2:=[]InvParams.Inv).
    + apply AbstractCtrl.safety.
    + apply always_imp. apply AbstractCtrl.inv_safe.
Qed.