Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Import LibNotations.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import TLA.ArithFacts.
Require Import Modules.AbstractIndAccCtrl.
Require Import Modules.AbstractOneDimAccCtrl2.
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

Definition CtrlTerm (t1 t2:R) : Term :=
  "H" + tdist "V" amax t1 +
  tdist ("V" + amax*d) amax t2 +
  sdist ("V" + amax*d + amax*t2).

Definition SafeCtrl (t1 t2:R) : Formula :=
  CtrlTerm t1 t2 <= ub.

Definition Ctrl : Formula :=
     (SafeCtrl d d /\ SafeCtrl 0 d /\
      "A" <= amax /\ "a"! = "A")
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

Lemma CtrlTerm_incr1 : forall (t:R),
  |- t <= d -->
     0 <= "V" + amax*d + amax*t -->
     CtrlTerm d t <= CtrlTerm d d.
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
        { solve_linear; unfold InvParams.d in *;
          repeat match goal with
                   | [ H : _ |- _ ] =>
                     match type of H with
                       | @eq R _ _ => idtac
                       | _ => revert H
                     end
                 end;
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H
                 end; intros;
          try solve [ destruct (Rle_dec 0
                         (hd tr "v"*d+/2*amax*(d*(d*1))))%R;
                      [left; apply Rplus_le_compat_l;
                       apply (tdist_incr "v" "v" "A"
                                         amax x d);
                       solve_linear |
                       right; apply Rplus_le_l;
                       apply (tdist_neg "v" "v" "A" amax x d);
                       solve_linear ] |
                      destruct (Rle_dec 0
                         (hd tr "v"*d+/2*amax*(d*(d*1))))%R;
                      [left; apply Rplus_le_compat_l;
                       apply (tdist_incr "v" "v" amin
                                         amax x d);
                       solve_linear |
                       right; apply Rplus_le_l;
                       apply (tdist_neg "v" "v" amin
                                        amax x d);
                       solve_linear ] |
                      apply Rplus_le_compat_l;
                        apply Rmult_le_compat_3pos1;
                        solve_linear ].
          - clear H9.
            assert (0 <= hd tr "V" + amax*d + amax*x)%R.
            + eapply Rle_trans; eauto.
              eapply Rplus_rewrite_l; eauto.
              solve_linear.
            + pose proof (CtrlTerm_incr1 x tr).
              simpl in *; unfold eval_comp in *;
              simpl in *; intuition.
              eapply Rle_trans; eauto;
              eapply Rle_trans; eauto.
              rewrite Rplus_assoc.
              match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
              end.
              eapply Rle_trans; eauto.
              repeat rewrite Rplus_assoc;
                repeat apply Rplus_le_compat_l.
              repeat apply Rplus_le_compat.
              * apply Rmult_le_compat_r; auto.
              * { apply Rmult_le_compat_r.
                  - apply pow_0_le.
                  - apply Rmult_le_compat_l; solve_linear. }
              * unfold amininv.
                { repeat apply Rmult_le_compat_r;
                  solve_linear.
                  - rewrite Rminus_0_l.
                    solve_linear.
                  - apply Rle_sq_pos; solve_linear.
                    eapply Rplus_rewrite_l; eauto.
                    repeat rewrite Rplus_assoc;
                      repeat apply Rplus_le_compat_l.
                    solve_linear. }
          - clear H9.
            destruct (Rlt_dec (hd tr "v") R0);
            intuition.
            + eapply Rle_trans; eauto.
              rewrite <- Rplus_0_r.
              apply Rplus_le_compat_l.
              apply (tdist_vel_neg "v" "A" x);
                solve_linear.
            + assert (0 <= hd tr "V" + amax*d + amax*x)%R.
              * apply Rle_trans with (r2:=hd tr "v");
                solve_linear.
                eapply Rle_trans; eauto.
                apply Rplus_le_r.
                apply Rmult_0_le; solve_linear.
              * pose proof (CtrlTerm_incr1 x tr).
                simpl in *; unfold eval_comp in *;
                simpl in *; intuition.
                eapply Rle_trans; eauto.
                eapply Rle_trans; eauto.
                rewrite Rplus_assoc.
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
                repeat apply Rplus_le_compat;
                solve_linear.
                rewrite <- Rplus_0_r at 1.
                { apply Rplus_le_compat.
                  - apply Rmult_le_compat_r.
                    + apply pow_0_le.
                    + apply Rmult_le_compat_l;
                      solve_linear.
                  - repeat apply Rmult_0_le; solve_linear.
                    unfold amininv. rewrite Rminus_0_l.
                    solve_linear. }
          - clear H2.
            assert (0 <= hd tr "V" + amax*d + amax*x)%R.
            + eapply Rle_trans; eauto.
              eapply Rplus_rewrite_l; eauto.
              solve_linear.
            + pose proof (CtrlTerm_incr1 x tr).
              simpl in *; unfold eval_comp in *;
              simpl in *; intuition.
              eapply Rle_trans; eauto.
              rewrite Rplus_assoc.
              match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
              end.
              eapply Rle_trans; eauto.
              repeat rewrite Rplus_assoc;
                repeat apply Rplus_le_compat_l.
              repeat first [ rewrite Rmult_0_r |
                             rewrite Rmult_0_l |
                             rewrite Rplus_0_l ].
              pose proof (tdist_sdist_incr "v" ("V" + amax*d)
                     "A" amax x d tr) as Htsdist.
              simpl in *; unfold eval_comp in *;
              simpl in *. repeat rewrite Rplus_assoc in *.
              apply Htsdist; solve_linear.
          - destruct (Rlt_dec (hd tr "v") R0);
            intuition.
            + eapply Rle_trans; eauto.
              rewrite <- Rplus_0_r.
              apply Rplus_le_compat_l.
              apply (tdist_vel_neg "v" "A" x);
                solve_linear.
            + assert (0 <= hd tr "V" + amax*d + amax*x)%R.
              * apply Rle_trans with (r2:=hd tr "v");
                solve_linear.
                eapply Rle_trans; eauto.
                apply Rplus_le_r.
                apply Rmult_0_le; solve_linear.
              * pose proof (CtrlTerm_incr1 x tr).
                simpl in *; unfold eval_comp in *;
                simpl in *; intuition.
                eapply Rle_trans; eauto.
                rewrite Rplus_assoc.
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
                repeat first [ rewrite Rmult_0_r |
                               rewrite Rmult_0_l |
                               rewrite Rplus_0_l ].
                { repeat apply Rplus_le_compat;
                  solve_linear.
                  - apply Rmult_le_compat; solve_linear.
                  - rewrite <- Rplus_0_r at 1.
                    apply Rplus_le_compat.
                    + repeat rewrite Rmult_assoc.
                      apply Rmult_le_compat_l; solve_linear.
                      apply Rmult_le_compat_3pos1;
                        solve_linear.
                      * apply pow_0_le.
                      * apply pow_0_le.
                      * apply Rle_sq_pos; solve_linear.
                    + unfold amininv.
                      apply Rmult_0_le.
                      * apply Rmult_0_le; solve_linear.
                        apply pow_0_le.
                      * rewrite Rminus_0_l.
                        solve_linear. }
          - assert (0 <= hd tr "v")%R.
            + eapply Rle_trans; eauto.
              solve_nonlinear.
            + intuition.
              unfold amaxinv, amininv in *.
              eapply Rle_trans; eauto.
              R_simplify; solve_linear.
          - destruct (Rle_dec R0 (hd tr "v")).
            + intuition.
              unfold amaxinv, amininv in *.
              eapply Rle_trans; eauto.
              apply Rplus_le_compat_l.
              apply sdist_tdist
              with (v:="v") (t:=x) (tr:=tr).
            + assert (hd tr "v" < 0)%R by solve_linear.
              intuition.
              eapply Rle_trans; eauto.
              pose proof (tdist_vel_neg "v" amin x tr).
              simpl in *; unfold eval_comp in *;
              simpl in *; solve_linear.
          - assert (0 <= hd tr "v")%R.
            + eapply Rle_trans; eauto.
              solve_nonlinear.
            + intuition.
              unfold amaxinv, amininv in *.
              eapply Rle_trans; eauto.
              R_simplify; solve_linear.
          - destruct (Rle_dec R0 (hd tr "v")).
            + intuition.
              unfold amaxinv, amininv in *.
              eapply Rle_trans; eauto.
              apply Rplus_le_compat_l.
              apply sdist_tdist
              with (v:="v") (t:=x) (tr:=tr).
            + assert (hd tr "v" < 0)%R by solve_linear.
              intuition.
              eapply Rle_trans; eauto.
              pose proof (tdist_vel_neg "v" amin x tr).
              simpl in *; unfold eval_comp in *;
              simpl in *; solve_linear. }
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