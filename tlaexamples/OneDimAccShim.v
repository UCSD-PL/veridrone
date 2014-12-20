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
     (SafeCtrl d d /\ "A" <= amax /\ "a"! = "A")
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

(*
Lemma CtrlTerm_incr2 : forall (t1 t2:R),
  |- t1 <= d --> t2 <= d -->
     0 <= "V" + amax*t1 + amax*t2 -->
     CtrlTerm t1 t2 <= CtrlTerm d d.
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
*)

(* Attempt at a more sophisticated safety check. *)
(*
(*Definition safe_travel (h v t:Term) :=
  ("A" >= 0 /\ h + tdist v "A" t <= ub - sdist v2.*)

Definition Safe (V a:Term) : Formula :=
  (* Always moves up *)
  ((V >= 0 /\ a >= 0)
   --> "h" - "H" <= tdist V a d) /\
  (* Always moves down *)
    ((V < 0 /\ a < 0)
     --> "h" - "H" <= 0) /\
    (* Moves up for next d time *)
    ((V >= 0 /\ a < 0 /\ --a*d < V)
     --> "h" - "H" <= tdist V a d) /\
    (* Peaks in middle *)
    ((V >= 0 /\ a < 0 /\ --a*d >= V)
     (* We don't have division, so we need a
        on the left. *)
     --> a*("h" - "H") <= --V^^2*(/2)%R) /\
    (* Moves down then turns around and ends
       heigher than at the beginning *)
    ((V < 0 /\ a >= 0 /\ tdist V a d >= 0)
     --> "h" - "H" <= tdist V a d) /\
    (* Moves down, maybe turns around, but ends
       lower than at the beginning *)
    ((V < 0 /\ a >= 0 /\ tdist V a d < 0)
     --> "h" - "H" <= 0)



     ("V" >= 0 /\ "a" >= 0 /\ "A" >= 0 /\
      "H" + tdist "V" "a" d + tdist ("V" + "a"*d) "A" d
       <= ub - sdist ("V" + "a"*d + "A"*d))
  \/ ("V" >= 0 /\ "a" >= 0 /\ "A" < 0 /\
      --"A"*d < "V" + "a"*d /\
      "H" + tdist "V" "a" d + tdist ("V" + "a"*d) "A" d
       <= ub - sdist ("V" + "a"*d))
  \/ ("V" >= 0 /\ "a" >= 0 /\ "A" < 0 /\
      --"A"*d >= "V" + "a"*d /\
      "H" + tdist "V" "a" d + tdist ("V" + "a"*d) "A" d
       <= ub - sdist ("V" + "a"*d))

    (* Always moves down *)
    (("V" < 0 /\ "a" < 0)
     --> "h" - "H" <= 0) /\
    (* Moves up for next d time *)
    (("V" >= 0 /\ "a" < 0 /\ --"a"*d < "V")
     --> "h" - "H" <= tdist "V" "a" d) /\
    (* Peaks in middle *)
    (("V" >= 0 /\ "a" < 0 /\ --"a"*d >= "V")
     (* We don't have division, so we need "a"
        on the left. *)
     --> "a"*("h" - "H") <= --"V"^^2*(/2)%R) /\
    (* Moves down then turns around and ends
       heigher than at the beginning *)
    (("V" < 0 /\ "a" >= 0 /\ tdist "V" "a" d >= 0)
     --> "h" - "H" <= tdist "V" "a" d) /\
    (* Moves down, maybe turns around, but ends
       lower than at the beginning *)
    (("V" < 0 /\ "a" >= 0 /\ tdist "V" "a" d < 0)
     --> "h" - "H" <= 0)*)

Definition Next : Formula :=
     (Evolve /\ "t"! <= "T" + d)
  \/ (Ctrl /\ Read /\ Unchanged (["h", "v", "t"])).

Definition Init : Formula := AbstractCtrl.Ind_Inv.

Definition Safe : Formula :=
  "h" <= ub.

Lemma Rmult_le_lt_0 : forall r1 r2,
  (0 < r1 -> 0 <= r1*r2 -> 0 <= r2)%R.
Proof. solve_nonlinear. Qed.

(*
Lemma tdist_incr1 : forall v1 v2 a1 a2 d1 d2,
  |- v1 <= v2 --> a1 <= a2 --> d1 <= d2 -->
     0 <= a2 --> 0 <= d1 -->
     0 < tdist v1 a1 d1 -->
     tdist v1 a1 d1 <= tdist v2 a2 d2.
Admitted.
*)

Lemma tdist_incr2 : forall v1 v2 a1 a2 d1 d2,
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

Lemma Rmult_le_compat_3pos:
  forall r1 r2 r3 r4 : R,
  (0 <= r2)%R -> (0 <= r3)%R ->
  (0 <= r4)%R -> (r1 <= r2)%R ->
  (r3 <= r4)%R -> (r1 * r3 <= r2 * r4)%R.
Proof. solve_nonlinear. Qed.

Lemma Rplus_rewrite_l : forall r1 r2 r3 r4,
  (r1 <= r2 -> r2 + r3 <= r4 -> r1 + r3 <= r4)%R.
Proof. solve_linear. Qed.

Lemma Rplus_le_r : forall r1 r2,
  (0 <= r2 -> r1 <= r1 + r2)%R.
Proof. solve_linear. Qed.

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
                 end; intros.
          - assert (0 <= hd tr "V" + amax*d + amax*x)%R.
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
          - destruct (Rle_dec 0
                       (hd tr "v" * d +
                        / 2 * amax * (d * (d * 1))))%R.
            + left. apply Rplus_le_compat_l.
              apply (tdist_incr2 "v" "v" "A" amax x d);
                solve_linear.
            + right.
              pose proof (tdist_neg "v" "v" "A" amax x d tr).
              simpl in *; unfold eval_comp in *;
              simpl in *; solve_linear.
          - apply Rplus_le_compat_l.
            apply Rmult_le_compat_3pos;
              solve_linear.
          - assert (0 <= hd tr "V" + amax*d + amax*x)%R.
            * eapply Rle_trans; eauto.
              eapply Rplus_rewrite_l; eauto.
              solve_linear.
            * Declare ML Module "z3Tactic".
repeat match goal with
            | H : @eq R _ _ |- _ => revert H
            | H : @Rle _ _ |- _ => revert H
            | H : @Rge _ _ |- _ => revert H
            | H : @Rlt _ _ |- _ => revert H
            | H :@ Rgt _ _ |- _ => revert H
            | H : @Rge _ _ |- _ => revert H
           end.
z3Tactic.


pose proof (CtrlTerm_incr2 0 x tr).
              simpl in *; unfold eval_comp in *;
              simpl in *; intuition.
              eapply Rle_trans; eauto.
              eapply Rle_trans; eauto.
              repeat rewrite Rplus_assoc.
              apply Rplus_le_compat; auto.
              solve_nonlinear.
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
              Declare ML Module "z3Tactic".
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H :@ Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              z3Tactic.

eapply Rle_trans; eauto.
            apply Rplus_le_compat.
            + repeat rewrite Rplus_assoc.
              apply Rplus_le_compat; auto.
              

                       | [ H : _ |- _ ]
                         => match type of H with
                              | Rlt _ _ => revert H
                              | _ => clear H
                            end
                     end; intros.
              clear H1.
              solve_nonlinear.
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
            + 

 destruct (Rlt_dec 0 (hd tr "V" * d +
                                 / 2 * amax * (d * (d * 1))));
            intuition.
            + clear H13. eapply Rle_trans; eauto.
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
              repeat rewrite <- Rplus_assoc.
              apply Rplus_le_compat.
              * apply tdist_incr2
                with (v1:="v") (a1:="A") (d1:=x)
                     (v2:="V" + amax*d) (a2:=amax) (d2:=d);
                solve_linear.
                apply Rle_trans
                with (r2:=(hd tr "V" * d +
                           /2 * amax * (d * (d * 1)))%R);
                  solve_linear.
                apply tdist_incr1
                with (v1:="V") (a1:=amax) (d1:=d)
                     (v2:="V"+amax*d) (a2:=amax) (d2:=d);
                  solve_linear.
                rewrite <- Rplus_0_r with (r:=hd tr "V") at 1.
                apply Rplus_le_compat; solve_linear.
                apply Rmult_0_le; solve_linear.
              * apply sdist_incr
                with (v1:="v" + "A"*x) (v2:="V" + amax*d +
                                            amax*d);
                solve_linear.
                match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
                end.
                eapply Rle_trans; eauto.
                repeat rewrite Rplus_assoc;
                  repeat apply Rplus_le_compat_l.
                apply Rmult_le_compat_3pos; solve_linear.
            + clear H10. eapply Rle_trans; eauto.
              rewrite Rplus_assoc.
              match goal with
                | [ _ : _ -> Rle ?x ?e1 |-
                    Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        solve_linear)
              end.
              eapply Rle_trans; eauto.
              repeat rewrite Rplus_assoc;
                repeat apply Rplus_le_compat_l.
              repeat rewrite <- Rplus_assoc.
              apply Rplus_le_compat.
              * apply tdist_incr2
                with (v1:="v") (a1:="A") (d1:=x)
                     (v2:="V" + amax*d) (a2:=amax) (d2:=d);
                solve_linear.
                apply Rle_trans
                with (r2:=(hd tr "V" * d +
                           /2 * amax * (d * (d * 1)))%R);
                  solve_linear.
                apply tdist_incr1
                with (v1:="V") (a1:=amax) (d1:=d)
                     (v2:="V"+amax*d) (a2:=amax) (d2:=d);
                  solve_linear.
                rewrite <- Rplus_0_r with (r:=hd tr "V") at 1.
                apply Rplus_le_compat; solve_linear.
                apply Rmult_0_le; solve_linear.
              * apply sdist_incr
                with (v1:="v" + "A"*x) (v2:="V" + amax*d +
                                            amax*d);
                solve_linear.
                match goal with
                | [ _ : Rle ?x ?e1 |- Rle (Rplus ?x ?e2) ?e3 ]
                  => assert (Rle (Rplus x e2) (Rplus e1 e2))
                    by (try apply Rplus_le_compat;
                        try apply Rle_refl; auto)
                end.
                eapply Rle_trans; eauto.
                repeat rewrite Rplus_assoc;
                  repeat apply Rplus_le_compat_l.
                apply Rmult_le_compat_3pos; solve_linear.

solve_nonlinear. Qed.
              apply Rplus_le_compat.
Lemma Rmult_le_compat_3pos:
  forall r1 r2 r3 r4 : R,
  (0 <= r2)%R -> (0 <= r3)%R ->
  (0 <= r4)%R -> (r1 <= r2)%R ->
  (r3 <= r4)%R -> (r1 * r3 <= r2 * r4)%R.
Proof. solve_nonlinear. Qed.
apply Rmult_le_compat_3pos; auto.
solve_nonlinear.


SearchAbout Rmult.
            apply Rmult_le_compat; solve_linear.

            repeat rewrite Rmult_plus_distr_r.

rewrite H8.
            (*          clear H4 H6 H2 H12 H5.*)
            (*Time solve_nonlinear.*)
            admit.
          - eapply Rle_trans; eauto.
            clear H5 H4 H6 H2 H12 H11.
            Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.

Ltac thing t :=
match goal with
| [ _ : (t - ?e1 <= ?e2) |- 
pose proof (derive_increasing_interv_var 
(* 8, 12 solved nonlinearly *)


apply and_right; repeat apply or_left;
          try apply imp_right.
          try solve [unfold amax; solve_linear].
          - apply imp_strengthen with (F2:="h" < ubH);
            [ solve_linear | ].
            apply imp_strengthen with (F2:="v" < vt + ubV);
              [ solve_linear | ].
            solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.inv2, ub, ubV, ubv, ubv_r, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H8 in H10. clear H8 H0 H1 H5 H7 H11 H6.
              unfold amax, ubv_r in *. repeat rewrite Rplus_assoc.
              match goal with
                | [ H : Rlt ?e1 ?e2 |- Rle (Rplus ?e1 ?e3) _ ]
                  => apply Rle_trans with (r2:=Rplus e2 e3);
                    [ solve_linear | clear H ]
              end.
              Time solve_nonlinear.
            + clear H10 H11. unfold ubv_r in *. Time solve_nonlinear.
            + clear H11. unfold ubv_r in *. Time solve_nonlinear.
          - apply imp_strengthen with (F2:="h" < ubH);
            [ solve_linear | ].
            solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.inv2, ub, ubV, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H7 in H9.
              assert (0 <= hd tr "v")%R by solve_linear.
              intuition. eapply Rle_trans; eauto.
              R_simplify; solve_linear. unfold amax. simpl.
              repeat rewrite Rmult_1_r.
              R_simplify. simpl. solve_linear.
            + repeat rewrite Rplus_assoc.
              match goal with
                | [ H : Rlt ?e1 ?e2 |- Rle (Rplus ?e1 ?e3) _ ]
                  => apply Rle_trans with (r2:=Rplus e2 e3);
                    [ solve_linear | clear H ]
              end.
              rewrite H7 in H9.
              assert (hd tr "v" - x <= 0)%R by solve_linear.
              clear H8.
              unfold ubv_r in *.
              R_simplify. simpl.
              apply Rminus_le.
              R_simplify. simpl.
              rewrite Rmult_comm.
              apply Rmult_le_0; solve_linear.
              clear H10. generalize dependent (hd tr "v").
              intros. clear dependent tr.
              Time solve_nonlinear.
            + unfold ubv_r in *. Time solve_nonlinear.
          - apply imp_strengthen with (F2:="v" < --vt + ubV);
              [ solve_linear | ].
            solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.inv2, ub, ubV, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H7 in H9.
              assert (hd tr "v" + 1 * x < 0)%R by solve_linear.
              solve_linear.
            + rewrite H7 in H9. clear H10.
              unfold ubv_r in *.
              Time solve_nonlinear.
            + clear H10. unfold ubv_r in *.
              solve_linear.
            + clear H10. unfold ubv_r in *.
              Time solve_nonlinear.
          - solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.inv2, ub, ubV, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H6 in H8.
              assert (0 <= hd tr "v")%R by solve_linear.
              unfold amax, ubv_r in *. clear H9.
              Time solve_nonlinear.
            + rewrite H6 in H8. clear H9.
              destruct (Rle_dec 0 (hd tr "v"))%R.
              * unfold amax, ubv_r in *. Time solve_nonlinear.
              * assert (hd tr "v" * x + / 2 * (0 - 1) * (x * (x * 1))
                      <= 0)%R
                       by (generalize dependent (hd tr "v"); intros; clear dependent tr;
                           clear r0; solve_nonlinear).
                solve_linear.
            + unfold ubv_r in *. Time solve_nonlinear. }
      * solve_linear.
Qed.

Lemma safety :
  |- (Init /\ []Next) --> []Safe.
Proof.
  apply imp_trans
  with (F2:=AbstractCtrl.Init /\ []AbstractCtrl.Next).
  - apply refinement.
  - apply AbstractCtrl.safety.
Qed.