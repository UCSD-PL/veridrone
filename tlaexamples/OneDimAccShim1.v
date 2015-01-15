Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Import LibNotations.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import TLA.ArithFacts.
Require Import TLA.Substitution.
Require Import AbstractIndAccCtrl.
Require Import OneDimAccShimUtil.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

(* This is an upper bound height shim
   for a one dimensional system where
   the controller can directly set the
   acceleration. *)

(* The parameters of this system *)
Module Params <: UtilParams.

  (* The upper bound *)
  Parameter ub : R.
  (* The positive delay of the controller *)
  Parameter d : R.
  Parameter Hd : (d > 0)%R.

  (* The minimum possible acceleration *)
  Parameter amin : R.
  Parameter Hamin : (amin < 0)%R.

  (* The maximum possible acceleration *)
  Parameter amax : R.
  Parameter Hamax : (amax > 0)%R.

End Params.
Import Params.

(* Specialize some useful definitions
   and lemmas to this system. *)
Module Util := Util(Params).
Import Util.

(* The system specification *)
Module System.

  (* Read sensors and the current time *)
  Definition Read : Formula :=
    "T"! = "t" /\ "H"! = "h" /\ "V"! = "v".

  (* The continuous dynamics of the system *)
  Definition Evolve : Formula :=
    Continuous (["h"' ::= "v",
                 "v"' ::= "a",
                 "a"' ::= 0,
                 "t"' ::= 1,
                 "H"' ::= 0,
                 "T"' ::= 0,
                 "V"' ::= 0]).

  (* Specialize the control Term to this
     system's parameters *)
  Definition CtrlTermUB :=
    CtrlTermUB "H" "V" amax amax.

  (* The controller *)
  Definition Ctrl : Formula :=
       (CtrlTermUB d d /\ CtrlTermUB 0 d /\
        "A" <= amax /\ "a"! = "A")
    \/ ("a"! = amin).

  (* The transition formula for the whole system *)
  Definition Next : Formula :=
       (Evolve /\ "t"! <= "T" + d)
    \/ (Ctrl /\ Read /\ Unchanged (["h", "v", "t"])).

  (* We don't write an initial state predicate here
     because we're going to use the initial state
     predicate of the abstract controller of which
     this will be a refinement. See AbstractCtrl
     below. *)

  (* The safety condition *)
  Definition Safe : Formula :=
    "h" <= ub.

End System.

Import System.

(* Now we want to prove safety of the system.
   We'll use AbstractIndAccCtrl for this. We
   need to supply some parameters to this
   abstract controller, which is what the
   following module does. *)
Module InvParams <: InvParameters.
  Definition d := d.
  Definition Hd := Hd.
  (* Formula expressing the inductive
     safety condition for this controller *)
  Definition Inv : Formula :=
    "a" <= amax /\
    (0 <= "v" --> "h" + (sdist "v") <= ub) /\
    ("v" < 0 --> "h" <= ub) /\
    ("h" <= "H" + tdist "V" amax d \/
     "h" <= "H") /\
    "v" <= "V" + amax*d.
  
  Lemma HInv_st : is_st_formula Inv.
  Proof.
    simpl. intuition.
  Qed.
  
  Lemma HInv_unch : forall (t:R),
    |- (Inv["H" + (tdist "V" "a" t)//"h"]
           ["V" + "a"*t//"v"] /\
        Unchanged (["a", "H", "V", "T"]))
         --> (next Inv)
             [next_term ("H" + (tdist "V" "a" t))/!"h"]
             [next_term ("V" + "a"*t)/!"v"].
  Proof.
    solve_linear;
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
             end; solve_linear.
  Qed.
  
End InvParams.

(* We pass the parameters to the module. *)
Module AbstractCtrl := AbstractIndAccCtrlMod(InvParams).

(* We ultimately want to prove the lemma safety
   at the end of this file. We do this in two
   steps:
     1) Show that our inductive safety condition
        Inv implies the safety condition
        we care about, Safe (inv_safe).
     2) Show that this system spec is a refinement
        of the abstract system spec in the module
        AbstractCtrl (refinement)
   Then by transitivity, we prove safety. *)

(* A proof that the inductive safety condition
   Inv implies the safety contition
   we actually care about, Safe. *)
Lemma inv_safe : |- InvParams.Inv --> Safe.
Proof.
  pose proof Hd.
  pose proof Hamin.
  simpl; unfold eval_comp; simpl; intros.
  decompose [and] H1. clear H1 H5.
  generalize dependent (hd tr "t" - hd tr "T")%R.
  intros. unfold amininv in *.
  destruct (Rle_dec R0 (hd tr "v"))%R;
    solve_linear.
  match goal with
    | [ _ : Rle ?r ub |- _ ]
      => apply Rle_trans with (r2:=r); auto
  end.
  rewrite <- Rplus_0_r at 1.
  apply Rplus_le_compat_l.
  apply Rmult_0_le; solve_linear.
  apply Rmult_0_le; solve_linear.
  apply pow_0_le.
  rewrite <- Rplus_0_r at 1.
  apply Rplus_le_compat_l.
  solve_linear.
Qed.

(* Further specialize a utility lemma *)
Definition CtrlTerm_incr :=
  CtrlTerm_incr "H" "V" amax amax.

(* A proof that this system spec is a refinement
   of the abstract system spec in the module
   AbstractCtrl. *)
Lemma refinement :
  |- (AbstractCtrl.Init /\ []Next)
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
            + pose proof (CtrlTerm_incr x tr).
              assert (amax >= 0)%R by solve_linear.
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
              * pose proof (CtrlTerm_incr x tr).
                assert (amax >= 0)%R by solve_linear.
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
            + pose proof (CtrlTerm_incr x tr).
              assert (amax >= 0)%R by solve_linear.
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
              * pose proof (CtrlTerm_incr x tr).
                assert (amax >= 0)%R by solve_linear.
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
              unfold amininv in *.
              eapply Rle_trans; eauto.
              R_simplify; solve_linear.
          - destruct (Rle_dec R0 (hd tr "v")).
            + intuition.
              unfold amininv in *.
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
              unfold amininv in *.
              eapply Rle_trans; eauto.
              R_simplify; solve_linear.
          - destruct (Rle_dec R0 (hd tr "v")).
            + intuition.
              unfold amininv in *.
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

(* Finally, we prove the safety condition
   we care about using inv_safe and refinement. *)
Lemma safety :
  |- (AbstractCtrl.Init /\ []Next) --> []Safe.
Proof.
  apply imp_trans
  with (F2:=AbstractCtrl.Init /\ []AbstractCtrl.Next).
  - apply refinement.
  - apply imp_trans
    with (F2:=[]InvParams.Inv).
    + apply AbstractCtrl.safety.
    + apply always_imp. apply inv_safe.
Qed.