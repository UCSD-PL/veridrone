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
Require Import Compile2.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

(* This is an upper bound height shim
   for a one dimensional system where
   the controller can directly set the
   acceleration. This means that the
   shim (Ctrl below) takes a proposed
   acceleration ("A") and decides whether
   it is safe. If it is safe, the shim
   sets the acceleration to "A". Otherwise,
   the shim sets the acceleration to
   some safe value. The safety check and
   the safe value are such that the height
   of the system will always stay below
   the upper bound. *)

(* The parameters of this system *)
Module Params <: UtilParams.

  (* The upper bound *)
  Parameter ub : Floats.float.

  (* The positive delay of the controller *)
  Parameter d : Floats.float.
  Parameter Hd : (d > 0)%R.

  (* The minimum possible acceleration *)
  Parameter amin : Floats.float.
  Parameter Hamin : (amin < 0)%R.

End Params.
Import Params.

(* Specialize some useful definitions
   and lemmas to this system. *)
Module UtilSrc := UtilSrc(Params).
Import UtilSrc.
Module Util := Util(Params).
Import Util.

(* The system specification *)

  (* Read sensors and the current time *)
Definition Read : progr :=
  ([PIF FTRUE
    PTHEN ["T" !!= "t", "H" !!= "h", "V" !!= "v"]])%SL.

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
Definition CtrlTermUB_src :=
  CtrlTermUB_src "H" "V".

(* The safety check on proposed accelerations *)
Definition SafeCtrl : FlatFormula :=
     (("a" >= 0 /\ tdist_src "V" "a" d >= 0 /\ "A" >= 0 /\
       CtrlTermUB_src "a" "A" d d)
  \/ ("a" >= 0 /\ tdist_src "V" "a" d < 0 /\ "A" >= 0 /\
      CtrlTermUB_src "a" "A" 0 d)
  \/ ("a" < 0 /\ tdist_src "V" 0 d >= 0 /\ "A" >= 0 /\
      CtrlTermUB_src 0 "A" d d)
  \/ ("a" < 0 /\ tdist_src "V" 0 d < 0 /\ "A" >= 0 /\
      CtrlTermUB_src 0 "A" 0 d)
  \/ ("a" >= 0 /\ tdist_src "V" "a" d >= 0 /\ "A" < 0 /\
      CtrlTermUB_src "a" 0 d d)
  \/ ("a" >= 0 /\ tdist_src "V" "a" d < 0 /\ "A" < 0 /\
      CtrlTermUB_src "a" 0 0 d)
  \/ ("a" < 0 /\ tdist_src "V" 0 d >= 0 /\ "A" < 0 /\
      CtrlTermUB_src 0 0 d d)
  \/ ("a" < 0 /\ tdist_src "V" 0 d < 0 /\ "A" < 0 /\
      CtrlTermUB_src 0 0 0 d))%SL.

(* The controller *)
Definition Ctrl : progr :=
  ([PIF SafeCtrl PTHEN ["a" !!= "A"],
    PIF FTRUE PTHEN ["a" !!= amin]])%SL.

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

(* End of system specification *)

(* Now we want to prove safety of the system.
   We'll use AbstractIndAccCtrl for this. We
   need to supply some parameters to this
   abstract controller, which is what the
   following module does. *)
Module InvParams <: InvParameters.
  Definition d : R := d.
  Definition Hd := Hd.
  (* Formula expressing the inductive
     safety condition for this controller *)
  Definition Inv : Formula :=
    (0 <= "v" --> "h" + (sdist "v") <= ub) /\
    ("v" < 0 --> "h" <= ub) /\
    ("a" >= 0 --> tdist "V" "a" d >= 0 -->
     "h" <= "H" + tdist "V" "a" d) /\
    ("a" < 0 --> tdist "V" 0 d >= 0 -->
     "h" <= "H" + tdist "V" 0 d) /\
    ((("a" >= 0 /\ tdist "V" "a" d < 0) \/
      ("a" < 0 /\ tdist "V" 0 d < 0)) -->
     "h" <= "H") /\
    ("a" >= 0 --> "v" <= "V" + "a"*d) /\
    ("a" < 0 --> "v" <= "V").
  
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
  destruct (Rle_dec R0 (Semantics.hd tr "v"))%R;
    solve_linear.
  eapply Rle_trans; eauto.
  rewrite <- Rplus_0_r at 1.
  apply Rplus_le_compat_l.
  apply Rmult_0_le; solve_linear.
  apply Rmult_0_le; solve_linear.
  apply inv_0_le.
  solve_linear.
Qed.

(* A proof that this system spec is a refinement
   of the abstract system spec in the module
   AbstractCtrl. *)
Lemma refinement :
  |- (AbstractCtrl.Init /\ []Next)
       --> (AbstractCtrl.Init /\ []AbstractCtrl.Next).
Proof.
  pose proof Hd. pose proof Hamin.
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
          - solve_linear; rewrite_next_st.
            + assert (0 <= Semantics.hd tr "v")%R.
              * match goal with
                  | [ H : _ |- _ ]
                      => eapply Rle_trans; [ apply H | ];
                         apply Rplus_le_algebra; R_simplify;
                         rewrite Rmult_comm;
                         apply Rmult_le_0; solve_linear
                end.
              * intuition.
                eapply Rle_trans; eauto.
                apply Rplus_le_algebra.
                R_simplify; solve_linear.
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
          - solve_linear; rewrite_next_st.
            + destruct (Rlt_dec (Semantics.hd tr "v") R0).
              * intuition. eapply Rle_trans; eauto.
                apply Rplus_le_l.
                apply (tdist_vel_neg "v" amin x);
                  solve_linear.
              * assert (0 <= Semantics.hd tr "v")%R
                  by solve_linear.
                intuition. eapply Rle_trans; eauto.
                apply Rplus_le_algebra.
                R_simplify; simpl; solve_linear.
                { rewrite Rmult_comm. apply Rmult_le_0.
                  - apply inv_0_le. solve_linear.
                  - unfold InvParams.d in *.
                    solve_nonlinear. }
            + assert (Semantics.hd tr "v" < 0)%R.
              * { apply Rle_lt_trans
                  with (r2:=(Semantics.hd tr "v"+
                             Semantics.hd tr "A"*x)%R); auto.
                  assert (0 <= Semantics.hd tr "A"*x)%R.
                  - apply Rmult_0_le; solve_linear.
                  - solve_linear. }
              * intuition. eapply Rle_trans; eauto.
                apply Rplus_le_l.
                apply (tdist_vel_neg "v" "A" x);
                  solve_linear.
            + assert (Semantics.hd tr "v" < 0)%R.
              * { apply Rle_lt_trans
                  with (r2:=(Semantics.hd tr "v"+
                             Semantics.hd tr "A"*x)%R); auto.
                  assert (0 <= Semantics.hd tr "A"*x)%R.
                  - apply Rmult_0_le; solve_linear.
                  - solve_linear. }
              * intuition. eapply Rle_trans; eauto.
                apply Rplus_le_l.
                apply (tdist_vel_neg "v" "A" x);
                  solve_linear.
            + assert (Semantics.hd tr "v" < 0)%R.
              * { apply Rle_lt_trans
                  with (r2:=(Semantics.hd tr "v"+
                             Semantics.hd tr "A"*x)%R); auto.
                  assert (0 <= Semantics.hd tr "A"*x)%R.
                  - apply Rmult_0_le; solve_linear.
                  - solve_linear. }
              * intuition. eapply Rle_trans; eauto.
                apply Rplus_le_l.
                apply (tdist_vel_neg "v" "A" x);
                  solve_linear.
            + assert (Semantics.hd tr "v" < 0)%R.
              * { apply Rle_lt_trans
                  with (r2:=(Semantics.hd tr "v"+
                             Semantics.hd tr "A"*x)%R); auto.
                  assert (0 <= Semantics.hd tr "A"*x)%R.
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
              assert (0 <= Semantics.hd tr "V"+
                           Semantics.hd tr "a"*d)%R.
              * apply (tdist_pos_vel_pos "V" "a" d);
                solve_linear.
              * { assert (0 <= (Semantics.hd tr "V"+
                                Semantics.hd tr "a"*d)*d +
                               / 2 * 0 * (d * (d * 1)))%R.
                  - rewrite_real_zeros.
                    apply Rmult_0_le; solve_linear.
                  - intuition.
                    assert (0 <=
                            (Semantics.hd tr "V"+
                             (Semantics.hd tr "a"*d+0*d))*
                            ((Semantics.hd tr "V"+
                              (Semantics.hd tr "a"*d+0*d))*1)
                            * / ((0 - 2) * amin))%R.
                    + apply Rmult_0_le.
                      * apply Rmult_0_le; solve_linear.
                      * apply inv_0_le.
                        solve_linear.
                    + solve_linear. }
            + destruct (Rlt_dec (Semantics.hd tr "v") R0).
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
                { assert (0 <= (Semantics.hd tr "V"+
                                Semantics.hd tr "a"*d)*d +
                               / 2 * 0 * (d * (d * 1)))%R.
                  - rewrite_real_zeros.
                    unfold InvParams.d in *.
                    apply Rmult_0_le; solve_linear.
                  - intuition.
                    assert (0 <=
                            (Semantics.hd tr "V"+
                             (Semantics.hd tr "a"*d+0*d))*
                            ((Semantics.hd tr "V"+
                              (Semantics.hd tr "a"*d+0*d))*1)
                            * / ((0 - 2)*amin))%R.
                    + apply Rmult_0_le.
                      * apply pow_0_le.
                      * apply inv_0_le.
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
              assert (0<=Semantics.hd tr "V"*
                         (Semantics.hd tr "V"*1)*
                         /((0-2)*amin))%R.
              * { apply Rmult_0_le.
                  - apply pow_0_le.
                  - rewrite Rminus_0_l.
                    apply inv_0_le.
                    solve_linear. }
              * solve_linear.
            + assert (Semantics.hd tr "v" < 0)%R.
              * apply Rle_lt_trans
                with (r2:=(Semantics.hd tr "V")%R);
                solve_linear.
                revert H11 H1 H6.
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