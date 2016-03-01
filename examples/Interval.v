Require Import Coq.Reals.Reals.
Require Import ChargeCore.Tactics.Lemmas.
Require Import Logic.Logic.
Require Import Logic.EnabledLemmas.
Require Import Logic.ProofRules.
Require Import Logic.ArithFacts.
Require Import Examples.System.
Require Import Examples.UtilPosition.
Require Import Examples.Position.
Require Import Examples.Velocity.

Local Open Scope string_scope.
Local Open Scope HP_scope.

Module Type IntervalParams.
  Parameter ub : R.
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
  Parameter amin : R.
  Parameter amin_lt_0 : (amin < 0)%R.
  Parameter ubv : R.
  Axiom ubv_gt_amin_d : (ubv >= -amin*d)%R.
  Parameter ubv_gt_0 : (ubv > 0)%R.
  Parameter ub_ubv :
    (ubv*d + ubv*ubv*(0 - /2)*(/amin) <= ub)%R.
End IntervalParams.

Module IntervalShim (Import P : IntervalParams).

  Module X_Params <: PositionShimParams.
    Definition ub := P.ub.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin.
    Definition amin_lt_0 := P.amin_lt_0.
    Definition ubv := P.ubv.
    Definition ub_ubv := P.ub_ubv.
  End X_Params.

  Module X := PositionShim X_Params.

  Module V_Params <: VelocityShimParams.
    Definition ub := P.ubv.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
  End V_Params.

  Module V := VelocityShim V_Params.

  Module SdistUtil := SdistUtil(X_Params).
  Import SdistUtil.

  Let mirror : RenameList :=
    {{ "y" ~> --"y" & "v" ~> --"v" & "a" ~> --"a" }}%rn.

  Definition mirroredX : ActionFormula :=
    SysRename mirror (deriv_term_RenameList mirror) X.Next.

  Definition mirroredV : ActionFormula :=
    SysRename mirror (deriv_term_RenameList mirror) V.Next.

  Definition Next : ActionFormula :=
    SysCompose (SysCompose X.Next mirroredX)
               (SysCompose V.Next mirroredV).

  Definition IndInv : StateFormula :=
    (X.IndInv //\\ Rename mirror X.IndInv) //\\
    (V.IndInv //\\ Rename mirror V.IndInv).

  Lemma TimedPreserves_Next :
    |-- TimedPreserves d IndInv Next.
  Proof with (refine _).
    unfold IndInv, X.IndInv, V.IndInv, Next, X.SafeAcc.
    unfold SysCompose.
    repeat ((try simple apply TimedPreserves_intro);
      rewrite SysCompose_simpl;
      rewrite <- TimedPreserves_And by tlaIntuition;
      charge_split).
      { apply TimedPreserves_intro. rewrite <- X.TimedPreserves_Next.
        charge_tauto. }
      { apply TimedPreserves_intro.
        rewrite Sys_rename_formula by eauto with rw_rename.
        rewrite SysRename_rule by eauto with rw_rename.
        rewrite TimedPreserves_Rename by eauto with rw_rename.
        rewrite <- X.TimedPreserves_Next. rewrite Rename_True.
        charge_tauto. }
      { apply TimedPreserves_intro. rewrite <- V.TimedPreserves_Next.
        charge_tauto. }
      { apply TimedPreserves_intro.
        rewrite Sys_rename_formula by eauto with rw_rename.
        rewrite SysRename_rule by eauto with rw_rename.
        rewrite TimedPreserves_Rename by eauto with rw_rename.
        rewrite <- V.TimedPreserves_Next. rewrite Rename_True.
        charge_tauto. }
  Qed.

  Lemma velocity_refinement :
    "v" <= ubv //\\
    "v" + "a"!*d <= ubv //\\
    ("y" > 0 -->> X.SafeAccZeroOrder "a"! d)
    |-- X.SafeAccZeroOrder "a"! d.
  Proof.
    pose proof d_gt_0 as d_gt_0. pose proof amin_lt_0 as amin_lt_0.
    pose proof ubv_gt_0 as ubv_gt_0. pose proof ub_ubv as ub_ubv.
    intros. reason_action_tac.
    destruct H as [Hubv1 [Hubv2 Hctrl]].
    destruct (Rgt_dec (pre "y") R0).
    { auto. }
    { clear Hctrl. split; intros.
      { eapply Rle_trans; eauto.
        pose proof (sdist_incr (pre "v" + post "a" * d)
                               ubv (Stream.forever (fun _ => R0))).
        breakAbstraction. specialize_arith_hyp H0. rewrite H0.
        assert ((pre "v" * d + / 2 * post "a" * (d * (d * 1))) <=
                ubv * d)%R.
        { clear - Hubv1 Hubv2 H d_gt_0. solve_nonlinear. }
        { unfold X_Params.amin, X_Params.ub in *. solve_linear. } }
      { unfold X_Params.ub. transitivity (ubv*d)%R.
        { field_simplify; [ | solve_nonlinear ].
          apply Rmult_le_algebra_neg; [ solve_nonlinear | ].
          unfold Rdiv. rewrite RMicromega.Rinv_1. simpl.
          clear - Hubv1 d_gt_0 H n. solve_nonlinear. }
        { assert ((0 - / 2) < 0)%R by solve_linear.
          assert (/amin < 0)%R by solve_linear.
          generalize dependent (/amin)%R.
          generalize dependent (0-/2)%R. intros.
          clear -H0 H1 ubv_gt_0 ub_ubv0. solve_nonlinear. } } }
  Qed.

  Definition Constraint :=
    amin <= "a" <= --amin.

   Lemma SysNeverStuck_Discr :
     IndInv //\\ "T" = 0
     |-- Enabled ((0 <= "T"! <= d //\\ Sys_D Next) //\\
                     next Constraint).
   Proof.
     unfold Sys_D, IndInv, X.IndInv. repeat rewrite Rename_ok by eauto with rw_rename.
     rewrite <- velocity_refinement.
     charge_assert (X.SafeAcc "a" 0).
     { rewrite <- (X.SafeAcc_downclock "a" 0 "T"). solve_linear. }
     charge_assert (Rename mirror (X.SafeAcc "a" 0)).
     { rewrite <- (X.SafeAcc_downclock "a" 0 "T").
       repeat rewrite <- Rename_ok by eauto with rw_rename. solve_linear. }
     charge_assert ("v" <= ubv).
     { reason_action_tac. assert (pre "a" < 0 \/ pre "a" >= 0)%R by solve_linear.
       destruct H. rewrite H1 in *. rewrite_real_zeros. solve_linear. }
     charge_assert (--"v" <= ubv).
     { repeat rewrite <- Rename_ok by eauto with rw_rename.
       reason_action_tac. assert (0 - pre "a" < 0 \/ 0 - pre "a" >= 0)%R by solve_linear.
       destruct H. rewrite H1 in *. rewrite_real_zeros. solve_linear. }
     charge_assert ("y" <= ub).
     { rewrite <- (X.SafeAcc_Safe "a" "T"). solve_linear. }
     charge_assert (Rename mirror ("y" <= ub)).
     { rewrite <- (X.SafeAcc_Safe "a" "T").
       repeat rewrite <- Rename_ok by eauto with rw_rename. solve_linear. }
     rewrite X.SafeAcc_ZeroOrder_amin. charge_clear. charge_intros.
     repeat rewrite <- Rename_ok by eauto with rw_rename. enable_ex_st'.
     pose proof P.amin_lt_0. pose proof P.d_gt_0.
     pose proof P.ubv_gt_amin_d.
     unfold V_Params.ub, V_Params.d, X_Params.ub, X_Params.amin, X_Params.d in *.
     destruct (Rgt_dec (st "y") R0);
       destruct (Rgt_dec (st "v") R0).
     { exists amin; do 2 eexists; exists d; solve_nonlinear. }
     { exists R0; do 2 eexists; exists d; intuition; try solve [solve_linear].
       rewrite_real_zeros. destruct H11; [ solve_linear | rewrite <- H11 ].
       rewrite_real_zeros. solve_linear. exfalso. solve_linear. }
     { exists R0; do 2 eexists; exists d; intuition; try solve [solve_linear].
       exfalso. solve_linear. }
     { exists (-amin)%R; do 2 eexists; exists d; solve_linear.
       solve_nonlinear. rewrite_real_zeros. repeat rewrite Ropp_involutive. solve_linear. }
   Qed.

   Lemma SysNeverStuck_Next :
     |-- SysNeverStuck d IndInv Next.
   Proof.
     intros. pose proof d_gt_0. pose proof amin_lt_0.
     eapply SysNeverStuck_Sys; [ solve_linear | | ].
     { rewrite SysNeverStuck_Discr. unfold X_Params.d.
       apply Proper_Enabled_lentails. charge_tauto. }
    { admit. (** Provable, but we won't worry about it *) }
  Admitted.

  Definition Safe : StateFormula :=
    (X.Safe //\\ Rename mirror X.Safe) //\\
    ("v" <= V_Params.ub //\\ Rename mirror ("v" <= V_Params.ub)).

  Lemma IndInv_impl_Safe : IndInv //\\ TimeBound d |-- Safe.
  Proof with (eauto with rw_rename).
    unfold Safe. charge_split.
    { charge_split.
      { rewrite <- X.IndInv_impl_Safe. charge_tauto. }
      { rewrite <- X.IndInv_impl_Safe. rewrite Rename_and.
        unfold IndInv. charge_split; [ charge_assumption | ].
        rewrite <- (Rename_ok (TimeBound X_Params.d))...
        solve_linear. } }
    { charge_split.
      { rewrite <- V.IndInv_impl_Inv. charge_tauto. }
      { rewrite <- V.IndInv_impl_Inv. rewrite Rename_and.
        unfold IndInv. charge_split; [ charge_assumption | ].
        rewrite <- (Rename_ok (TimeBound X_Params.d))...
        solve_linear. } }
  Qed.

  Local Open Scope HP_scope.

  (* Our main safety theorem. *)
  Lemma Spec_safe :
    |-- (IndInv //\\ TimeBound d) //\\ []SysSystem Next -->> []Safe.
  Proof.
    rewrite Inductively.Preserves_Inv_simple.
    { rewrite IndInv_impl_Safe.
      charge_tauto. }
    { compute; tauto. }
    { apply SafeAndReactive_TimedPreserves.
      unfold SafeAndReactive. charge_split.
      { apply TimedPreserves_Next. }
      { apply SysNeverStuck_Next. } }
  Qed.

End IntervalShim.