Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import Examples.System.
Require Import Examples.FirstDerivShimCtrl.
Require Import ChargeTactics.Lemmas.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import BasicProofRules.
Require Import Coq.Lists.List.

Set Implicit Arguments.
Set Strict Implicit.

Module Type UpperLowerFirstParams.
  Parameter ub : R.
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
End UpperLowerFirstParams.

Module UpperLowerFirst (P : UpperLowerFirstParams).
  Module V <: FirstDerivShimParams.
    Definition ub := P.ub.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
  End V.

  Module Vel := FirstDerivShim V.

  Let mirror :=
    ("v",--"v")::("a",--"a")::nil.

  Definition SpecVelocityMirrorR :
    { x : SysRec &
          SysD x |-- Rename (to_RenameMap mirror)
                            (SysD Vel.SpecR) }.
  Proof.
    discharge_Sys_rename_formula.
    apply forget_prem.
    rewrite <- Rename_ok by is_st_term_list.
    enable_ex_st. smart_repeat_eexists.
    solve_linear.
  Defined.

  Definition SpecR :=
    SysCompose (projT1 SpecVelocityMirrorR) Vel.SpecR.

  Lemma UpperLower_ok :
    |-- SysD SpecR -->> []--P.ub <= "v" <= P.ub.
  Proof.
    apply Compose.
    - apply SysSafe_rule. apply always_tauto.
      simpl. restoreAbstraction.
      enable_ex_st. smart_repeat_eexists. solve_linear.
    - charge_intros.
      pose proof (projT2 SpecVelocityMirrorR).
      cbv beta in H. rewrite H. clear.
      pose proof Vel.ctrl_safe.
      apply (Proper_Rename (to_RenameMap mirror)
                           (to_RenameMap mirror)) in H;
        [ | reflexivity ].
      rewrite Rename_impl in H. rewrite Rename_True in H.
      restoreAbstraction. apply landAdj in H.
      rewrite landtrueL in H. rewrite H. clear.
      rewrite <- Rename_ok by rw_side_condition.
      tlaRevert. apply always_imp. unfold V.ub.
      solve_linear.
    - charge_intros. pose proof Vel.ctrl_safe.
      unfold V.ub in *. charge_apply H. charge_tauto. 
  Qed.

End UpperLowerFirst.
