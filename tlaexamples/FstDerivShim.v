Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import TLA.DifferentialInduction.
Require Import Examples.System.
Require Import Examples.SensorWithError.
Require Import Examples.SensorDelayFstDeriv.
Require Import Examples.SensorDelaySndDeriv.
Require Import Examples.FstDerivShimCtrl.
Require Import ChargeTactics.Lemmas.
Require Import Coq.Lists.List.

Open Scope HP_scope.
Open Scope string_scope.

Module ShimParams <: FirstDerivShimParams.

  (* The upper bound on y. *)
  Parameter ub : R.
  (* Max time between executions of the
     controller. *)
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.

End ShimParams.

Import ShimParams.

Module ShimCtrl := FirstDerivShim(ShimParams).

Let rename_v :=
  RenameListC (("x","v")::("Xmax","Vmax")::nil).

Definition SensorErrorV err :
  { x : SysRec &
        SysRec_equiv
          (SysRename
             (to_RenameMap rename_v)
             (deriv_term_RenameList rename_v)
             (SensorWithError.SpecR err d))
          x}.
Proof.
  discharge_sysrec_equiv_rename.
Defined.

Definition CtrlSenseErrorSysR err :=
  SysCompose (projT1 (SensorErrorV err))
             ShimCtrl.SpecR.

Theorem ctrl_sense_error_safe : forall err,
  |-- SysD (CtrlSenseErrorSysR err) -->> []"v" <= ub.
Proof.
  intro err.
  charge_intros. eapply lcut.
  { tlaRevert. apply Compose.
    - rewrite_rename_pf (SensorErrorV err).
      rewrite SysRename_sound
        by sysrename_side_cond.
      pose proof
           (SensorWithError.sense_safe err ShimParams.d).
      rename_hyp rename_v H.
      rewrite Rename_Always in H.
      charge_intros. apply H.
    - rewrite landtrueL.
      repeat rewrite <- Rename_ok by rw_side_condition.
      simpl rename_formula. restoreAbstraction.
      rewrite <- ShimCtrl.ctrl_safe.
      rewrite <- Always_and. charge_tauto. }
  { repeat rewrite <- Always_and. charge_tauto. }
Qed.

Let rename_v_delay :=
  RenameListC (("x","v")::("v","a")::("Xmax","Vmax_pre")::
               ("Xmax_post","Vmax")::nil).

Definition DelayCompensatorV :
  { x : SysRec &
        SysRec_equiv
          (SysRename
             (to_RenameMap rename_v_delay)
             (deriv_term_RenameList rename_v_delay)
             (SensorDelayFstDeriv.SpecR ShimParams.d))
          x}.
Proof.
  discharge_sysrec_equiv_rename.
Defined.

Definition CtrlSenseDelaySysR :=
  SysCompose (projT1 DelayCompensatorV)
             ShimCtrl.SpecR.

Theorem ctrl_sense_delay_safe :
  []"v" <= "Vmax_pre"
    |-- SysD CtrlSenseDelaySysR -->> []"v" <= ub.
Proof.
  charge_intros. eapply lcut.
  { eapply landAdj. apply Compose.
    - rewrite_rename_pf DelayCompensatorV.
      rewrite SysRename_sound
        by sysrename_side_cond.
      pose proof
           (SensorDelayFstDeriv.sense_safe ShimParams.d).
      rename_hyp rename_v_delay H.
      rewrite Rename_Always in H.
      charge_intros. rewrite <- H.
      rewrite Rename_and. rewrite Rename_Always.
      charge_split; [ | charge_tauto ].
      rewrite landC. tlaRevert. apply forget_prem.
      rewrite <- Rename_ok by rw_side_condition.
      repeat rewrite Always_and. apply always_imp.
      simpl rename_formula. charge_tauto.
    - repeat rewrite <- Rename_ok by rw_side_condition.
      simpl rename_formula. restoreAbstraction.
      rewrite <- ShimCtrl.ctrl_safe. charge_tauto. }
  { repeat rewrite <- Always_and. charge_tauto. }
Qed.

Let rename_v_pre :=
  RenameListC (("x","v")::("Xmax","Vmax_pre")::nil).

Definition SensorErrorV_pre err :
  { x : SysRec &
        SysRec_equiv
          (SysRename
             (to_RenameMap rename_v_pre)
             (deriv_term_RenameList rename_v_pre)
             (SensorWithError.SpecR err ShimParams.d))
          x}.
Proof.
  discharge_sysrec_equiv_rename.
Defined.

Definition CtrlSenseErrorDelaySysR err :=
  SysCompose (projT1 (SensorErrorV_pre err))
             CtrlSenseDelaySysR.

Theorem ctrl_sense_error_delay_safe : forall err,
  |-- SysD (CtrlSenseErrorDelaySysR err) -->> []"v" <= ub.
Proof.
  intro err.
  charge_intros. eapply lcut.
  { tlaRevert. apply Compose.
    - rewrite_rename_pf (SensorErrorV_pre err).
      rewrite SysRename_sound
        by sysrename_side_cond.
      pose proof
           (SensorWithError.sense_safe err ShimParams.d).
      rename_hyp rename_v_pre H.
      rewrite Rename_Always in H.
      charge_intros. apply H.
    - repeat rewrite <- Rename_ok by rw_side_condition.
      simpl rename_formula. restoreAbstraction.
      rewrite <- ctrl_sense_delay_safe.
      repeat rewrite <- Always_and. charge_tauto. }
  { repeat rewrite <- Always_and. charge_tauto. }
Qed.
