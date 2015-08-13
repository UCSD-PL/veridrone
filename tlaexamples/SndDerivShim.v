Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import TLA.DifferentialInduction.
Require Import Examples.System.
Require Import Examples.SensorWithError.
Require Import Examples.SensorDelayFstDeriv.
Require Import Examples.SensorDelaySndDeriv.
Require Import Examples.SndDerivShimCtrl.
Require Import ChargeTactics.Lemmas.
Require Import Coq.Lists.List.

Open Scope HP_scope.
Open Scope string_scope.

Module ShimParams <: SecondDerivShimParams.

  (* The upper bound on y. *)
  Parameter ub : R.
  (* Max time between executions of the
     controller. *)
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
  (* Our breaking acceleration. *)
  Parameter amin : R.
  Parameter amin_lt_0 : (amin < 0)%R.

End ShimParams.

Module ShimCtrl := SecondDerivShimCtrl(ShimParams).

Module DelayParams <: SensorWithDelayRangeSndOrderParams.

  Parameter d : R.

  Parameter amin : R.
  Parameter amin_lt_0 : (amin < 0)%R.

  Definition WC := ltrue.

End DelayParams.

Module DelayCompensator :=
  SensorWithDelayRangeSndOrder(DelayParams).

Let rename_v :=
  RenameListC (("x","v")::("Xmax","Vmax")::nil).

Let rename_y :=
  RenameListC (("x","y")::("Xmax","Ymax")::nil).

Definition SensorErrorY err :
  { x : SysRec &
        SysRec_equiv
          (SysRename
             (to_RenameMap rename_y)
             (deriv_term_RenameList rename_y)
             (SensorWithError.SpecR err ShimParams.d))
          x}.
Proof.
  discharge_sysrec_equiv_rename.
Defined.

Definition SensorErrorV err :
  { x : SysRec &
        SysRec_equiv
          (SysRename
             (to_RenameMap rename_v)
             (deriv_term_RenameList rename_v)
             (SensorWithError.SpecR err ShimParams.d))
          x}.
Proof.
  discharge_sysrec_equiv_rename.
Defined.

Definition CtrlSenseErrorSysR errV errY :=
  SysCompose (projT1 (SensorErrorV errV))
             (SysCompose (projT1 (SensorErrorY errY))
                         ShimCtrl.SpecR).

Theorem ctrl_sense_error_safe : forall errV errY,
  |-- SysD (CtrlSenseErrorSysR errV errY) -->>
      []"y" <= ShimParams.ub.
Proof.
  intros errV errY.
  charge_intros. eapply lcut.
  { tlaRevert. apply Compose.
    - rewrite_rename_pf (SensorErrorV errV).
      rewrite SysRename_sound
        by sysrename_side_cond.
      pose proof
           (SensorWithError.sense_safe errV ShimParams.d).
      rename_hyp rename_v H.
      rewrite Rename_Always in H.
      charge_intros. apply H.
    - rewrite landtrueL. apply Compose.
      + rewrite_rename_pf (SensorErrorY errY).
        rewrite SysRename_sound
          by sysrename_side_cond.
        pose proof
             (SensorWithError.sense_safe errY ShimParams.d).
        rename_hyp rename_y H.
        rewrite Rename_Always in H.
        charge_intros. rewrite H. rewrite Always_and.
        charge_assumption.
      + repeat rewrite <- Rename_ok by rw_side_condition.
        simpl rename_formula. restoreAbstraction.
        rewrite <- ShimCtrl.ctrl_safe.
        repeat rewrite Always_and. tlaRevert.
        apply always_imp. solve_linear. }
  { unfold ShimCtrl.Safe. repeat rewrite <- Always_and.
    charge_tauto. }
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

Let rename_y_delay :=
  RenameListC (("x","y")::("Xmax","Ymax_pre")::
               ("Xmax_post","Ymax")::("Vmax","Vmax_pre")::
               ("Vmax_post","Vmax")::nil).

Definition DelayCompensatorY :
  { x : SysRec &
        SysRec_equiv
          (SysRename
             (to_RenameMap rename_y_delay)
             (deriv_term_RenameList rename_y_delay)
             DelayCompensator.SpecR)
          x}.
Proof.
  discharge_sysrec_equiv_rename.
Defined.

Definition CtrlSenseDelaySysR :=
  SysCompose (projT1 DelayCompensatorV)
    (SysCompose (projT1 DelayCompensatorY)
                ShimCtrl.SpecR).

Theorem ctrl_sense_delay_safe :
  []"v" <= "Vmax_pre" //\\ []"y" <= "Ymax_pre"
    |-- SysD CtrlSenseDelaySysR -->> []"y" <= ShimParams.ub.
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
    - apply Compose.
      + rewrite_rename_pf DelayCompensatorY.
        rewrite SysRename_sound
          by sysrename_side_cond.
        pose proof DelayCompensator.sense_safe.
        rename_hyp rename_y_delay H.
        rewrite Rename_Always in H.
        charge_intros. rewrite <- H.
        rewrite Rename_and. rewrite Rename_Always.
        charge_split; [ | charge_tauto ].
        tlaAssert ([]"v" <= "Vmax_pre" //\\
                   []"y" <= "Ymax_pre");
          [ charge_tauto | apply forget_prem ].
        rewrite <- Rename_ok by rw_side_condition.
        simpl rename_formula. restoreAbstraction.
        rewrite Always_and. charge_tauto.
      + repeat rewrite <- Rename_ok by rw_side_condition.
        simpl rename_formula. restoreAbstraction.
        rewrite <- ShimCtrl.ctrl_safe.
        repeat rewrite Always_and. tlaRevert.
        apply always_imp. solve_linear. }
  { unfold ShimCtrl.Safe. repeat rewrite <- Always_and.
    charge_tauto. }
Qed.

Let rename_v_pre :=
  RenameListC (("x","v")::("Xmax","Vmax_pre")::nil).

Let rename_y_pre :=
  RenameListC (("x","y")::("Xmax","Ymax_pre")::nil).

Definition SensorErrorY_pre err :
  { x : SysRec &
        SysRec_equiv
          (SysRename
             (to_RenameMap rename_y_pre)
             (deriv_term_RenameList rename_y_pre)
             (SensorWithError.SpecR err ShimParams.d))
          x}.
Proof.
  discharge_sysrec_equiv_rename.
Defined.

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

Definition CtrlSenseErrorDelaySysR errV errY :=
  SysCompose (projT1 (SensorErrorV_pre errV))
             (SysCompose (projT1 (SensorErrorY_pre errY))
                         CtrlSenseDelaySysR).

Theorem ctrl_sense_error_delay_safe : forall errV errY,
  |-- SysD (CtrlSenseErrorDelaySysR errV errY) -->>
      []"y" <= ShimParams.ub.
Proof.
  intros errV errY.
  charge_intros. eapply lcut.
  { tlaRevert. apply Compose.
    - rewrite_rename_pf (SensorErrorV_pre errV).
      rewrite SysRename_sound
        by sysrename_side_cond.
      pose proof
           (SensorWithError.sense_safe errV ShimParams.d).
      rename_hyp rename_v_pre H.
      rewrite Rename_Always in H.
      charge_intros. apply H.
    - rewrite landtrueL. apply Compose.
      + rewrite_rename_pf (SensorErrorY_pre errY).
        rewrite SysRename_sound
          by sysrename_side_cond.
        pose proof
             (SensorWithError.sense_safe errY ShimParams.d).
        rename_hyp rename_y_pre H.
        rewrite Rename_Always in H.
        charge_intros. rewrite <- H. charge_tauto.
      + repeat rewrite <- Rename_ok by rw_side_condition.
        simpl rename_formula. restoreAbstraction.
        rewrite <- ctrl_sense_delay_safe.
        repeat rewrite <- Always_and. charge_tauto. }
  { unfold ShimCtrl.Safe. repeat rewrite <- Always_and.
    charge_tauto. }
Qed.
