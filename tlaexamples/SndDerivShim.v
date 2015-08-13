Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import TLA.DifferentialInduction.
Require Import Examples.System.
Require Import Examples.SensorWithError.
Require Import SensorWithDelayRange.
Require Import Examples.SensorWithDelayRangeSndOrder.
Require Import Examples.SecondDerivShimCtrl.
Require Import ChargeTactics.Lemmas.

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

  Definition WC : Formula := ltrue.

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

Require Import Coq.Lists.List.

Definition CtrlSenseErrorSysR err :=
  SysCompose
    (SysRename (VarRenameMap (("x","v")::("Xmax","Vmax")::("Xmin","Vmin")::nil))
            (SensorWithError.SpecR err ShimParams.d))
    (SysCompose
       (SysRename (VarRenameMap (("x","y")::("Xmax","Ymax")::nil))
                   (SensorWithError.SpecR err ShimParams.d))
       ShimCtrl.SpecR).

Definition CtrlSenseErrorSys err :=
  SysD (CtrlSenseErrorSysR err).

Theorem ctrl_sense_error_safe : forall err,
  |-- CtrlSenseErrorSys err -->> []"y" <= ShimParams.ub.
Proof.
  intro err.
  apply imp_trans with
  (F2:=[](Rename (VarRenameMap (("x","v")::("Xmax","Vmax")::("Xmin","Vmin")::nil))
                 SensorWithError.SenseSafe //\\
          Rename (VarRenameMap (("x","y")::("Xmax","Ymax")::nil))
          SensorWithError.SenseSafe //\\
          "y" <= ShimParams.ub)).
  - apply Compose.
    + apply SysSafe_rule; apply always_tauto.
      enable_ex_st; repeat eexists; solve_linear.
    + tlaIntro. rewrite <- Rename_always.
      rewrite <- (SensorWithError.sense_safe err ShimParams.d).
      rewrite SysRename_sound.
      * charge_tauto.
      * simpl. intuition.
      * compute. intuition congruence.
      * 
    + apply Compose.
      * apply SysSafe_rule; apply always_tauto.
        enable_ex_st; repeat eexists; solve_linear.
      * tlaIntro. tlaRevert. apply forget_prem.
        tlaIntro. pose proof (SensorWithError.sense_safe err ShimParams.d).
        apply Proper_Rename
        with (m:=VarRenameMap (("x","y")::("Xmax","Ymax")::nil))
          in H. revert H. unfold SensorWithError.SenseSafe.
        Rename_rewrite; try solve [ apply VarRenameMap_is_st_term ].
        simpl rename_formula. intro H. charge_apply H.
        apply SysRename_sound.
        { simpl. intuition. }
        { compute. intuition congruence. }
        { admit. }
      * tlaIntro. pose proof ShimCtrl.ctrl_safe.
        unfold ShimCtrl.Safe in *. charge_apply H.
        unfold ShimCtrl.Spec. unfold SensorWithError.SenseSafe.
        Rename_rewrite; try solve [apply VarRenameMap_is_st_term].
        simpl rename_formula.
        repeat rewrite <- Always_and.
        repeat charge_split; try charge_assumption;
        solve_linear.
  - apply always_imp. charge_tauto.
Qed.

Definition DelayCompensatorV :=
  (SensorWithDelayRange.SpecR
     "v" "Vmax_pre" "Vmin_pre" "Vmax"
     "Vmin" "a" ShimParams.d ltrue).

Definition CtrlSenseDelaySysR :=
  SysCompose DelayCompensatorV
    (SysCompose DelayCompensator.SpecR ShimCtrl.SpecR).

Definition CtrlSenseDelaySys :=
  SysD CtrlSenseDelaySysR.

Theorem ctrl_sense_delay_safe :
  []"Vmin_pre" <= "v" //\\ []"v" <= "Vmax_pre"
  //\\ []"y" <= "Ymax_pre"
    |-- CtrlSenseDelaySys -->> []"y" <= ShimParams.ub.
Proof.
  apply imp_trans with
  (F2:=[](SensorWithDelayRange.SenseSafe "v" "Vmax" "Vmin"
          //\\ DelayCompensator.SenseSafe
          //\\ "y" <= ShimParams.ub)).
  - apply Compose.
    + tlaIntro.
      pose proof
           (SensorWithDelayRange.sense_safe
              "v" "Vmax_pre" "Vmin_pre" "Vmax" "Vmin" "a"
              ShimParams.d (eq_refl _) (eq_refl _) (eq_refl _)
              (eq_refl) ltrue).
      charge_apply H. rewrite <- Always_and.
      charge_tauto.
    + apply Compose.
      * tlaIntro. charge_apply DelayCompensator.sense_safe.
        unfold SenseSafe. repeat rewrite <- Always_and.
        charge_tauto.
      * tlaIntro.
        pose proof ShimCtrl.ctrl_safe.
        unfold ShimCtrl.Safe in *. charge_apply H.
        unfold Spec. unfold DelayCompensator.SenseSafe.
        charge_split; try charge_assumption.
        rewrite landC. tlaRevert. repeat rewrite Always_and.
        apply always_imp. solve_linear.
  - apply always_imp. charge_tauto.
Qed.

Definition CtrlSenseErrorDelaySysR err :=
  SysCompose
    (SensorWithError.SpecR "v" "Vmax_pre" "Vmin_pre" err
                           ShimCtrl.w ShimParams.d)
    (SysCompose
       (SensorWithError.SpecR "y" "Ymax_pre" "Ymin_pre" err
                              ShimCtrl.w ShimParams.d)
       CtrlSenseDelaySysR).

Definition CtrlSenseErrorDelaySys err :=
  SysD (CtrlSenseErrorDelaySysR err).

Theorem ctrl_sense_error_delay_safe : forall err,
  |-- CtrlSenseErrorDelaySys err -->> []"y" <= ShimParams.ub.
Proof.
  intros err.
  apply imp_trans with
  (F2:=[](SensorWithError.SenseSafe "v" "Vmax_pre" "Vmin_pre"
          //\\ SensorWithError.SenseSafe "y" "Ymax_pre" "Ymin_pre"
          //\\ "y" <= ShimParams.ub)).
  - apply Compose.
    + tlaIntro. apply SensorWithError.sense_safe; reflexivity.
    + apply Compose.
      * tlaIntro. tlaRevert. apply forget_prem.
        tlaIntro. apply SensorWithError.sense_safe; reflexivity.
      * tlaIntro. pose proof ctrl_sense_delay_safe.
        charge_apply H. unfold SensorWithError.SenseSafe.
        repeat rewrite <- Always_and. charge_tauto.
  - apply always_imp. charge_tauto.
Qed.
