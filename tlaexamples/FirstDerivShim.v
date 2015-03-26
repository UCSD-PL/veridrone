Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import Examples.System.
Require Import Examples.SensorWithError.
Require Import Examples.SensorWithDelay.
Require Import Examples.SensorWithDelayRange.
Require Import Examples.FirstDerivShimCtrl.

Open Scope HP_scope.
Open Scope string_scope.

Definition CtrlSenseErrorSysR ub d err :=
  SysCompose (SensorWithError.SpecR "v" "Vmax" "Vmin" err
                                    FirstDerivShimCtrl.w d)
             (FirstDerivShimCtrl.SpecR ub d ltrue).

Definition CtrlSenseErrorSys ub d err :=
  SysD (CtrlSenseErrorSysR ub d err).

Theorem ctrl_sense_error_safe : forall ub d err,
  |-- CtrlSenseErrorSys ub d err -->> []"v" <= ub.
Proof.
  intros ub d err.
  apply imp_trans with
  (F2:=[]((SensorWithError.SenseSafe "v" "Vmax" "Vmin") //\\
          "v" <= ub)).
  - apply Compose.
    + tlaIntro. apply SensorWithError.sense_safe; reflexivity.
    + tlaIntro.
      pose proof (FirstDerivShimCtrl.ctrl_safe ub d ltrue).
      charge_apply H.
      unfold Spec. unfold SensorWithDelay.SenseSafe.
      charge_split; try charge_assumption.
      rewrite landC. tlaRevert. rewrite curry.
      tlaIntro. apply always_imp. solve_linear.
  - apply always_imp. charge_tauto.
Qed.

Definition CtrlSenseDelaySysR ub d :=
  (SysCompose (SensorWithDelayRange.SpecR
                            "v" "Vmax_pre" "Vmin_pre" "Vmax"
                            "Vmin" "a" d ltrue)
              (FirstDerivShimCtrl.SpecR ub d ltrue)).

Definition CtrlSenseDelaySys ub d :=
  SysD (CtrlSenseDelaySysR ub d).

Theorem ctrl_sense_delay_safe : forall ub d,
  []"Vmin_pre" <= "v" <= "Vmax_pre"
    |-- CtrlSenseDelaySys ub d -->> []"v" <= ub.
Proof.
  intros ub d.
  apply imp_trans with
  (F2:=[]((SensorWithDelay.SenseSafe "v" "Vmax" "Vmin") //\\
          "v" <= ub)).
  - apply Compose.
    + tlaIntro. apply SensorWithDelayRange.sense_safe;
                reflexivity.
    + tlaIntro.
      pose proof (FirstDerivShimCtrl.ctrl_safe ub d ltrue).
      charge_apply H.
      unfold Spec. unfold SensorWithDelay.SenseSafe.
      charge_split; try charge_assumption.
      rewrite landC. tlaRevert. rewrite Always_and.
      apply always_imp. solve_linear.
  - apply always_imp. charge_tauto.
Qed.

Definition CtrlSenseErrorDelaySysR ub d err :=
  SysCompose (SensorWithError.SpecR "v" "Vmax_pre" "Vmin_pre" err
                                    FirstDerivShimCtrl.w d)
             (CtrlSenseDelaySysR ub d).

Definition CtrlSenseErrorDelaySys ub d err :=
  SysD (CtrlSenseErrorDelaySysR ub d err).

Theorem ctrl_sense_error_delay_safe : forall ub d err,
  |-- CtrlSenseErrorDelaySys ub d err -->> []"v" <= ub.
Proof.
  intros ub d err.
  apply imp_trans with
  (F2:=[]((SensorWithError.SenseSafe "v" "Vmax_pre" "Vmin_pre")
            //\\ "v" <= ub)).
  - apply Compose.
    + tlaIntro. apply SensorWithError.sense_safe; reflexivity.
    + tlaIntro.
      pose proof (ctrl_sense_delay_safe ub d).
      charge_apply H. charge_tauto.
  - apply always_imp. charge_tauto.
Qed.
