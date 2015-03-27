Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Import LibNotations.
Require Import TLA.BasicProofRules.
Require Import TLA.DifferentialInduction.
Require Import Examples.System.
Require Import Examples.SensorWithError.
Require Import SensorWithDelayRange.
Require Import Examples.SensorWithDelayRangeSndOrder.
Require Import Examples.SecondDerivShimCtrl.

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

  Definition x := "y".
  Definition Xmax := "Ymax_pre".
  Definition Xmax_post := "Ymax".
  Definition xd1 := "v".
  Definition xd2 := "a".
  Definition xd1max := "Vmax".
  Definition X := "Y".
  Definition Xd1 := "V".
  Definition T := "T".
  Parameter d : R.

  Let w_all := ["t" '  ::= -- (1), x '  ::= xd1,
                xd1 ' ::= xd2, Xmax_post '  ::= 0,
                xd2 '  ::= 0, X ' ::= 0, Xd1 ' ::= 0,
                T ' ::= 0].
  Definition get_deriv_Xmax_post :
    get_deriv Xmax_post w_all = Some (NatT 0) :=
    eq_refl _.
  Definition get_deriv_xd2 :
    get_deriv xd2 w_all = Some (NatT 0) :=
    eq_refl _.
  Definition get_deriv_x :
    get_deriv x w_all = Some (VarNowT xd1) :=
    eq_refl _.
  Definition get_deriv_xd1 :
    get_deriv xd1 w_all = Some (VarNowT xd2) :=
    eq_refl _.
  Definition get_deriv_Xd1 :
    get_deriv Xd1 w_all = Some (NatT 0) :=
    eq_refl _.
  Definition get_deriv_X :
    get_deriv X w_all = Some (NatT 0) :=
    eq_refl _.
  Definition get_deriv_T :
    get_deriv T w_all = Some (NatT 0) :=
    eq_refl _.

  Parameter amin : R.
  Parameter amin_lt_0 : (amin < 0)%R.

  Definition WC := ltrue.

End DelayParams.

Module DelayCompensator :=
  SensorWithDelayRangeSndOrder(DelayParams).

Definition CtrlSenseErrorSysR err :=
  SysCompose
    (SensorWithError.SpecR "v" "Vmax" "Vmin" err
                           ShimCtrl.w ShimParams.d)
    (SysCompose
       (SensorWithError.SpecR "y" "Ymax" "Ymin" err
                              ShimCtrl.w ShimParams.d)
       ShimCtrl.SpecR).

Definition CtrlSenseErrorSys err :=
  SysD (CtrlSenseErrorSysR err).

Theorem ctrl_sense_error_safe : forall err,
  |-- CtrlSenseErrorSys err -->> []"y" <= ShimParams.ub.
Proof.
  intros err.
  apply imp_trans with
  (F2:=[]((SensorWithError.SenseSafe "v" "Vmax" "Vmin") //\\
          (SensorWithError.SenseSafe "y" "Ymax" "Ymin") //\\
          "y" <= ShimParams.ub)).
  - apply Compose.
    + tlaIntro. apply SensorWithError.sense_safe; reflexivity.
    + apply Compose.
      * tlaIntro. tlaRevert. apply forget_prem.
        tlaIntro. apply SensorWithError.sense_safe; reflexivity.
      * tlaIntro. pose proof ShimCtrl.ctrl_safe.
        unfold ShimCtrl.Safe in *. charge_apply H.
        unfold ShimCtrl.Spec. unfold SensorWithError.SenseSafe.
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
