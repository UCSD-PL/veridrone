Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import Examples.System.
Require Import Examples.SensorWithError.
Require Import Examples.SensorWithDelay.
Require Import Examples.FirstDerivShimCtrl.

Open Scope HP_scope.
Open Scope string_scope.

Definition CtrlSenseDelaySys ub d :=
  Sys ("Vmax"::"Vmin"::"a"::nil)%list ("v"::nil)%list
      (SensorWithDelay.Init "v" "Vmax" "Vmin" "a" //\\
                            FirstDerivShimCtrl.Init ub d)
      (SensorWithDelay.Sense "v" "Vmax" "Vmin" "a" d //\\
                             FirstDerivShimCtrl.Ctrl ub d)
      FirstDerivShimCtrl.world TRUE d.

Ltac sys_apply_with_weaken H :=
  eapply imp_trans; [ | apply H ];
  try (charge_intros; eapply Sys_weaken;
       try solve [ apply all_in_dec_ok ; reflexivity
                 | apply imp_id
                 | reflexivity ]).

Require Import Coq.Classes.RelationClasses.
Require Import RIneq.
Instance Reflexive_Rge : Reflexive Rge.
Proof.
  red. intro. apply Req_ge. reflexivity.
Qed.

Theorem ctrl_sense_delay_safe : forall ub d,
  |-- CtrlSenseDelaySys ub d -->> []"v" <= ub.
Proof.
  intros ub d.
  apply imp_trans with
  (F2:=[]("v" <= ub //\\ SensorWithDelay.SenseSafe "v" "Vmax" "Vmin")).
  - apply compose_discrete.
    + sys_apply_with_weaken SensorWithDelay.sense_safe;
      reflexivity.
    + sys_apply_with_weaken FirstDerivShimCtrl.ctrl_safe.
      tlaSplit; tlaAssume || solve_linear.
  - apply always_imp. charge_tauto.
Grab Existential Variables.
exact TRUE.
exact TRUE.
Qed.

Definition CtrlSenseErrorSys ub d err :=
  Sys ("a"::nil)%list ("v"::"Vmax"::"Vmin"::nil)%list
      (SensorWithError.Init "v" "Vmax" "Vmin" //\\
                            FirstDerivShimCtrl.Init ub d)
      (FirstDerivShimCtrl.Ctrl ub d)
      FirstDerivShimCtrl.world (SensorWithError.Sense "v" "Vmax" "Vmin" err) d.

Theorem ctrl_sense_error_safe : forall ub d err,
  |-- CtrlSenseErrorSys ub d err -->> []"v" <= ub.
Proof.
  intros ub d err.
  apply imp_trans with
  (F2:=[]("v" <= ub //\\ SensorWithError.SenseSafe "v" "Vmax" "Vmin")).
  - apply compose_world.
    + (* apply SensorWithError.sense_safe.*)
      admit.
    + unfold InvariantUnder. solve_linear.
    + sys_apply_with_weaken FirstDerivShimCtrl.ctrl_safe.
      tlaSplit; tlaAssume || solve_linear.
  - apply always_imp. charge_tauto.
Qed.