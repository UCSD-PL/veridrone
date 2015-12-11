Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rbasic_fun.
Require Import ExtLib.Structures.Applicative.
Require Import Charge.Logics.ILogic.
Require Import SLogic.Logic.
Require Import SLogic.Instances.
Require Import SLogic.Continuous.
Require Import SLogic.ContinuousInstances.
Require Import SLogic.Robustness.
Require Import SLogic.LTLNotation.

Record state : Type :=
  { v : R; (* Actual velocity *)
    v_sense : R; (* Velocity used by the monitor *)
    a : R; (* Actual acceleration *)
    a_output : R; (* Desired acceleration of the monitor *)
    dv : R; (* Disturbance from velocity sensor *)
    da : R; (* Disturbance from actuator error *)
    t : R (* Time *)
  }.

Local Open Scope R_scope.
Local Open Scope LTL_scope.

Section VelocityMonitor.

  (* Time between executions of the monitor. *)
  Variable delta : R.
  (* Upper bound that the monitor enforces. *)
  Variable ub : R.

  (* Monitor logic *)
  Definition Monitor : ActionProp state :=
    a_output! `* pure delta `+ v_sense! `<= pure ub.

  (* Sensor error *)
  Definition Sense : ActionProp state :=
    v_sense! `= !v `+ !dv.

  (* Actuator error *)
  Definition Output : ActionProp state :=
    a! `= a_output! `+ !da.

  (* Full discrete transition *)
  Definition Discr : ActionProp state :=
    Sense //\\ Monitor //\\ Output.

  (* Evolution predicate *)
  Definition w : SimpleDiffProp state (v :: a :: nil) :=
    D v `= (fun _ => a) //\\ D a `= pure 0.

  (* Continuous transition *)
  Definition World : ActionProp state :=
    !dv `= pure 0 //\\ !da `= pure 0 //\\
    SimpleContinuous state w.

  (* Full system transition *)
  Definition Next : ActionProp state :=
    Discr \\// World.

  (* Is the monitor robust? *)
  Theorem monitor_robust :
    (* Do we need an initial condition? *)
    [][Next] |-- robust state (dv `+ da)
                              (`Rmax (v `- pure ub) (pure 0))
                              t.
  Proof.
  Admitted.

End VelocityMonitor.