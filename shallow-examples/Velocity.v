Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rtrigo_def.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.micromega.Psatz.
Require Import ExtLib.Structures.Applicative.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import ChargeTactics.Tactics.
Require Import ChargeTactics.Lemmas.
Require Import SLogic.Logic.
Require Import SLogic.Instances.
Require Import SLogic.Continuous.
Require Import SLogic.ContinuousInstances.
Require Import SLogic.BoundingFunctions.
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
  Axiom delta_gt_0 : (delta > 0)%R.
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
    (*Sense //\\*) Monitor //\\ Output.

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

Lemma continuity_id :
  continuity id.
Proof.
  apply derivable_continuous; apply derivable_id.
Qed.

Lemma continuity_exp :
  continuity exp.
Proof.
  apply derivable_continuous; apply Ranalysis4.derivable_exp.
Qed.

(* TODO: move *)
(* Proves continuity facts of real-valued functions. *)
Ltac prove_continuity :=
  repeat first [ apply continuity_plus |
                 apply continuity_opp |
                 apply continuity_minus |
                 apply continuity_mult |
                 solve [apply continuity_const; congruence] |
                 apply continuity_scal |
                 apply continuity_inv |
                 apply continuity_div |
                 apply continuity_id |
                 apply continuity_exp |
                 apply Ranalysis4.Rcontinuity_abs ].

Lemma Rabs_involutive :
  forall r, Rabs (Rabs r) = Rabs r.
Proof.
  intros. apply Rabs_pos_eq; apply Rabs_pos.
Qed.          


  (* Is the monitor robust? *)
  Theorem monitor_robust :
    (* Do we need an initial condition? *)
    [][Next] |-- robust state ((*`Rabs dv `+ *)`Rabs da)
                              (`Rmax (v `- `ub) (`0))
                              t.
  Proof.
    unfold robust.
    apply lexistsR with (x:=fun x => delta * x).
    charge_split.
    { charge_clear. apply embedPropR. unfold K_fun.
      split.
      { prove_continuity. }
      { unfold strict_increasing_bound, Ranalysis1.id. split.
        { intros. pose proof delta_gt_0. psatz R. }
        { psatzl R. } } }
    { apply lexistsR
      with (x:=fun d t => Rabs d * exp (-t)).
      charge_split.
      { charge_clear. apply embedPropR. unfold KLD_fun.
        split.
        { unfold KL_fun. split.
          { unfold K_fun. split.
            { prove_continuity. }
            { split.
              { unfold strict_increasing_bound. intros.
                pose proof (Exp_prop.exp_pos (-t0)).
                repeat (rewrite Rabs_right;
                        [ | solve [psatzl R ] ]).
                psatz R. }
              { rewrite Rabs_R0. psatzl R. } } }
          { unfold L_fun. intros. split.
            { prove_continuity.
              apply continuity_comp with (f1:=Ropp) (f2:=exp);
                prove_continuity. }
            { split.
              { unfold decreasing_bound. intros.
                destruct H0. destruct H1.
                { pose proof
                       (Rpower.exp_increasing (-y) (-x)).
                  pose proof (Rabs_pos c).
                  assert (- y < - x) by psatzl R.
                  pose proof (Exp_prop.exp_pos (-y)).
                  intuition.
                  (* I don't understand
                     how this solves the goal. *) }
                { rewrite H1. intuition. } }
              { unfold limit_pos_inf. intros.
                admit. (* Need some limit lemmas. *) } } } }
        { intros. split.
          { rewrite RIneq.Ropp_0. rewrite exp_0.
            rewrite RIneq.Rmult_1_r.
            apply Rabs_pos_eq; assumption. }
          { rewrite RIneq.Ropp_plus_distr.
            rewrite Exp_prop.exp_plus. rewrite Rabs_mult.
            rewrite Rabs_involutive.
            rewrite Rabs_pos_eq with (x:=exp (-s));
              [ | left; apply Exp_prop.exp_pos ].
            psatzl R. } } }
      { apply lexistsR  with (x:=R0).
        charge_split.
        { charge_clear. apply embedPropR. psatzl R. }
        { admit. } } }
  Admitted.

End VelocityMonitor.