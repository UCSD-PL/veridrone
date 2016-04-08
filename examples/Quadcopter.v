Require Import Coq.Reals.Reals.
Require Import ExtLib.Tactics.
Require Import Logic.Logic.
Require Import Logic.ProofRules.
Require Import Logic.Inductively.
Require Import Logic.EnabledLemmas.
Require Import Logic.Tactics.
Require Import Examples.System.

Set Implicit Arguments.
Set Strict Implicit.

Local Open Scope string_scope.

Section quadcopter.
  Variable delta : R.
  Hypothesis delta_gt_0 : (delta > 0)%R.
  Variable gravity : R.
  Variable angle_min : R.
  Hypothesis angle_min_lt_0 : (angle_min < 0)%R.
  Definition angle_max := (-angle_min)%R.

  Local Open Scope HP_scope.

  Definition small_angle : StateFormula :=
           angle_min <= "pitch" <= angle_max
      //\\ angle_min <= "roll" <= angle_max
      //\\ 0 <= "A".

  Definition W_quad : Evolution := fun st' =>
          st' "x" = "vx" //\\ st' "y" = "vy" //\\
          st' "z" = "vz"
     //\\ st' "vx" = "A" * cos("pitch")*sin("roll")
     //\\ st' "vy" = --"A" * sin("pitch")
     //\\ st' "vz" = "A" * cos("pitch")*cos("roll") - gravity
     //\\ st' "pitch" = 0 //\\ st' "roll" = 0 //\\
          st' "A" = 0.

  Lemma quadcopter_evolve_enabled :
    |-- Enabled (World W_quad).
  Admitted.

  Definition Quadcopter (D : ActionFormula) :=
    Sys (D //\\ next small_angle) W_quad delta.

  Lemma Enabled_small_angle :
    |-- Enabled (next small_angle).
  Proof.
    enable_ex_st. unfold angle_max. exists R0. exists R0.
    exists R0. solve_linear.
  Qed.

  Theorem Quadcopter_refine :
    forall D W I,
      |-- TimedPreserves delta I (Sys D W delta) ->
      |-- SysNeverStuck delta I (Sys D W delta) ->
      D |-- next small_angle ->
      W_quad |-- W ->
      |-- TimedPreserves delta I (Quadcopter D) //\\
          SysNeverStuck delta I (Quadcopter D).
  Proof.
    intros.
    assert (D //\\ next small_angle -|- D)
      by (split; charge_tauto).
    charge_split.
    { unfold Quadcopter, TimedPreserves, Preserves in *.
      rewrite H3. charge_intros. charge_apply H. rewrite H2.
      charge_tauto. }
    { unfold Quadcopter, SysNeverStuck, Sys in *.
      charge_intros. rewrite limplValid in H0. rewrite H0.
      repeat (rewrite <- Enabled_and_push; [| intuition]).
      charge_split; [ charge_assumption | ].
      repeat rewrite <- Enabled_or. charge_cases.
      { rewrite H3. charge_tauto. }
      { charge_right. charge_clear.
        apply quadcopter_evolve_enabled. } }
  Qed.

End quadcopter.