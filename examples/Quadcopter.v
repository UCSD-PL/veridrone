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
    forall D W I A B,
      is_st_formula A ->
      is_st_formula B ->
      |-- TimedPreserves delta I
          (Sys (D //\\ next B) W delta) ->
      |-- SysNeverStuck delta I
          (Sys (D //\\ next B) W delta) ->
      small_angle -|- A //\\ B ->
      disjoint_states (next A)
                      (Discr (D //\\ next B) delta) ->
      W_quad |-- W ->
      |-- TimedPreserves delta I (Quadcopter D) //\\
          SysNeverStuck delta I (Quadcopter D).
  Proof.
    intros. charge_split.
    { unfold Quadcopter, TimedPreserves, Preserves in *.
      charge_intros. charge_apply H1. charge_split.
      { destruct H3. apply next_st_formula_entails in H3.
        { rewrite H3. rewrite H5. rewrite next_And.
          etransitivity. 2:eapply Proper_Sys_lentails.
          { charge_assumption. }
          { charge_tauto. }
          { reflexivity. }
          { reflexivity. } }
        { tlaIntuition. }
        { tlaIntuition. } }
      { charge_assumption. } }
    { unfold Quadcopter, SysNeverStuck in *. charge_intros.
      destruct H3. apply next_st_formula_entails in H6.
      { rewrite <- H6. rewrite next_And.
        rewrite limplValid in H2. rewrite H2.
        repeat rewrite landA. unfold Sys.
        repeat (rewrite <- Enabled_and_push; [| intuition]).
        charge_split; [ charge_assumption | ].
        repeat rewrite <- Enabled_or. charge_cases.
        { charge_left. unfold Discr.
          charge_assert (Enabled
         (next A //\\ (D //\\ next B //\\
          "T" = 0 //\\ 0 <= ("T") ! <= delta))).
          { repeat rewrite landA.
            rewrite <- disjoint_state_enabled.
            { charge_split.
              { charge_clear. etransitivity.
                apply Enabled_small_angle.
                apply Proper_Enabled_lentails.
                apply next_st_formula_entails in H3.
                { rewrite next_And in H3. rewrite H3.
                  charge_tauto. }
                { intuition. }
                { intuition. } }
              { charge_assumption. } }
            { rewrite <- landA. auto. } }
          { charge_clear. charge_intros.
            apply Proper_Enabled_lentails. charge_tauto. } }
        { charge_right. rewrite <- quadcopter_evolve_enabled.
          charge_tauto. } }
      { intuition. }
      { intuition. } }
  Qed.

End quadcopter.