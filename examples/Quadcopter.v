Require Import Coq.Reals.Reals.
Require Import ExtLib.Tactics.
Require Import Logic.Logic.
Require Import Logic.ProofRules.
Require Import Inductively.
Require Import Examples.System.

Set Implicit Arguments.
Set Strict Implicit.

Local Open Scope string_scope.

Section quadcopter.
  Variable delta : R.
  Hypothesis delta_gt_0 : (delta > 0)%R.
  Variable gravity : R.
  Variable angle_min : R.
  Definition angle_max := (-angle_min)%R.

  Definition roll  : Var := "roll".
  Definition pitch : Var := "pitch".

  Local Open Scope HP_scope.

  Definition small_angle : StateFormula :=
           angle_min <= pitch <= angle_max
      //\\ angle_min <= roll <= angle_max.

  Definition W_quadcopter' : Evolution := fun st' =>
          st' "x" = "vx" //\\ st' "y" = "vy" //\\
          st' "z" = "vz"
     //\\ st' "vx" = "a" * cos(pitch) * sin(roll)
     //\\ st' "vy" = "a" * sin(pitch)
     //\\ st' "vz" = "a" * cos(pitch) * cos(roll) + gravity
     //\\ st' pitch = 0 //\\ st' roll = 0 //\\ st' "a" = 0.

  Definition W_quadcopter : Evolution :=
    (fun _  => small_angle) -->> W_quadcopter'.

  Lemma quadcopter_evolve_enabled' :
    |-- Enabled (World W_quadcopter').
  Admitted.

  Lemma quadcopter_quadcopter' :
    W_quadcopter' |-- W_quadcopter.
  Proof.
    charge_tauto.
  Qed.

  Lemma quadcopter_evolve_enabled :
    |-- Enabled (World W_quadcopter).
  Proof.
    rewrite <- quadcopter_quadcopter'.
    apply quadcopter_evolve_enabled'.
  Qed.
(*
Lemma land_forgetL :
  forall P Q,
    P //\\ Q |-- Q.
Proof. intros. charge_tauto. Qed.
Lemma land_forgetR :
  forall P Q,
    P //\\ Q |-- P.
Proof. intros. charge_tauto. Qed.
Lemma SysNeverStuck_Discr :
  forall d I D W,
    (d > 0)%R ->
    |-- SysNeverStuck d I (Sys D W d) ->
    I //\\ "T" = 0 |-- Enabled (0 <= "T"! <= d //\\ D).
Proof.
  intros. unfold SysNeverStuck in H0.
  charge_assert (Enabled (Sys D W d)).
  { charge_apply H0. solve_linear. }
  { clear H0. unfold Sys. charge_intros.
    rewrite <- EnabledLemmas.Enabled_and_push.
    { rewrite <- Enabled_or. charge_cases.
      { unfold Discr. charge_revert. charge_clear.
        charge_intros. charge_revert. charge_clear.
        charge_intros. apply Proper_Enabled_lentails.
        charge_tauto. }
      { charge_exfalso. breakAbstraction.
        intros. intuition. destruct H4. solve_linear. } }
    { tlaIntuition. } }
Qed.

  Lemma quadcopter_refine_neverstuck :
    forall I D W,
      |-- SysNeverStuck
          delta I (Sys (D //\\ next small_angle)
                 W delta) ->
      |-- SysNeverStuck delta I (Sys D W_quadcopter delta).
  Proof.
    intros. apply SysNeverStuck_Sys.
    { solve_linear. }
    { apply SysNeverStuck_Discr in H.
      { rewrite H. apply Proper_Enabled_lentails.
        charge_tauto. }
      { assumption. } }
    { rewrite <- quadcopter_evolve_enabled. charge_tauto. }
  Qed.

  Theorem quadcopter_refine :
    forall I D W,
      is_st_formula I ->
      |-- TimedPreserves delta I (Sys D W delta) ->
      |-- SysNeverStuck
          delta I (Sys (D //\\ next small_angle)
                 W delta) ->
      W_quadcopter' |-- W ->
          ((I //\\ small_angle) //\\ 0 <= "T" <= delta) //\\
          []System (D //\\ next small_angle)
                   W_quadcopter delta
      |-- []((I //\\ small_angle) //\\ 0 <= "T" <= delta).
  Proof.
    intros. apply Preserves_Inv_simple.
    { tlaIntuition. }
    { apply SafeAndReactive_TimedPreserves.
      unfold SafeAndReactive. charge_split.
      { unfold TimedPreserves, Preserves. charge_intros.
        do 2 rewrite next_And.
        rewrite landC with (Q:=next small_angle).
        repeat rewrite landA. charge_split.
        { unfold Sys. charge_cases.
          { charge_tauto. }
          { unfold World, mkEvolution.
            Check zero_deriv.
            eapply diff_ind with (Hyps:=ltrue).
            3:charge_assumption.
            { tlaIntuition. }
            { tlaIntuition. }
            { tlaIntuition. }
            { charge_tauto. }
            { charge_assumption. }
            { charge_tauto. }
            { unfold W_quadcopter, W_quadcopter', small_angle.
              simpl. restoreAbstraction.
              
              compute.
              try solve [tlaIntuition].
            { 
            eapply zero_deriv with (x:=pitch).
            { charge_assumption. }
            { unfold W_quadcopter. solve_linear.
        rewrite next_And. charge

etransitivity.
        { apply H0. }
        unfold TimedPreserves.
        SearchAbout Inductively.Preserves.
        apply Inductively.Preserves_entails.
        { tlaIntuition. }
        { tlaIntuition. }
        { 


  Lemma quadcopter_refine_preserves :
    forall I D W,
      |-- TimedPreserves delta I (Sys D W delta) ->
      |-- SysNeverStuck
          delta I (Sys (D //\\ next small_angle)
                 W delta) ->
      W_quadcopter' |-- W ->
      |-- TimedPreserves delta I (Sys D W_quadcopter delta).
  Proof.
    unfold TimedPreserves, Inductively.Preserves. intros.
    charge_intros. charge_apply H. charge_split.
    { unfold Sys. charge_split.
      { charge_tauto. }
      { charge_cases.
        { charge_tauto. }
        { rewrite <- H1.
    { charge_tauto. }

 

  Definition W_quadcopter_plane : Evolution :=
    fun st' =>
           st' "x" = "vx" //\\ st' "y" = "vy"
      //\\ st' "vx" = "a" * cos( "theta" )
      //\\ st' "vy" = "a" * sin( "theta" )
      //\\ st' "theta" = 0 //\\ st' "a" = 0.

  Definition W_quadcopter_vplane : Evolution :=
    fun st' =>
      -- max_angle <= pitch <= max_angle //\\
      -- max_angle <= "theta" <= max_angle -->>
           st' "x" = "vx" //\\ st' "z" = "vz"
      //\\ st' "vx" = "a" * sin( "theta" )
      //\\ st' "vz" = "a" * cos( "theta" ) + gravity
      //\\ st' "theta" = 0 //\\ st' "a" = 0.


  Theorem W_quadcopter_vplane_refinement
  : let A : Term := "a" * cos( pitch ) in
    let theta : Term := roll in
        Continuous W_quadcopter
    |-- Rename ({{ "a" ~> A
                 & "theta" ~> theta }})%rn
               (Continuous W_quadcopter_vplane).
  Proof.
    cbv zeta.
    intros.
    rewrite <- Rename_Continuous_deriv_term'.
    2: eapply deriv_term_list; reflexivity.
    eapply Proper_Continuous_entails.
    red. intros.
    charge_intros.
    rewrite <- Rename_ok by eauto with rw_rename.
    simpl. restoreAbstraction.
    unfold W_quadcopter.
    unfold small_angle.
    charge_intros.
    unfold roll.
    breakAbstraction. intros.
    forward_reason.
    repeat rewrite H4. simpl.
    repeat split; auto.
    rewrite H12.
    rewrite H10.
    rewrite_real_zeros. reflexivity.
  Qed.
*)
End quadcopter.