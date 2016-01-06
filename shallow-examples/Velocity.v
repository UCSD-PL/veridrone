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
Require Import SLogic.BasicProofRules.
Require Import SLogic.Continuous.
Require Import SLogic.ContinuousInstances.
Require Import SLogic.BoundingFunctions.
Require Import SLogic.RobustnessISS.
Require Import SLogic.LTLNotation.
Require Import SLogic.Tactics.
Require Import SLogic.Util.
Require Import SLogic.Arithmetic.

Local Open Scope R_scope.
Local Open Scope LTL_scope.

Record state : Type :=
  { v : R; (* Actual velocity *)
    v_sense : R; (* Velocity used by the monitor *)
    a : R; (* Actual acceleration *)
    dv : R; (* Disturbance from velocity sensor *)
    t : R; (* Time *)
    T : R (* Timer *)
  }.

Section VelocityMonitor.

  (* Time between executions of the monitor. *)
  Variable delta : R.
  Axiom delta_gt_0 : (delta > 0)%R.
  (* The monitor enforces an upper bound of 0. *)

  (* Monitor logic *)
  Definition Monitor : StateProp state :=
    a `* pure delta `+ v_sense `<= pure 0.

  (* Sensor error *)
  Definition Sense : StateProp state :=
    v_sense `= v `+ dv.

  (* Reset the timer when the discrete transition runs. *)
  Definition ResetTimer : StateProp state :=
    T `= t.

  (* Full discrete transition *)
  Definition Discr : ActionProp state :=
    (Sense //\\ Monitor //\\ ResetTimer)! //\\
    Unchanged (v :: t :: nil).

  (* Evolution predicate *)
  Definition w : SimpleDiffProp state (v :: a :: t :: nil) :=
    D v `= (fun _ => a) //\\ D a `= pure 0 //\\
    D t `= pure 1 //\\ (fun _ => t `- T `<= pure delta).

  (* Continuous transition *)
  Definition World : ActionProp state :=
    SimpleContinuous state w //\\
    Unchanged (dv :: nil).

  (* Full system transition *)
  Definition Next : ActionProp state :=
    Discr \\// World.

  Definition time_left : StateVal state R :=
    pure delta `- (t `- T).

  Definition IndInv : StateProp state :=
    v `+ a `* time_left `<= dv.

  Theorem next_robust :
    [][Next] |-- robust state (`Rmax (`-dv) `0)
                              (`Rmax v (`0))
                              t.
  Proof.
  Admitted.

  (* An attempt at a proof of Tabuada robustness. *)
  (*
  Theorem next_robust :
    [][Next] |-- robust state (`Rmax (`-dv) `0)
                              (`Rmax v (`0))
                              t.
  Proof.
    rewrite <- robust2_robust.
    apply robust2_no_texists.
    { admit. }
    { exists (fun d => 2*d).
      exists (fun d t => Rabs d * exp (-t/2)).
      exists 0.
      split; [ | split; [ | split ] ].
      { apply K_fun_scale; [ apply K_fun_id | psatzl R ]. }
      { apply KLD_fun_abs_exp. psatzl R. }
      { reflexivity. }
      { rewrite_focusT. eapply discrete_induction.
        { clear_not_always. charge_revert_all.
          charge_intros. repeat rewrite always_and.
          charge_assumption. }
        { (* Base case. *) admit. }
        { (* Inductive step. *)
          charge_clear. apply always_tauto. charge_intros.
          unfold Next. rewrite focusA_or.
          rewrite <- starts_or.
          repeat rewrite land_lor_distr_L.
          apply lorL.
          { rewrite next_starts_pre. reason_action_tac.
            destruct pre_st
              as [[d1 td1] [v1 v_sense1 a1 dv1 t1 T1]].
            destruct post_st
              as [[d2 td2] [v2 v_sense2 a2 dv2 t2 T2]].
            Local Transparent ILInsts.ILFun_Ops.
            Local Transparent ILInsts.ILPre_Ops.
            unfold focusA, Discr, Sense, Monitor,
            ResetTimer, Unchanged, acc_dist2,
            bounded2, pre, post, dist2, PreFun.compose,
            _liftn, focusS. simpl. intros.
            assert (Rabs d1 <= d2).
            { admit. }
            assert (d1 <= Rabs d1) by apply Rle_abs.
            intuition. subst. psatzl R. }
          { rewrite next_starts_pre. reason_action_tac.
            destruct pre_st
              as [[d1 td1] [v1 v_sense1 a1 dv1 t1 T1]].
            destruct post_st
              as [[d2 td2] [v2 v_sense2 a2 dv2 t2 T2]].
            Local Transparent ILInsts.ILFun_Ops.
            Local Transparent ILInsts.ILPre_Ops.
            unfold focusA, World, Unchanged, acc_dist2,
            bounded2, pre, post, dist2, PreFun.compose,
            _liftn, focusS. simpl. intros.
            assert (v2 = v1 + a1 * (t2 - t1)) by admit.
            assert (a2 = a1) by admit.
            decompose [and] H1. subst. clear H1 H4.
   *)


(**** Old Stuff ****)
(*
Record state : Type :=
  { v : R; (* Actual velocity *)
    v_sense : R; (* Velocity used by the monitor *)
    a : R; (* Actual acceleration *)
    a_output : R; (* Desired acceleration of the monitor *)
    dv : R; (* Disturbance from velocity sensor *)
    da : R; (* Disturbance from actuator error *)
    t : R; (* Time *)
    T : R (* Timer *)
  }.


Section VelocityMonitor.

  (* Time between executions of the monitor. *)
  Variable delta : R.
  Axiom delta_gt_0 : (delta > 0)%R.
  (* Upper bound that the monitor enforces. *)
  Variable ub : R.

  (* Monitor logic *)
  Definition Monitor : StateProp state :=
    a_output `* pure delta `+ v_sense `<= pure ub.

  (* Sensor error *)
  Definition Sense : StateProp state :=
    v_sense `= v `+ dv.

  (* Actuator error *)
  Definition Output : StateProp state :=
    a `= a_output `+ da.

  (* Reset the timer when the discrete transition runs. *)
  Definition ResetTimer : StateProp state :=
    T `= t.

  (* Full discrete transition *)
  Definition Discr : ActionProp state :=
    (Sense //\\ Monitor //\\ Output //\\ ResetTimer)! //\\
    Unchanged (v :: t :: nil).

  (* Evolution predicate *)
  Definition w : SimpleDiffProp state (v :: a :: t :: nil) :=
    D v `= (fun _ => a) //\\ D a `= pure 0 //\\
    D t `= pure 1 //\\ (fun _ => t `- T `<= pure delta).

  (* Continuous transition *)
  Definition World : ActionProp state :=
    SimpleContinuous state w //\\
    Unchanged (dv :: da :: nil).

  (* Full system transition *)
  Definition Next : ActionProp state :=
    Discr \\// World.

  (* Is the monitor robust? *)
  Theorem monitor_robust :
    (* Do we need an initial condition? *)
    [][Next] |-- robust state ((*`Rabs dv `+ *)`Rabs da)
                              (`Rmax (v `- `ub) (`0))
                              t.
  Proof.
    rewrite <- robust2_robust.
    apply robust2_no_texists.
    { admit. }
    { exists (fun x => delta * x). (* gamma *)
      exists (fun d t => Rabs d * exp (-t)). (* mu *)
      exists R0. (* rho *)
      split; [ | split; [ | split ] ].
      { split.
        { prove_continuity. }
        { unfold strict_increasing_bound, Ranalysis1.id.
          split.
          { intros. pose proof delta_gt_0. psatz R. }
          { psatzl R. } } }
      { split.
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
              apply continuity_comp with (f1:=Ropp)
                                           (f2:=exp);
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
          { intros. rewrite RIneq.Ropp_plus_distr.
            rewrite Exp_prop.exp_plus. rewrite Rabs_mult.
            rewrite Rabs_involutive.
            rewrite Rabs_pos_eq with (x:=exp (-s));
              [ | left; apply Exp_prop.exp_pos ].
            psatzl R. } } }
        { psatzl R. }
        { rewrite_focusT. eapply discrete_induction.
          { clear_not_always. charge_revert_all.
            charge_intros. repeat rewrite always_and.
            charge_assumption. }
          { (* Base case. *) admit. }
          { (* Inductive step. *) charge_clear.
            apply always_tauto. charge_intros.
            unfold Next. rewrite focusA_or.
            rewrite <- starts_or.
            repeat rewrite land_lor_distr_L.
            apply lorL.
            { (* Discrete transition *)
              rewrite next_starts_pre.
              reason_action_tac.
              destruct pre_st
                as [[d1 td1]
                      [v1 v_sense1 a1 a_output1
                          dv1 da1 t1 T1]].
              destruct post_st
                as [[d2 td2]
                      [v2 v_sense2 a2 a_output2
                          dv2 da2 t2 T2]].
              Local Transparent ILInsts.ILFun_Ops.
              Local Transparent ILInsts.ILPre_Ops.
              unfold focusA, Discr, Monitor, Output,
              ResetTimer, UnchangedDiscr, acc_dist2,
              bounded2, pre, post, dist2, PreFun.compose,
              _liftn. simpl. 
              intros.
              assert (Rabs d1 <= d2).
              { admit. }
              assert (d1 <= Rabs d1) by apply Rle_abs.
              intuition. subst. psatzl R. }
            { rewrite next_starts_pre.
              reason_action_tac.
              destruct pre_st
                as [[d1 td1]
                      [v1 v_sense1 a1 a_output1
                          dv1 da1 t1 T1]].
              destruct post_st
                as [[d2 td2]
                      [v2 v_sense2 a2 a_output2
                          dv2 da2 t2 T2]].
              Local Transparent ILInsts.ILFun_Ops.
              Local Transparent ILInsts.ILPre_Ops.
              unfold focusA, World, Monitor, Output,
              ResetTimer, UnchangedDiscr, acc_dist2,
              bounded2, pre, post, dist2, PreFun.compose,
              _liftn. simpl. intros.
              
            (* This is unprovable. The proof needs to be by
               induction. *) admit. }
          { admit. } } }
  Admitted.
*)
End VelocityMonitor.