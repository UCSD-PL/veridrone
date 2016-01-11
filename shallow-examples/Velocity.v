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
    Unchanged (dv :: v_sense :: T :: nil).

  (* Full system transition *)
  Definition Next : ActionProp state :=
    Discr \\// World.

  (* Inductive invariant *)
  Definition IndInv : StateProp state :=
    a `* (`delta `- (t `- T)) `<= `- (v `+ dv).

  (* Full system specification. *)
  Definition Spec : TraceProp state :=
    [!IndInv] //\\ [][Next].

  (* The following seems to be necessary for breaking the
     abstraction. It would be nice if we didn't need to do
     this. *)
  Local Transparent ILInsts.ILFun_Ops.
  Local Transparent ILInsts.ILPre_Ops.

  (* Proof that our inductive invariant is in fact
     an invariant. *)
  Lemma Spec_IndInv :
    Spec |-- [][!IndInv].
  Proof.
    eapply discrete_induction.
    { charge_assumption. }
    { charge_assumption. }
    { charge_clear. apply always_tauto.
      rewrite next_starts_pre. reason_action_tac.
      destruct pre_st as [v1 v_sense1 a1 dv1 t1 T1].
      destruct post_st as [v2 v_sense2 a2 dv2 t2 T2].
      unfold IndInv, Next, World, Discr, Monitor, Sense,
      Unchanged, ResetTimer, pre, post, _liftn.
      simpl. intros. destruct H0.
      { decompose [and] H0. clear H0. subst.
        psatzl R. }
      { decompose [and] H0. clear H0. subst.
        assert (v2 = v1 + a1 * (t2 - t1)) by admit.
        assert (a2 = a1) by admit.
        psatz R. } }
  Qed.

  (* Essentially states that the initial condition
     always holds. *)
  Lemma Spec_always :
    Spec |-- []Spec.
  Proof.
    unfold Spec. rewrite <- always_and. charge_split.
    { apply Spec_IndInv. }
    { rewrite always_idemp. charge_assumption. }
  Qed.

  (* Our bounding functions. *)
  Definition mu : R -> R -> R :=
    fun d t => Rabs d * exp (-t/delta).
  Definition gamma : R -> R := Ranalysis1.id.

  (* Spec satisfies [robust]. *)
  Lemma Spec_robust :
    Spec |-- robust state (`Rmax (`-dv) `0)
                          (`Rmax v `0)
                          t mu gamma.
  Proof.
    unfold Spec, robust.
    repeat charge_split.
    { apply embedPropR. apply KL_fun_abs_exp.
      pose proof delta_gt_0. apply RIneq.Rinv_0_lt_compat.
      psatzl R. }
    { apply embedPropR. apply K_inf_fun_id. }
    { exists_val_now OC_0. exists_val_now t_0.
      { charge_intros.
        charge_assert ([][!IndInv]).
        { rewrite Spec_IndInv. charge_assumption. }
        charge_intros. eapply discrete_induction.
        { clear_not_always. repeat rewrite always_and.
          charge_assumption. }
        { (* Base case *)
          reason_action_tac.
          destruct pre_st as [v1 v_sense1 a1 dv1 t1 T1].
          destruct post_st as [v2 v_sense2 a2 dv2 t2 T2].
          unfold IndInv, Monitor, Sense, ResetTimer,
          pre, _liftn, gamma, mu, id.
          simpl. intros. subst.
          rewrite RIneq.Rminus_diag_eq; [ | reflexivity ].
          rewrite RIneq.Ropp_0. unfold Rdiv.
          rewrite RIneq.Rmult_0_l. rewrite exp_0.
          rewrite RIneq.Rmult_1_r.
          rewrite Rabs_pos_eq; [ | apply Rmax_r ].
          rewrite <- Rmax_r in H3. psatzl R. }
        { (* Inductive step *)
          charge_clear. apply always_tauto. charge_intros.
          unfold Next. rewrite <- starts_or.
          repeat rewrite land_lor_distr_L. apply lorL.
          { (* Discrete transition *)
            repeat rewrite next_starts_pre.
            repeat rewrite starts_and.
            reason_action_tac.
            destruct pre_st as [v1 v_sense1 a1 dv1 t1 T1].
            destruct post_st as [v2 v_sense2 a2 dv2 t2 T2].
            unfold Discr, Sense, Monitor, ResetTimer,
            Unchanged, pre, post, _liftn, id. simpl. intros.
            intuition congruence. }
          { (* Continuous transition *)
            repeat rewrite next_starts_pre.
            repeat rewrite starts_and.
            reason_action_tac.
            destruct pre_st as [v1 v_sense1 a1 dv1 t1 T1].
            destruct post_st as [v2 v_sense2 a2 dv2 t2 T2].
            unfold IndInv, World, Unchanged,
            pre, post, _liftn, mu, gamma, id.
            simpl. intros.
            assert (v2 = v1 + a1 * (t2 - t1)) by admit.
            assert (a2 = a1) by admit.
            assert (t1 <= t2) by admit.
            assert (T1 <= t1) by admit.
            assert (t2 - T1 <= delta) by admit.
            decompose [and] H. subst.
            apply Rmax_case_strong; intros.
            { pose proof delta_gt_0.
              pose proof H8.
              rewrite <- Rmax_l in H8.
              rewrite <- Rmax_r in H6.
              assert (x <= v1 \/ v1 < x)
                as Hsgn by psatzl R.
              destruct Hsgn as [Hsgn | Hsgn].
              { rewrite Rmax_left in H5; [ | psatzl R ].
                assert (exp (-(t2 - t_0)/delta) =
                        exp (-(t1 - t_0)/delta)*
                        exp(-(t2 - t1)/delta))
                  as Hexp.
                { rewrite <- Exp_prop.exp_plus. f_equal.
                  z3_prove. }
                rewrite Hexp. clear Hexp.
                transitivity
                  ((v1 - x) * exp (- (t2-t1) / delta)
                   + x).
                { pose proof
                       (x_plus_1_le_exp (-(t2-t1)/delta)).
                  z3_prove. }
                { pose proof
                       (Exp_prop.exp_pos (-(t2-t1)/delta)).
                  psatz R. } }
              { transitivity x.
                { z3_prove. }
                { pose proof (Rabs_pos OC_0).
                  pose proof
                       (Exp_prop.exp_pos (-(t2-t_0)/delta)).
                  psatz R. } } }
            { rewrite <- Rmax_r in H8. rewrite <- H8.
              pose proof
                   (Exp_prop.exp_pos (-(t2-t_0)/delta)).
              pose proof (Rabs_pos OC_0).
              psatz R. } } } } }
  Qed.

  (* Our main robustness theorem. *)
  Theorem Spec_robust2 :
    Spec |-- robust2 state (`Rmax (`-dv) `0)
                          (`Rmax v `0)
                          t mu gamma.
  Proof.
    apply robust_robust2.
    { apply Spec_robust. }
    { apply Spec_always. }
  Qed.

  (* An attempt at a proof of Tabuada robustness. *)
  (*
  Definition time_left : StateVal state R :=
    pure delta `- (t `- T).

  Definition IndInv : StateProp state :=
    v `+ a `* time_left `<= dv.

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