Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import Examples.System.
Require Import Examples.UpperLowerSecond.
Require Import Examples.UpperLowerFirst.
Require Import ChargeTactics.Lemmas.
Require Import Coq.Reals.R_sqrt.
Require Import Coq.Reals.Ratan.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Require Import BasicProofRules.
Require Import Coq.Lists.List.

Set Implicit Arguments.
Set Strict Implicit.

Module Type BoxParams.
  Parameter ub_X : R.
  Parameter ub_Y : R.

  Parameter d : R.
  Axiom d_gt_0 : (d > 0)%R.

  Parameter amin : R.
  Axiom amin_lt_0 : (amin < 0)%R.

  Parameter ubv_X : R.
  Parameter ubv_Y : R.

  Parameter theta_min : R.
  Parameter theta_max : R.
  Axiom theta_min_lt_theta_max : (theta_min <= theta_max)%R.
  Axiom theta_max_bound : (0 < theta_max < Rtrigo1.PI)%R.
End BoxParams.

Module Box (P : BoxParams).
  Module X <: UpperLowerSecondParams.
    Definition ub := P.ub_X.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin.
    Definition amin_lt_0 := P.amin_lt_0.
    Definition ubv := P.ubv_X.
  End X.

  Module Y <: UpperLowerSecondParams.
    Definition ub := P.ub_Y.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin :=
      (X.amin/Rtrigo1.tan (P.theta_max))%R.
    Theorem amin_lt_0 : (amin < 0)%R.
    Admitted.
    Definition ubv := P.ubv_Y.
  End Y.

  Module UpperLower_X := UpperLowerSecond X.
  Module UpperLower_Y := UpperLowerSecond Y.

  Let rename_y :=
    RenameListC (("A","Ay")::("V","Vy")::("Y","Y")::("y","y")::
                 ("v","vy")::("a","ay")::("Ymax","Ymax")::
                 ("Vmax","Vymax")::nil).
  Let rename_x :=
    RenameListC (("A","Ax")::("V","Vx")::("Y","X")::("y","x")::
                 ("v","vx")::("a","ax")::("Ymax","Xmax")::
                 ("Vmax","Vxmax")::nil).

  Definition UpperLower_X_SpecR :
    { x : SysRec &
          SysD x |-- Rename (to_RenameMap rename_x)
                            (SysD UpperLower_X.SpecR) }.
  Proof.
    discharge_Sys_rename_formula.
    apply forget_prem.
    rewrite <- Rename_ok by is_st_term_list.
    enable_ex_st.
    pose proof UpperLower_X.Params.amin_lt_0.
    destruct (RIneq.Rgt_dec (st "x") R0).
    { smart_repeat_eexists; solve_linear. }
    { smart_repeat_eexists; solve_linear.
      instantiate (1:=(-UpperLower_X.Params.amin)%R).
      unfold UpperLower_X.Params.amin.
      solve_linear. }
  Defined.

  Definition UpperLower_Y_SpecR :
    { x : SysRec &
          SysD x |-- Rename (to_RenameMap rename_y)
                            (SysD UpperLower_Y.SpecR) }.
  Proof.
    discharge_Sys_rename_formula.
    apply forget_prem.
    rewrite <- Rename_ok by is_st_term_list.
    enable_ex_st.
    pose proof UpperLower_Y.Params.amin_lt_0.
    destruct (RIneq.Rgt_dec (st "y") R0).
    { smart_repeat_eexists; solve_linear. }
    { smart_repeat_eexists; solve_linear.
      instantiate (1:=(-UpperLower_Y.Params.amin)%R).
      unfold UpperLower_Y.Params.amin.
      solve_linear. }
  Defined.

  Definition SpecRectR :=
    SysCompose (projT1 UpperLower_X_SpecR)
               (projT1 UpperLower_Y_SpecR).

  Let rename_polar : list (Var*Term) :=
    ("ax","a"*sin("theta"))::("ay","a"*cos("theta"))::nil.

  Definition SpecPolarR :
    { x : SysRec &
          SysD x |-- Rename (to_RenameMap rename_polar)
                            (SysD SpecRectR) }.
  Proof.
    discharge_Sys_rename_formula.
    apply forget_prem.
    rewrite <- Rename_ok by is_st_term_list.
    simpl; restoreAbstraction.
    setoid_rewrite <- lor_right2.
    enable_ex_st.
    admit.
    (* smart_repeat_eexists.
    solve_linear.
    instantiate (2:=sqrt (X.amin*X.amin + Y.amin*Y.amin)).
    instantiate (1:=atan (Y.amin/X.amin)).
    rewrite ArithFacts.sin_atan. admit.
    rewrite ArithFacts.sin_atan. admit.
    rewrite ArithFacts.cos_atan. admit.
    rewrite ArithFacts.cos_atan. admit.*)
  Defined.

  Definition InputConstraint : Formula :=
    P.theta_min <= "theta" <= P.theta_max.

  Definition InputConstraintSysR : SysRec :=
    {| Init := InputConstraint;
       Prog := next InputConstraint;
       world := fun _ => TRUE;
       unch := nil;
       maxTime := P.d |}.

  Definition SpecPolarConstrainedR :=
    SysCompose (projT1 SpecPolarR) InputConstraintSysR.

  Module VX <: UpperLowerFirstParams.
    Definition ub := P.ubv_X.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
  End VX.

  Module VY <: UpperLowerFirstParams.
    Definition ub := P.ubv_Y.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
  End VY.

  Module VelX := UpperLowerFirst VX.
  Module VelY := UpperLowerFirst VY.

  Definition SpecVelocityR_X :
    { x : SysRec &
          SysD x |-- Rename (to_RenameMap rename_x)
                            (SysD VelX.SpecR) }.
  Proof.
    discharge_Sys_rename_formula.
    apply forget_prem.
    rewrite <- Rename_ok by is_st_term_list.
    enable_ex_st. smart_repeat_eexists.
    solve_linear.
  Defined.

  Definition SpecVelocityR_Y :
    { x : SysRec &
          SysD x |-- Rename (to_RenameMap rename_y)
                            (SysD VelY.SpecR) }.
  Proof.
    discharge_Sys_rename_formula.
    apply forget_prem.
    rewrite <- Rename_ok by is_st_term_list.
    enable_ex_st. smart_repeat_eexists.
    solve_linear.
  Defined.

  Definition SpecVelocityR :=
    SysCompose (projT1 SpecVelocityR_X)
               (projT1 SpecVelocityR_Y).

  Definition SpecVelocityR_Polar :
    { x : SysRec &
          SysD x |-- Rename (to_RenameMap rename_polar)
                            (SysD SpecVelocityR) }.
  Proof.
    discharge_Sys_rename_formula.
    apply forget_prem.
    rewrite <- Rename_ok by is_st_term_list.
    enable_ex_st.
    (* Trig stuff. *)
    admit.
  Defined.

  Definition SpecR :=
    SysCompose (projT1 SpecVelocityR_Polar)
               SpecPolarConstrainedR.

  Lemma constraints_ok :
    (** generalize with respect to the underlying system and add a premise
     ** that says something about the arctan(x/y) is bounded by some theta.
     **)
    SysD SpecPolarConstrainedR |-- SysD (projT1 SpecPolarR).
  Proof.
    tlaAssert ltrue;
      [ charge_tauto | charge_intros; rewrite landC ].
    apply ComposeRefine.
    apply SysSafe_rule. apply always_tauto.
    unfold Discr. simpl; restoreAbstraction.
    setoid_rewrite <- lor_right2.
    pose proof P.theta_min_lt_theta_max.
    enable_ex_st.
    admit.
    (*eexists.
    exists P.theta_max. smart_repeat_eexists.
    solve_linear.
    instantiate
      (1:=(- sqrt (X.amin*X.amin + Y.amin*Y.amin))%R).
    { unfold Y.amin. admit. }
    { unfold Y.amin. admit. }
    { unfold Y.amin. admit. }
    { unfold Y.amin. admit. }*)
  Qed.

  Lemma rect_to_polar :
    (** this should generalize without any additional premises
     ** it might require enabledness
     **)
    SysD (projT1 SpecPolarR)
    |-- Rename (to_RenameMap rename_polar) (SysD SpecRectR).
  Proof.
    apply (projT2 SpecPolarR).
  Qed.

  Lemma rect_safe
    : []"vx" <= P.ubv_X //\\ []"vx" >= --P.ubv_X //\\
      []"vy" <= P.ubv_Y //\\  []"vy" >= --P.ubv_Y
      |-- SysD SpecRectR -->>
          [](Rename (to_RenameMap rename_x)
                    UpperLower_X.Safe //\\
             Rename (to_RenameMap rename_y)
                    UpperLower_Y.Safe).
  Proof.
    apply Compose.
    { apply SysSafe_rule; apply always_tauto.
      unfold Discr. simpl. restoreAbstraction.
      setoid_rewrite <- lor_right2.
      enable_ex_st.
      pose proof UpperLower_X.Params.amin_lt_0.
      pose proof UpperLower_Y.Params.amin_lt_0.
      destruct (RIneq.Rgt_dec (st "x") R0);
        destruct (RIneq.Rgt_dec (st "y") R0).
      { smart_repeat_eexists; solve_linear. }
      { do 6 eexists. exists (-UpperLower_Y.Params.amin)%R.
        smart_repeat_eexists. solve_linear. }
      { do 11 eexists. exists (-UpperLower_X.Params.amin)%R.
        smart_repeat_eexists. solve_linear. }
      { do 6 eexists. exists (-UpperLower_Y.Params.amin)%R.
        do 4 eexists. exists (-UpperLower_X.Params.amin)%R.
        smart_repeat_eexists. solve_linear. } }
    { charge_intros. pose proof UpperLower_X.UpperLower_ok.
      apply (Proper_Rename (to_RenameMap rename_x)
                           (to_RenameMap rename_x))
        in H; [ | reflexivity ].
      rewrite Rename_impl in H. rewrite Rename_Always in H.
      charge_apply H. clear.
      { charge_split.
        { rewrite landC. tlaRevert.
          apply forget_prem.
          rewrite <- Rename_ok by rw_side_condition.
          simpl rename_formula. restoreAbstraction.
          repeat rewrite Always_and. apply always_imp.
          solve_linear. }
        { pose proof (projT2 UpperLower_X_SpecR).
          cbv beta in H. charge_tauto. } } }
    { charge_intros. pose proof UpperLower_Y.UpperLower_ok.
      apply (Proper_Rename (to_RenameMap rename_y)
                           (to_RenameMap rename_y))
        in H; [ | reflexivity ].
      rewrite Rename_impl in H. rewrite Rename_Always in H.
      charge_apply H. clear.
      { charge_split.
        { rewrite landC. tlaRevert.
          apply forget_prem.
          repeat rewrite <- Rename_ok by rw_side_condition.
          simpl rename_formula. restoreAbstraction.
          repeat rewrite Always_and. apply always_imp.
          solve_linear. }
        { pose proof (projT2 UpperLower_Y_SpecR).
          cbv beta in H. charge_tauto. } } }
  Qed.

  Lemma box_safe_under_vel_bounds :
    []"vx" <= P.ubv_X //\\ []"vx" >= --P.ubv_X //\\
    []"vy" <= P.ubv_Y //\\  []"vy" >= --P.ubv_Y
    |-- SysD SpecPolarConstrainedR -->>
        [](--P.ub_X <= "x" <= P.ub_X //\\
           --P.ub_Y <= "y" <= P.ub_Y).
  Proof.
    charge_intros.
    rewrite constraints_ok.
    rewrite rect_to_polar.
    pose proof rect_safe.
    eapply Proper_Rename in H. 2: reflexivity.
    revert H. instantiate (1 := to_RenameMap rename_polar).
    intro.
    rewrite <- Rename_ok in H by rw_side_condition.
    tlaRevert.
    simpl rename_formula in H. restoreAbstraction.
    rewrite H; clear.
    rewrite Rename_impl.
    eapply trans_it.
    { reflexivity. }
    { rewrite <- Rename_ok by rw_side_condition.
      simpl; restoreAbstraction.
      tlaRevert. apply always_imp.
      solve_linear. }
  Qed.

  Lemma velocity_safe :
    |-- SysD SpecVelocityR -->>
        [](("vx" <= VX.ub //\\ -- ("vx") <= VX.ub) //\\
            "vy" <= VY.ub //\\ -- ("vy") <= VY.ub).
  Proof.
    apply Compose.
    - admit.
    - pose proof (projT2 SpecVelocityR_X). cbv beta in H.
      rewrite H. clear. pose proof VelX.UpperLower_ok.
      apply (Proper_Rename (to_RenameMap rename_x)
                           (to_RenameMap rename_x))
        in H; [ | reflexivity ].
      rewrite Rename_impl in H. rewrite Rename_True in H.
      apply landAdj in H. restoreAbstraction.
      rewrite landtrueL in H. rewrite H. clear.
      rewrite <- Rename_ok by rw_side_condition.
      apply always_imp. solve_linear.
    - pose proof (projT2 SpecVelocityR_Y). cbv beta in H.
      rewrite H. clear. pose proof VelY.UpperLower_ok.
      apply (Proper_Rename (to_RenameMap rename_y)
                           (to_RenameMap rename_y))
        in H; [ | reflexivity ].
      rewrite Rename_impl in H. rewrite Rename_True in H.
      apply landAdj in H. restoreAbstraction.
      rewrite landtrueL in H. rewrite H. clear.
      rewrite <- Rename_ok by rw_side_condition.
      apply always_imp. solve_linear.
  Qed.

Axiom amin_ubv_X : (-P.amin*P.d <= P.ubv_X)%R.
Axiom amin_ubv_Y : (-P.amin*P.d <= P.ubv_Y)%R.

  Theorem box_safe :
    |-- SysD SpecR -->>
        []((("vx" <= VX.ub //\\ --"vx" <= VX.ub) //\\
           ("vy" <= VY.ub //\\ --"vy" <= VY.ub)) //\\
           (--P.ub_X <= "x" <= P.ub_X //\\
            --P.ub_Y <= "y" <= P.ub_Y)).
  Proof.
    charge_intros.
    apply lrevert. apply Compose.
    - apply SysSafe_rule. apply always_tauto.
      simpl. restoreAbstraction.
      admit.
(*
        enable_ex_st.
        pose proof P.theta_min_lt_theta_max.
        pose proof P.amin_lt_0.
        pose proof amin_ubv_X.
        pose proof amin_ubv_Y.
        pose proof P.d_gt_0.
        destruct (RIneq.Rgt_dec (st "x") R0);
        destruct (RIneq.Rgt_dec (st "y") R0);
        destruct (RIneq.Rge_dec (st "vx") R0);
        destruct (RIneq.Rge_dec (st "vy") R0).
        { repeat match goal with
                 | |- exists x, _ => eexists
                 end.
          repeat split.
          left. instantiate
          solve_linear.
*)
    - charge_intros. pose proof (projT2 SpecVelocityR_Polar).
      cbv beta in H. rewrite H. clear.
      pose proof velocity_safe.
      apply (Proper_Rename (to_RenameMap rename_polar)
                           (to_RenameMap rename_polar))
        in H; [ | reflexivity ].
      rewrite Rename_True in H. rewrite Rename_impl in H.
      restoreAbstraction. apply landAdj in H.
      rewrite landtrueL in H. rewrite H. clear.
      rewrite <- Rename_ok by rw_side_condition.
      tlaRevert. apply always_imp. solve_linear.
    - charge_intros.
      pose proof box_safe_under_vel_bounds.
      charge_apply H. clear. unfold VX.ub, VY.ub.
      charge_split.
      + rewrite landC. tlaRevert. apply forget_prem.
        rewrite landtrueL. repeat rewrite Always_and.
        apply always_imp. solve_linear.
      + charge_tauto.
  Qed.

End Box.
