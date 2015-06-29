Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import Examples.System.
Require Import Examples.SecondDerivShimCtrlToMiddle.
Require Import Examples.FirstDerivShimCtrl.
Require Import ChargeTactics.Lemmas.
Require Import TLA.DifferentialInduction.
Require Import Coq.Reals.R_sqrt.
Require Import Coq.Reals.Ratan.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Require Import BasicProofRules.
Require Import Coq.Lists.List.

Set Implicit Arguments.
Set Strict Implicit.

Module Type UpperLowerParams.
  Parameter ub : R.

  Parameter d : R.
  Axiom d_gt_0 : (d > 0)%R.

  Parameter amin : R.
  Axiom amin_lt_0 : (amin < 0)%R.

  Parameter ubv : R.
End UpperLowerParams.

Module UpperLower (P : UpperLowerParams).
  Module Params <: SecondDerivShimParams.
    Definition ub := P.ub.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin.
    Definition amin_lt_0 := P.amin_lt_0.
    Definition ubv := P.ubv.
  End Params.

  Module Monitor := SecondDerivShimCtrl Params.

  Let mirror :=
    (("y",--"y")::("v",--"v")::("a",--"a")::
     ("Y",--"Y")::("V",--"V")::nil).

  Definition SpecR :=
    SysCompose Monitor.SpecR
               (SysRename (to_RenameMap mirror)
                          (deriv_term_RenameList mirror)
                          Monitor.SpecR).

  Definition Safe :=
    "y" <= Params.ub //\\ --Params.ub <= "y".

  Lemma UpperLower_ok :
    []"v" <= Params.ubv //\\ []"v" >= --Params.ubv
    |-- SysD SpecR -->> []Safe.
  Proof.
    intros.
    pose proof P.amin_lt_0. pose proof P.d_gt_0.
    apply Compose.
    - apply SysSafe_rule. apply always_tauto.
      unfold Discr. simpl.
      unfold Monitor.Ctrl, Monitor.History, Max.
      simpl. restoreAbstraction.
      rewrite <- Rename_ok
        by (simpl; intuition; is_st_term_list);
        simpl rename_formula; unfold RenameMap_compose;
        simpl rename_term; restoreAbstraction.
      enable_ex_st.
      destruct (RIneq.Rge_dec (st "y") R0).
      { repeat match goal with
                 |- exists x, _ => eexists
               end. solve_linear. }
      { repeat match goal with
                 |- exists x, _ => eexists
               end.
        repeat split.
        { right. intros. apply RIneq.Rgt_ge in H1.
          contradiction. }
        { right. instantiate (1:=(-Params.amin)%R).
          solve_linear. }
        { reflexivity. } }
    - charge_intros. pose proof Monitor.ctrl_safe.
      unfold Monitor.Safe in *.
      charge_apply H1. charge_tauto.
    - charge_intros.
      apply lcut with (R:=[]--"y" <= Params.ub).
      { pose proof Monitor.ctrl_safe.
        unfold Monitor.Safe in *.
        apply (Proper_Rename (to_RenameMap mirror)
                             (to_RenameMap mirror)) in H1;
          [ | reflexivity ].
        rewrite Rename_impl in H1.
        rewrite <-
                (SysRename_sound
                   Monitor.SpecR
                   (to_RenameMap mirror)
                   (deriv_term_RenameList mirror)) in H1;
          try solve [is_st_term_list; tauto].
        { rewrite <- Rename_ok in H1 by is_st_term_list.
          rewrite <- Rename_ok in H1
                               by (is_st_term_list; tauto).
          simpl rename_formula in *.
          unfold ConstC. charge_apply H1. clear H1.
          charge_split.
          { tlaAssert ([]"v" >= -- (RealT Params.ubv));
            [ charge_tauto | ].
            apply forget_prem. apply always_imp.
            solve_linear. }
          { charge_tauto. } }
        { apply forget_prem. clear H1.
          rewrite <- Rename_ok by (is_st_term_list; tauto).
          enable_ex_st.
          repeat match goal with
                 |- exists x, _ => eexists
               end. solve_linear.
          right. instantiate (1:=(-Params.amin)%R).
          solve_linear. } }
      { apply forget_prem. apply always_imp. solve_linear. }
Qed.

End UpperLower.

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
  Module X <: UpperLowerParams.
    Definition ub := P.ub_X.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin.
    Definition amin_lt_0 := P.amin_lt_0.
    Definition ubv := P.ubv_X.
  End X.

  Module Y <: UpperLowerParams.
    Definition ub := P.ub_Y.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin :=
      (X.amin/Rtrigo1.tan (P.theta_max))%R.
    Theorem amin_lt_0 : (amin < 0)%R.
    Admitted.
    Definition ubv := P.ubv_Y.
  End Y.

  Module UpperLower_X := UpperLower X.
  Module UpperLower_Y := UpperLower Y.

  Let rename_y :=
    RenameListC (("A","Ay")::("V","Vy")::("Y","Y")::("y","y")::
                 ("v","vy")::("a","ay")::("Ymax","Ymax")::
                 ("Vmax","Vymax")::nil).
  Let rename_x :=
    RenameListC (("A","Ax")::("V","Vx")::("Y","X")::("y","x")::
                 ("v","vx")::("a","ax")::("Ymax","Xmax")::
                 ("Vmax","Vxmax")::nil).

  Definition SpecRectR :=
    SysCompose (SysRename (to_RenameMap rename_x)
                          (deriv_term_RenameList rename_x)
                          UpperLower_X.SpecR)
               (SysRename (to_RenameMap rename_y)
                          (deriv_term_RenameList rename_y)
                          UpperLower_Y.SpecR).

  Let rename_polar : list (Var*Term) :=
    ("ax","a"*sin("theta"))::("ay","a"*cos("theta"))::nil.

  Definition SpecPolarR :=
    SysRename (to_RenameMap rename_polar)
              (deriv_term_RenameList rename_polar)
              SpecRectR.

  Definition InputConstraint : Formula :=
    P.theta_min <= "theta" <= P.theta_max.

  Definition InputConstraintSysR : SysRec :=
    {| Init := InputConstraint;
       Prog := next InputConstraint;
       world := fun _ => TRUE;
       unch := nil;
       maxTime := P.d |}.

  Definition SpecPolarConstrainedR :=
    SysCompose SpecPolarR InputConstraintSysR.

  Module VX <: FirstDerivShimParams.
    Definition ub := P.ubv_X.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
  End VX.

  Module VY <: FirstDerivShimParams.
    Definition ub := P.ubv_Y.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
  End VY.

  Module VelX := FirstDerivShim VX.
  Module VelY := FirstDerivShim VY.

  Let mirror :=
    ("v",--"v")::("a",--"a")::nil.

  Definition SpecVelocityR_X :=
    SysCompose VelX.SpecR
               (SysRename (to_RenameMap mirror)
                          (deriv_term_RenameList mirror)
                          VelX.SpecR).

  Definition SpecVelocityR_Y :=
    SysCompose VelY.SpecR
               (SysRename (to_RenameMap mirror)
                          (deriv_term_RenameList mirror)
                          VelY.SpecR).

  Definition SpecVelocityR :=
    SysCompose (SysRename (to_RenameMap rename_x)
                          (deriv_term_RenameList rename_x)
                          SpecVelocityR_X)
               (SysRename (to_RenameMap rename_y)
                          (deriv_term_RenameList rename_y)
                          SpecVelocityR_Y).

  Definition SpecR :=
    SysCompose (SysRename (to_RenameMap rename_polar)
                          (deriv_term_RenameList rename_polar)
                          SpecVelocityR)
               SpecPolarConstrainedR.

  Lemma constraints_ok :
    |-- SysD SpecPolarConstrainedR -->> SysD SpecPolarR.
  Proof.
    pose proof P.theta_min_lt_theta_max.
    charge_intros.
    tlaAssert ltrue;
      [ charge_tauto | charge_intros; rewrite landC ].
    apply ComposeRefine.
    apply SysSafe_rule. apply always_tauto.
    unfold Discr. simpl. restoreAbstraction.
    rewrite <- Rename_ok
      by (simpl; intuition; is_st_term_list);
      simpl rename_formula; unfold RenameMap_compose;
      simpl rename_term; restoreAbstraction.
    setoid_rewrite <- lor_right2.
    enable_ex_st.
    eexists.
    exists P.theta_max.
    repeat match goal with
             |- exists x, _ => eexists
           end. solve_linear.
    instantiate
      (1:=(- sqrt (X.amin*X.amin + Y.amin*Y.amin))%R).
    { unfold Y.amin. admit. }
    { unfold Y.amin. admit. }
    { unfold Y.amin. admit. }
    { unfold Y.amin. admit. }
  Qed.

    Lemma rect_to_polar :
    |-- SysD SpecPolarR -->>
        Rename (to_RenameMap rename_polar) (SysD SpecRectR).
    Proof.
      unfold SpecPolarR, SpecRectR.
      rewrite <- SysRename_sound.
      { charge_tauto. }
      { tlaIntuition; is_st_term_list. }
      { apply deriv_term_list; reflexivity. }
      { reflexivity. }
      { apply forget_prem. unfold Discr. simpl.
        restoreAbstraction.
        rewrite <- Rename_ok
          by (simpl; intuition; is_st_term_list);
          simpl rename_formula; unfold RenameMap_compose;
          simpl rename_term; restoreAbstraction.
        setoid_rewrite <- lor_right2.
        enable_ex_st.
        repeat match goal with
                 |- exists x, _ => eexists
               end. solve_linear.
        instantiate (2:=sqrt (X.amin*X.amin + Y.amin*Y.amin)).
        instantiate (1:=atan (Y.amin/X.amin)).
        rewrite ArithFacts.sin_atan. admit.
        rewrite ArithFacts.sin_atan. admit.
        rewrite ArithFacts.cos_atan. admit.
        rewrite ArithFacts.cos_atan. admit. }
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
        simpl. restoreAbstraction.
        unfold UpperLower_Y.Monitor.Ctrl,
        UpperLower_Y.Monitor.History, 
        UpperLower_X.Monitor.Ctrl,
        UpperLower_X.Monitor.History, Max, Discr.
        simpl. restoreAbstraction.
        rewrite <- Rename_ok by
            (simpl; intuition; is_st_term_list).
        simpl rename_formula. restoreAbstraction.
        rewrite <- Rename_ok by
            (simpl; intuition; is_st_term_list).
        simpl rename_formula. restoreAbstraction.
        unfold RenameMap_compose. simpl.
        restoreAbstraction.
        setoid_rewrite <- lor_right2.
        enable_ex_st.
        destruct (RIneq.Rgt_dec (st "x") R0);
        destruct (RIneq.Rgt_dec (st "y") R0).
        { repeat match goal with
                 | |- exists x, _ => eexists
                 end.
          solve_linear. }
        { repeat match goal with
                 | |- exists x, _ => eexists
                 end.
          solve_linear.
          instantiate (1:=(-UpperLower_Y.Params.amin)%R).
          solve_linear. }
        { repeat match goal with
                 | |- exists x, _ => eexists
                 end.
          solve_linear.
          instantiate (1:=(-UpperLower_X.Params.amin)%R).
          solve_linear. }
        { repeat match goal with
                 | |- exists x, _ => eexists
                 end.
          solve_linear.
          instantiate (1:=(-UpperLower_X.Params.amin)%R).
          solve_linear.
          instantiate (1:=(-UpperLower_Y.Params.amin)%R).
          solve_linear. } }
    { charge_intros.
      rewrite <- Rename_Always.
      unfold rename_x.
      rewrite SysRename_sound.
      { pose proof UpperLower_X.UpperLower_ok.
        apply (Proper_Rename (to_RenameMap rename_x)
                             (to_RenameMap rename_x))
          in H.
        rewrite Rename_impl in H. unfold rename_x in *.
        charge_apply H.
        { charge_split.
          { rewrite landC. tlaRevert.
            apply forget_prem.
            rewrite <- Rename_ok by (is_st_term_list; tauto).
            simpl rename_formula. restoreAbstraction.
            repeat rewrite Always_and. apply always_imp.
            clear H. solve_linear. }
          { charge_tauto. } }
        { reflexivity. } }
      { simpl; intuition; is_st_term_list. }
      { simpl; intuition; is_st_term_list. }
      { simpl; intuition; is_st_term_list. }
      { apply forget_prem.
        rewrite <- Rename_ok
          by (simpl; intuition; is_st_term_list).
        simpl rename_formula. restoreAbstraction.
        enable_ex_st.
        destruct (RIneq.Rgt_dec (st "x") R0).
        { repeat match goal with
                 | |- exists x, _ => eexists
                 end.
          solve_linear. }
        { repeat match goal with
                 | |- exists x, _ => eexists
                 end.
          solve_linear.
          instantiate (1:=(-UpperLower_X.Params.amin)%R).
          solve_linear. } } }
    { charge_intros.
      repeat rewrite <- Rename_Always.
      unfold rename_y.
      rewrite SysRename_sound.
      { pose proof UpperLower_Y.UpperLower_ok.
        apply (Proper_Rename (to_RenameMap rename_y)
                             (to_RenameMap rename_y))
          in H.
        rewrite Rename_impl in H. unfold rename_y in *.
        charge_apply H.
        { charge_split.
          { tlaAssert
              ((([]"vx" <= P.ubv_X //\\
                 []"vx" >= -- (P.ubv_X) //\\
                 []"vy" <= P.ubv_Y //\\
                 []"vy" >= -- (P.ubv_Y))));
            [ charge_tauto | ].
            apply forget_prem.
            rewrite <- Rename_ok by (is_st_term_list; tauto).
            simpl rename_formula. restoreAbstraction.
            repeat rewrite Always_and. apply always_imp.
            clear H. solve_linear. }
          { charge_tauto. } }
        { reflexivity. } }
      { simpl; intuition; is_st_term_list. }
      { simpl; intuition; is_st_term_list. }
      { simpl; intuition; is_st_term_list. }
      { apply forget_prem.
        rewrite <- Rename_ok
          by (simpl; intuition; is_st_term_list).
        simpl rename_formula. restoreAbstraction.
        enable_ex_st.
        destruct (RIneq.Rgt_dec (st "y") R0).
        { repeat match goal with
                 | |- exists x, _ => eexists
                 end.
          solve_linear. }
        { repeat match goal with
                 | |- exists x, _ => eexists
                 end.
          solve_linear.
          instantiate (1:=(-UpperLower_Y.Params.amin)%R).
          solve_linear. } } }
  Qed.

  Lemma box_safe_under_vel_bounds :
    []"vx" <= P.ubv_X //\\ []"vx" >= --P.ubv_X //\\
    []"vy" <= P.ubv_Y //\\  []"vy" >= --P.ubv_Y
    |-- SysD SpecPolarConstrainedR -->>
        [](--P.ub_X <= "x" <= P.ub_X //\\
           --P.ub_Y <= "y" <= P.ub_Y).
  Proof.
    charge_intros.
    pose proof rect_safe.
    rewrite <- Rename_ok
      in H by (simpl; intuition; is_st_term_list).
    rewrite <- Rename_ok
      in H by (simpl; intuition; is_st_term_list).
    simpl rename_formula in H. restoreAbstraction.
    match type of H with
    | _ |-- _ -->> ?C => tlaAssert C
    end.
    { apply (Proper_Rename (to_RenameMap rename_polar)
                           (to_RenameMap rename_polar))
        in H; [ | reflexivity ].
      rewrite <- Rename_ok
        in H by (simpl; intuition; is_st_term_list).
      rewrite Rename_impl in H.
      rewrite <- (Rename_ok (Always _))
        in H by (simpl; intuition; is_st_term_list).
      simpl rename_formula in H. restoreAbstraction.
      unfold ConstC, VarC in *.
      charge_apply H. clear H.
      charge_split; [ charge_tauto | ].
      pose proof rect_to_polar.
      charge_apply H. clear H.
      pose proof constraints_ok.
      charge_apply H. charge_tauto. }
    { apply forget_prem. apply always_imp.
      unfold UpperLower_X.Params.ub, UpperLower_Y.Params.ub.
      unfold ConstC, VarC.
      clear H. solve_linear. }
  Qed.

  Lemma velocity_safe :
    |-- SysD SpecVelocityR -->>
        [](("vx" <= VX.ub //\\ -- ("vx") <= VX.ub) //\\
            "vy" <= VY.ub //\\ -- ("vy") <= VY.ub).
  Proof.
    apply Compose.
    - admit.
    - unfold SpecVelocityR_X.
      rewrite SysCompose_SysRename. apply Compose.
      + admit.
      + pose proof VelX.ctrl_safe.
        apply (Proper_Rename (to_RenameMap rename_x)
                             (to_RenameMap rename_x))
        in H; [ | reflexivity ].
        rewrite Rename_True in H.
        rewrite Rename_impl in H.
        rewrite <- (Rename_ok (Always _))
          in H by (simpl; intuition; is_st_term_list).
        simpl rename_formula in *.
        unfold VarC, ConstC.
        charge_intros. charge_apply H.
        rewrite SysRename_sound;
          try solve [is_st_term_list; tauto].
        { unfold VelX.Spec. restoreAbstraction.
          charge_tauto. }
        { apply forget_prem. clear H.
          rewrite <- Rename_ok
            by (simpl; intuition; is_st_term_list).
          simpl rename_formula. restoreAbstraction.
          enable_ex_st.
          repeat match goal with
                 | |- exists x, _ => eexists
                 end.
          solve_linear. }
      + pose proof VelX.ctrl_safe.
        apply (Proper_Rename (to_RenameMap mirror)
                             (to_RenameMap mirror))
        in H; [ | reflexivity ].
        rewrite Rename_True in H.
        rewrite Rename_impl in H.
        rewrite <- (Rename_ok (Always _))
          in H by (simpl; intuition; is_st_term_list).
        simpl rename_formula in *.
        apply (Proper_Rename (to_RenameMap rename_x)
                             (to_RenameMap rename_x))
        in H; [ | reflexivity ].
        rewrite Rename_True in H.
        rewrite Rename_impl in H.
        rewrite <- (Rename_ok (Always _))
          in H by (simpl; intuition; is_st_term_list).
        simpl rename_formula in *.
        unfold VarC, ConstC.
        charge_intros. charge_apply H.
        rewrite SysRename_sound.
        { rewrite SysRename_sound.
          { restoreAbstraction. charge_tauto. }
          { simpl; intuition; is_st_term_list. }
          { simpl; intuition; is_st_term_list. }
          { simpl; intuition; is_st_term_list. }
          { apply forget_prem. clear H.
            rewrite <- Rename_ok
              by (simpl; intuition; is_st_term_list).
            simpl rename_formula. restoreAbstraction.
            enable_ex_st.
            repeat match goal with
                   | |- exists x, _ => eexists
                   end.
            solve_linear. } }
        { simpl; intuition; is_st_term_list. }
        { simpl; intuition; is_st_term_list. }
        { simpl; intuition; is_st_term_list. }
        { apply forget_prem. clear H.
          rewrite <- Rename_ok
            by (simpl; intuition; is_st_term_list).
          simpl rename_formula. restoreAbstraction.
          enable_ex_st.
          repeat match goal with
                 | |- exists x, _ => eexists
                 end.
          solve_linear. }
    - unfold SpecVelocityR_Y.
      rewrite SysCompose_SysRename. apply Compose.
      + admit.
      + pose proof VelY.ctrl_safe.
        apply (Proper_Rename (to_RenameMap rename_y)
                             (to_RenameMap rename_y))
        in H; [ | reflexivity ].
        rewrite Rename_True in H.
        rewrite Rename_impl in H.
        rewrite <- (Rename_ok (Always _))
          in H by (simpl; intuition; is_st_term_list).
        simpl rename_formula in *.
        unfold VarC, ConstC.
        charge_intros. charge_apply H.
        rewrite SysRename_sound;
          try solve [is_st_term_list; tauto].
        { unfold VelY.Spec. restoreAbstraction.
          charge_tauto. }
        { apply forget_prem. clear H.
          rewrite <- Rename_ok
            by (simpl; intuition; is_st_term_list).
          simpl rename_formula. restoreAbstraction.
          enable_ex_st.
          repeat match goal with
                 | |- exists x, _ => eexists
                 end.
          solve_linear. }
      + pose proof VelY.ctrl_safe.
        apply (Proper_Rename (to_RenameMap mirror)
                             (to_RenameMap mirror))
        in H; [ | reflexivity ].
        rewrite Rename_True in H.
        rewrite Rename_impl in H.
        rewrite <- (Rename_ok (Always _))
          in H by (simpl; intuition; is_st_term_list).
        simpl rename_formula in *.
        apply (Proper_Rename (to_RenameMap rename_y)
                             (to_RenameMap rename_y))
        in H; [ | reflexivity ].
        rewrite Rename_True in H.
        rewrite Rename_impl in H.
        rewrite <- (Rename_ok (Always _))
          in H by (simpl; intuition; is_st_term_list).
        simpl rename_formula in *.
        unfold VarC, ConstC.
        charge_intros. charge_apply H.
        rewrite SysRename_sound.
        { rewrite SysRename_sound.
          { restoreAbstraction. charge_tauto. }
          { simpl; intuition; is_st_term_list. }
          { simpl; intuition; is_st_term_list. }
          { simpl; intuition; is_st_term_list. }
          { apply forget_prem. clear H.
            rewrite <- Rename_ok
              by (simpl; intuition; is_st_term_list).
            simpl rename_formula. restoreAbstraction.
            enable_ex_st.
            repeat match goal with
                   | |- exists x, _ => eexists
                   end.
            solve_linear. } }
        { simpl; intuition; is_st_term_list. }
        { simpl; intuition; is_st_term_list. }
        { simpl; intuition; is_st_term_list. }
        { apply forget_prem. clear H.
          rewrite <- Rename_ok
            by (simpl; intuition; is_st_term_list).
          simpl rename_formula. restoreAbstraction.
          enable_ex_st.
          repeat match goal with
                 | |- exists x, _ => eexists
                 end.
          solve_linear. }
  Qed.

Axiom amin_ubv_X : (-P.amin*P.d <= P.ubv_X)%R.
Axiom amin_ubv_Y : (-P.amin*P.d <= P.ubv_Y)%R.

  Theorem box_safe :
    |-- SysD SpecR -->>
        [](--P.ub_X <= "x" <= P.ub_X //\\
           --P.ub_Y <= "y" <= P.ub_Y).
  Proof.
    charge_intros.
    tlaAssert
      ([]((("vx" <= VX.ub //\\ --"vx" <= VX.ub) //\\
           ("vy" <= VY.ub //\\ --"vy" <= VY.ub)) //\\
           (--P.ub_X <= "x" <= P.ub_X //\\
            --P.ub_Y <= "y" <= P.ub_Y))).
    { apply lrevert. apply Compose.
      - apply SysSafe_rule. apply always_tauto.
        simpl. restoreAbstraction.
        rewrite <- Rename_ok
          by (simpl; intuition; is_st_term_list).
        simpl rename_formula. restoreAbstraction.
        rewrite <- Rename_ok
          by (simpl; intuition; is_st_term_list).
        simpl rename_formula.
        unfold RenameMap_compose.
        simpl rename_term. restoreAbstraction.
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
      - charge_intros. pose proof velocity_safe.
        apply (Proper_Rename (to_RenameMap rename_polar)
                             (to_RenameMap rename_polar))
        in H; [ | reflexivity ].
        rewrite Rename_True in H.
        rewrite Rename_impl in H.
        rewrite <- (Rename_ok (Always _))
          in H by (simpl; intuition; is_st_term_list).
        simpl rename_formula in *. restoreAbstraction.
        unfold VarC, ConstC in *.
        charge_apply H.
        rewrite SysRename_sound.
        { charge_tauto. }
        { simpl; intuition; is_st_term_list. }
        { simpl; intuition; is_st_term_list. }
        { simpl; intuition; is_st_term_list. }
        { admit. }
      - charge_intros.
        pose proof box_safe_under_vel_bounds.
        charge_apply H. unfold VX.ub, VY.ub.
        charge_split.
        + rewrite landC. tlaRevert. apply forget_prem.
          rewrite landtrueL. repeat rewrite Always_and.
          apply always_imp. clear H.
          solve_linear.
        + charge_tauto. }
    { apply forget_prem. apply always_imp.
      solve_linear. }
  Qed.
         
End Box.
