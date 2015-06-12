Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import Examples.System.
Require Import Examples.SecondDerivShimCtrl.
Require Import ChargeTactics.Lemmas.
Require Import TLA.DifferentialInduction.
Require Import Coq.Reals.R_sqrt.
Require Import Coq.Reals.Ratan.

Set Implicit Arguments.
Set Strict Implicit.

Module Type CornerParams.
  Parameter ub_X : R.
  Parameter d : R.
  Axiom d_gt_0 : (d > 0)%R.

  Parameter amin_X : R.
  Axiom amin_lt_0_X : (amin_X < 0)%R.

  Parameter ub_Y : R.

  Parameter theta_min : R.
  Parameter theta_max : R.
  Axiom theta_min_lt_theta_max : (theta_min <= theta_max)%R.
  Axiom theta_max_bound : (0 < theta_max < Rtrigo1.PI)%R.
End CornerParams.

Module Corner (P : CornerParams).
  Module X <: SecondDerivShimParams.
    Definition ub := P.ub_X.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin_X.
    Definition amin_lt_0 := P.amin_lt_0_X.
  End X.

  Module Y <: SecondDerivShimParams.
    Definition ub := P.ub_Y.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin : R :=
      (X.amin/Rtrigo1.tan (P.theta_max))%R.
    Theorem amin_lt_0 : (amin < 0)%R.
    Admitted.
  End Y.

  Module SDSP_X := SecondDerivShimCtrl X.
  Module SDSP_Y := SecondDerivShimCtrl Y.

  Require Import Coq.Strings.String.
  Local Open Scope string_scope.

  Require Import BasicProofRules.
  Require Import Coq.Lists.List.

  Let rename_y :=
    RenameListC (("A","Ay")::("V","Vy")::("Y","Y")::("y","y")::
                 ("v","vy")::("a","ay")::("Ymax","Ymax")::
                 ("Vmax","Vymax")::nil).
  Let rename_x :=
    RenameListC (("A","Ax")::("V","Vx")::("Y","X")::("y","x")::
                 ("v","vx")::("a","ax")::("Ymax","Xmax")::
                 ("Vmax","Vxmax")::nil).

  Definition SpecRect :=
    SysCompose (SysRename (to_RenameMap rename_x)
                          (deriv_term_RenameList rename_x)
                          SDSP_X.SpecR)
               (SysRename (to_RenameMap rename_y)
                          (deriv_term_RenameList rename_y)
                          SDSP_Y.SpecR).

  Let rename_polar : list (Var*Term) :=
    ("ax","a"*sin("theta"))::("ay","a"*cos("theta"))::nil.

  Definition SpecPolar :=
    SysRename (to_RenameMap rename_polar)
              (deriv_term_RenameList rename_polar)
              SpecRect.

  Definition InputConstraint : Formula :=
    P.theta_min <= "theta" <= P.theta_max.

  Definition InputConstraintSys : SysRec :=
    {| Init := InputConstraint;
       Prog := next InputConstraint;
       world := fun _ => TRUE;
       unch := nil;
       maxTime := P.d |}.

  Definition SpecPolarConstrained :=
    SysCompose SpecPolar InputConstraintSys.

  Lemma constraints_ok :
    |-- SysD SpecPolarConstrained -->> SysD SpecPolar.
  Proof.
    charge_intros. apply ComposeRefine.
    apply SysSafe_rule. apply always_tauto.
    unfold Discr. simpl.
    unfold SDSP_X.Ctrl, SDSP_X.History,
    SDSP_Y.Ctrl, SDSP_Y.History, Max. simpl. restoreAbstraction.
    rewrite <- Rename_ok
      by (simpl; intuition; is_st_term_list);
      simpl rename_formula; unfold RenameMap_compose;
      simpl rename_term; restoreAbstraction.
    setoid_rewrite <- lor_right2.
    enable_ex_st.
    exists (Rbasic_fun.Rmin (Rbasic_fun.Rmin X.d Y.d) P.d).
    exists P.theta_max.
    repeat match goal with
             |- exists x, _ => eexists
           end. solve_linear.
    instantiate (1:=(- sqrt (X.amin*X.amin + Y.amin*Y.amin))%R).
    { unfold Y.amin. admit. }
    { unfold Y.amin. admit. }
    { apply P.theta_min_lt_theta_max. }
  Qed.

  Lemma rect_to_polar :
    |-- SysD SpecPolar -->>
        Rename (to_RenameMap rename_polar) (SysD SpecRect).
  Proof.
    unfold SpecPolar, SpecRect.
    rewrite <- SysRename_sound.
    { charge_tauto. }
    { tlaIntuition; is_st_term_list. }
    { apply deriv_term_list; reflexivity. }
    { reflexivity. }
    { apply forget_prem. unfold Discr. simpl.
      unfold SDSP_X.Ctrl, SDSP_X.History,
      SDSP_Y.Ctrl, SDSP_Y.History, Max. simpl. restoreAbstraction.
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
      rewrite sin_atan. admit.
      rewrite cos_atan. admit. }
  Qed.

  Lemma the_box_rect
  : |-- SysD SpecRect -->>
        [](Rename (to_RenameMap rename_x) SDSP_X.Safe //\\
           Rename (to_RenameMap rename_y) SDSP_Y.Safe).
  Proof.
    eapply Compose.
    { apply SysSafe_rule; apply always_tauto.
      unfold SDSP_X.SpecR, SDSP_X.Ctrl, SDSP_X.History,
             SDSP_Y.SpecR, SDSP_Y.Ctrl, SDSP_Y.History.
      simpl. restoreAbstraction.
      unfold Max, Discr.
      repeat rewrite <- Rename_ok by is_st_term_list.
(* TODO: We should be able to make this more efficient with a [cbv] 
      cbv beta iota zeta delta [ rename_formula rename_term find_term land lor limpl ILogicOps_Formula ltrue option_map find string_dec ].
*)
      Time simpl rename_formula; restoreAbstraction.
      unfold Discr.
      unfold X.d, Y.d.
      enable_ex_st.
      rewrite Rbasic_fun.Rmin_left by reflexivity.
      exists P.d.
      repeat match goal with
             | |- exists x, _ => eexists
             end.
      solve_linear. }
    { tlaIntro.
      rewrite <- Rename_Always.
      unfold rename_x.
      rewrite SysRename_sound.
      { eapply Proper_Rename.
        { reflexivity. }
        { pose proof SDSP_X.ctrl_safe.
          charge_apply H. unfold SDSP_X.Spec.
          charge_split; try charge_assumption. admit. } }
      { compute. tauto. }
      { intros. apply deriv_term_list; reflexivity. }
      { reflexivity. }
      { apply forget_prem. rewrite <- Rename_ok.
        simpl rename_formula. restoreAbstraction.
        enable_ex_st. repeat eexists. solve_linear.
        reflexivity. is_st_term_list. } }
    { apply forget_prem. tlaIntro.
      rewrite <- Rename_Always.
      unfold rename_y.
      rewrite SysRename_sound.
      { eapply Proper_Rename.
        { reflexivity. }
        { pose proof SDSP_Y.ctrl_safe.
          charge_apply H. unfold SDSP_Y.Spec.
          charge_split; try charge_assumption. admit. } }
      { compute. tauto. }
      { intros. apply deriv_term_list; reflexivity. }
      { reflexivity. }
      { apply forget_prem. rewrite <- Rename_ok.
        simpl rename_formula. restoreAbstraction.
        enable_ex_st. repeat eexists. solve_linear.
        reflexivity. is_st_term_list. } }
  Qed.

End Corner.