Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.ArithFacts.
Require Import TLA.EnabledLemmas.
Require Import TLA.DifferentialInduction.
Require Import Examples.System.
Require Import Examples.UpperLowerSecond.
Require Import Examples.UpperLowerFirst.
Require Import Examples.ParLang.
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
  Open Scope HP_scope.

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
                 ("Vmax","Vymax")::("T","Ty")::nil).
  Let rename_x :=
    RenameListC (("A","Ax")::("V","Vx")::("Y","X")::("y","x")::
                 ("v","vx")::("a","ax")::("Ymax","Xmax")::
                 ("Vmax","Vxmax")::("T","Tx")::nil).

  Lemma x_witness_function :
    exists f,
    forall xs,
      List.forallb
        (fun y => negb (List.existsb
                          (fun x => if String.string_dec x y
                                    then true else false)
                          (get_image_vars rename_x)))
        xs = true ->
      witness_function (to_RenameMap rename_x) f xs.
  Proof.
    exists (get_witness rename_x).
    intros. simpl. unfold witness_function. intros.
    repeat (destruct_ite; simpl); subst; try reflexivity;
    try (rewrite List.forallb_forall in H;
         specialize (H _ H0); discriminate).
  Qed.

  Lemma y_witness_function :
    exists f,
    forall xs,
      List.forallb
        (fun y => negb (List.existsb
                          (fun x => if String.string_dec x y
                                    then true else false)
                          (get_image_vars rename_y)))
        xs = true ->
      witness_function (to_RenameMap rename_y) f xs.
  Proof.
    exists (get_witness rename_y).
    intros. simpl. unfold witness_function. intros.
    repeat (destruct_ite; simpl); subst; try reflexivity;
    try (rewrite List.forallb_forall in H;
         specialize (H _ H0); discriminate).
  Qed.

  Definition UpperLower_X_SpecR :
    { x : SysRec &
          SysRec_equiv
            (SysRename
               (to_RenameMap rename_x)
               (deriv_term_RenameList rename_x)
               UpperLower_X.SpecR)
            x}.
  Proof.
    discharge_sysrec_equiv_rename.
  Defined.
(*
  Definition UpperLower_X_SpecR :
    { x : SysRec &
          PartialSysD x |--
            Rename (to_RenameMap rename_x)
                   (PartialSysD UpperLower_X.SpecR) }.
  Proof.
    discharge_PartialSys_rename_formula.
  Defined.
*)

  Lemma UpperLower_X_Enabled :
    |-- Enabled (Discr (projT1 UpperLower_X_SpecR).(Prog)
                       (projT1 UpperLower_X_SpecR).(maxTime)).
  Proof.
    pose proof (projT2 UpperLower_X_SpecR). cbv beta in H.
    rewrite <- H. clear H.
    pose proof x_witness_function. destruct H.
    eapply subst_enabled_sys_discr with (f:=x).
    { apply get_vars_next_state_vars; reflexivity. }
    { apply H; reflexivity. }
    { reflexivity. }
    { apply UpperLower_X.UpperLower_enabled. }
  Qed.

  Lemma UpperLower_X_Proposed_refine :
    forall t,
      (UpperLower_X.Monitor.SafeAcc t //\\ "a"! = t
       |-- UpperLower_X.Monitor.SafeAcc "a"!).
  Proof.
    breakAbstraction. solve_linear. rewrite H1 in *.
    solve_linear.
  Qed.

  Lemma same_next :
    forall x y,
      (x! = R0 //\\ y! = R0 |-- x! = y!).
  Proof. solve_linear. Qed.

  Definition refined_UpperLower_X_SpecR :
    { ins : list Var &
       { outs : list Var &
           { p : Parallel ins outs &
                 tlaParD p |--
                 Prog (projT1 UpperLower_X_SpecR)} } }.
  Proof.
    Opaque UpperLower_X.Monitor.SafeAcc
           UpperLower_X.Monitor.Default.
    eexists. eexists. eexists. simpl. restoreAbstraction.
    match goal with
    | [ |- context [ rename_formula ?m _ ] ]
      => remember m as rx
    end.
    match goal with
    | [ |- context
             [ rename_formula _ (rename_formula ?m _) ] ]
      => remember m as rm
    end.
    repeat rewrite minus_eq.
    rewrite land_distr.
    apply par_disjoint_refine.
    { repeat rewrite land_lor_distr_R.
      pose proof UpperLower_X_Proposed_refine
        as Hrefine. specialize (Hrefine "A").
      apply (Proper_Rename rx rx) in Hrefine;
        [ | reflexivity].
      rewrite <- Rename_ok in Hrefine.
      rewrite <- Rename_ok in Hrefine.
      rewrite <- Hrefine at 1. clear Hrefine.
      pose proof UpperLower_X_Proposed_refine as Hrefine.
      specialize (Hrefine "A").
      apply (Proper_Rename rm rm) in Hrefine;
        [ | reflexivity].
      apply (Proper_Rename rx rx) in Hrefine;
        [ | reflexivity].
      rewrite <- Rename_ok with (m:=rm) in Hrefine.
      rewrite <- Rename_ok with (m:=rm) in Hrefine.
      rewrite <- Rename_ok with (m:=rx) in Hrefine.
      rewrite <- Rename_ok with (m:=rx) in Hrefine.
      rewrite <- Hrefine at 1. clear Hrefine.
      repeat rewrite lorA.
      Transparent UpperLower_X.Monitor.SafeAcc
                  UpperLower_X.Monitor.Default.
      subst. simpl. restoreAbstraction.
      repeat rewrite minus_eq. rewrite land_distr.
      apply ite_refine.
      { reflexivity. }
      { apply Assign_refine; reflexivity. }
      { rewrite <- lor_intro2. rewrite <- lor_intro2.
        apply ite_refine_and_impl.
        { reflexivity. }
        { solve_linear. }
        { apply ite_refine_and_impl.
          { reflexivity. }
          { solve_linear. }
          { rewrite <- leq_eq_refine.
            apply Assign_refine; reflexivity. }
          { rewrite <- leq_eq_refine.
            apply Assign_refine; reflexivity. } }
        { apply ite_refine_and_impl.
          { reflexivity. }
          { solve_linear. }
          { rewrite <- leq_eq_refine.
            rewrite minus_0_l_equiv.
            rewrite <- neg_eq.
            apply Assign_refine; reflexivity. }
          { rewrite <- leq_eq_refine.
            rewrite minus_0_l_equiv.
            rewrite <- neg_eq.
            apply Assign_refine; reflexivity. } } }
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit. }
    { rewrite landtrueR.
      rewrite <- same_next.
      repeat apply par_disjoint_refine;
      try (apply Assign_refine; reflexivity). }
    Grab Existential Variables.
    { decide_disjoint_var_sets. }
    { decide_disjoint_var_sets. }
    { decide_disjoint_var_sets. }
    { decide_disjoint_var_sets. }
    { decide_disjoint_var_sets. }
    { decide_disjoint_var_sets. }
  Defined.

  Definition UpperLower_Y_SpecR :
    { x : SysRec &
          SysRec_equiv
            (SysRename
               (to_RenameMap rename_y)
               (deriv_term_RenameList rename_y)
               UpperLower_Y.SpecR)
            x}.
  Proof.
    discharge_sysrec_equiv_rename.
  Defined.
(*
  Definition UpperLower_Y_SpecR :
    { x : SysRec &
          PartialSysD x |--
            Rename (to_RenameMap rename_y)
                   (PartialSysD UpperLower_Y.SpecR) }.
  Proof.
    discharge_PartialSys_rename_formula.
  Defined.
*)

  Definition SpecRectR :=
    SysCompose (projT1 UpperLower_X_SpecR)
               (projT1 UpperLower_Y_SpecR).

  Lemma Prog_SysCompose :
    forall a b,
      Prog (SysCompose a b) -|- Prog a //\\ Prog b.
  Proof.
    simpl. restoreAbstraction. intros. split; charge_tauto.
  Qed.

  Lemma RectEnabled :
    |-- SysSafe SpecRectR.
  Proof.
  Admitted.
(*
    apply SysSafe_rule. apply always_tauto.
    unfold Discr.
    rewrite <- disjoint_state_enabled.
    { charge_split.
      { unfold SpecRectR. rewrite Prog_SysCompose.
        repeat rewrite <- disjoint_state_enabled.
        { charge_split.
          { admit. }
          { admit. } }
        { apply formulas_disjoint_state; try reflexivity.
          simpl Prog. restoreAbstraction.
          simpl.
          simpl get_next_vars_formula. simpl.
Print Formula.

rewrite <- ProgRefined_ok.
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
      smart_repeat_eexists. solve_linear. }
  Qed.
*)

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
          SysRec_equiv
            (SysRename
               (to_RenameMap rename_x)
               (deriv_term_RenameList rename_x)
               VelX.SpecR)
            x}.
  Proof.
    discharge_sysrec_equiv_rename.
  Defined.

(*
  Definition SpecVelocityR_X :
    { x : SysRec &
          PartialSysD x |-- Rename (to_RenameMap rename_x)
                                   (PartialSysD VelX.SpecR) }.
  Proof.
    discharge_PartialSys_rename_formula.
  Defined.
*)

  Definition SpecVelocityR_Y :
    { x : SysRec &
          SysRec_equiv
            (SysRename
               (to_RenameMap rename_y)
               (deriv_term_RenameList rename_y)
               VelY.SpecR)
            x}.
  Proof.
    discharge_sysrec_equiv_rename.
  Defined.
(*
  Definition SpecVelocityR_Y :
    { x : SysRec &
          PartialSysD x |-- Rename (to_RenameMap rename_y)
                                   (PartialSysD VelY.SpecR) }.
  Proof.
    discharge_PartialSys_rename_formula.
  Defined.
*)

  Definition SpecVelocityR :=
    SysCompose (projT1 SpecVelocityR_X)
               (projT1 SpecVelocityR_Y).

  (* The velocity and position monitors
     in rectangular coordinates without
     constraints on control inputs. *)
  Definition SpecRectVelocityR :=
    SysCompose SpecVelocityR SpecRectR.

  Let rename_polar : list (Var*Term) :=
    ("ax","a"*sin("theta"))::("ay","a"*cos("theta"))::nil.

  Lemma rectangular_to_polar :
    forall (x y:R),
      { p : (R*R) |
        (eq x ((fst p) * Rtrigo_def.cos (snd p)) /\
         eq y ((fst p) * Rtrigo_def.sin (snd p)))%R }.
  Admitted.

  Lemma polar_witness_function :
    exists f,
    forall xs,
      ~List.In "a" xs ->
      ~List.In "theta" xs ->
      witness_function (to_RenameMap rename_polar) f xs.
  Proof.
    exists
      (fun st x =>
         let witness :=
             proj1_sig
               (rectangular_to_polar (st "ay") (st "ax")) in
         if String.string_dec x "a"
         then fst witness
         else if String.string_dec x "theta"
              then snd witness
              else st x)%R.
    unfold witness_function.
    intros. simpl.
    repeat match goal with
           | [ |- context [if ?e then _ else _] ]
             => destruct e; simpl
           end; subst; simpl.
    { destruct (rectangular_to_polar (st "ay") (st "ax")).
      simpl. tauto. }
    { destruct (rectangular_to_polar (st "ay") (st "ax")).
      simpl. tauto. }
    { contradiction. }
    { contradiction. }
    { reflexivity. }
  Qed.

  Definition SpecPolarR :
    { x : SysRec &
          SysRec_equiv
            (SysRename
               (to_RenameMap rename_polar)
               (deriv_term_RenameList rename_polar)
               SpecRectVelocityR)
            x}.
  Proof.
    discharge_sysrec_equiv_rename.
  Defined.
(*
  Definition SpecPolarR :
    { x : SysRec &
          PartialSysD x |--
            Rename (to_RenameMap rename_polar)
                   (PartialSysD SpecRectVelocityR) }.
  Proof.
    discharge_PartialSys_rename_formula.
  Defined.
*)
(*    apply forget_prem.
    rewrite <- Rename_ok by is_st_term_list.
    simpl; restoreAbstraction.
    setoid_rewrite <- lor_right2.
    enable_ex_st.
    smart_repeat_eexists.
    solve_linear.
    instantiate (2:=sqrt (X.amin*X.amin + Y.amin*Y.amin)).
    instantiate (1:=atan (Y.amin/X.amin)).
    rewrite ArithFacts.sin_atan. admit.
    rewrite ArithFacts.sin_atan. admit.
    rewrite ArithFacts.cos_atan. admit.
    rewrite ArithFacts.cos_atan. admit.*)

  Definition InputConstraint : Formula :=
    P.theta_min <= "theta" <= P.theta_max.

  Definition InputConstraintSysR : SysRec :=
    {| Init := InputConstraint;
       Prog := next InputConstraint;
       world := fun _ => TRUE;
       unch := nil;
       maxTime := P.d |}.

  (* The full system, in polar coordinates, with
     control input constraints. *)
  Definition SpecPolarConstrainedR :=
    SysCompose (projT1 SpecPolarR) InputConstraintSysR.

  Lemma rect_safe
    : []"vx" <= P.ubv_X //\\ []"vx" >= --P.ubv_X //\\
      []"vy" <= P.ubv_Y //\\  []"vy" >= --P.ubv_Y
      |-- PartialSysD SpecRectR -->>
          [](rename_formula (to_RenameMap rename_x)
                    UpperLower_X.Safe //\\
             rename_formula (to_RenameMap rename_y)
                    UpperLower_Y.Safe).
  Proof.
    apply PartialCompose.
    { charge_intros. pose proof UpperLower_X.UpperLower_safe.
      apply (Proper_Rename (to_RenameMap rename_x)
                           (to_RenameMap rename_x))
        in H; [ | reflexivity ].
      rewrite Rename_impl in H. rewrite Rename_Always in H.
      rewrite Rename_ok by rw_side_condition.
      charge_apply H. clear.
      { charge_split.
        { rewrite landC. tlaRevert.
          apply forget_prem.
          rewrite <- Rename_ok by rw_side_condition.
          simpl rename_formula. restoreAbstraction.
          repeat rewrite Always_and. apply always_imp.
          solve_linear. }
        { rewrite_rename_pf UpperLower_X_SpecR.
          rewrite PartialSysRename_sound
            by sysrename_side_cond.
          charge_tauto. } } }
    { charge_intros. pose proof UpperLower_Y.UpperLower_safe.
      apply (Proper_Rename (to_RenameMap rename_y)
                           (to_RenameMap rename_y))
        in H; [ | reflexivity ].
      rewrite Rename_impl in H. rewrite Rename_Always in H.
      repeat rewrite Rename_ok by rw_side_condition.
      charge_apply H. clear.
      { charge_split.
        { rewrite landC. tlaRevert.
          apply forget_prem.
          repeat rewrite <- Rename_ok by rw_side_condition.
          simpl rename_formula. restoreAbstraction.
          repeat rewrite Always_and. apply always_imp.
          solve_linear. }
        { rewrite_rename_pf UpperLower_Y_SpecR.
          rewrite PartialSysRename_sound
            by sysrename_side_cond.
          charge_tauto. } } }
  Qed.

  Lemma velocity_safe :
    |-- PartialSysD SpecVelocityR -->>
        [](("vx" <= VX.ub //\\ -- ("vx") <= VX.ub) //\\
            "vy" <= VY.ub //\\ -- ("vy") <= VY.ub).
  Proof.
    apply PartialCompose.
    - rewrite_rename_pf SpecVelocityR_X.
      rewrite PartialSysRename_sound
        by sysrename_side_cond.
      pose proof VelX.UpperLower_safe.
      apply (Proper_Rename (to_RenameMap rename_x)
                           (to_RenameMap rename_x))
        in H; [ | reflexivity ].
      rewrite Rename_impl in H. rewrite Rename_True in H.
      apply landAdj in H. restoreAbstraction.
      rewrite landtrueL in H. rewrite H. clear.
      rewrite <- Rename_ok by rw_side_condition.
      apply always_imp. solve_linear.
    - rewrite_rename_pf SpecVelocityR_Y.
      rewrite PartialSysRename_sound
        by sysrename_side_cond.
      pose proof VelY.UpperLower_safe.
      apply (Proper_Rename (to_RenameMap rename_y)
                           (to_RenameMap rename_y))
        in H; [ | reflexivity ].
      rewrite Rename_impl in H. rewrite Rename_True in H.
      apply landAdj in H. restoreAbstraction.
      rewrite landtrueL in H. rewrite H. clear.
      rewrite <- Rename_ok by rw_side_condition.
      apply always_imp. solve_linear.
  Qed.

  Lemma rect_velocity_safe :
    |-- PartialSysD SpecRectVelocityR -->>
        []((("vx" <= VX.ub //\\ --"vx" <= VX.ub) //\\
            ("vy" <= VY.ub //\\ --"vy" <= VY.ub)) //\\
            (--P.ub_X <= "x" <= P.ub_X //\\
             --P.ub_Y <= "y" <= P.ub_Y)).
  Proof.
    apply PartialCompose.
    - apply velocity_safe.
    - rewrite landtrueL. pose proof rect_safe.
      simpl rename_formula in H. restoreAbstraction.
      charge_intros.
      tlaCutByHyp H.
      { charge_apply H. charge_split.
        { rewrite landC. tlaRevert. apply forget_prem.
          repeat rewrite Always_and. apply always_imp.
          clear. unfold VX.ub, VY.ub. solve_linear. }
        { charge_tauto. } }
      { apply forget_prem. apply always_imp. clear.
        unfold UpperLower_Y.Params.ub,
        UpperLower_X.Params.ub.
        solve_linear. }
  Qed.

Axiom amin_ubv_X : (-P.amin*P.d <= P.ubv_X)%R.
Axiom amin_ubv_Y : (-P.amin*P.d <= P.ubv_Y)%R.

  Theorem box_safe :
    |-- PartialSysD SpecPolarConstrainedR -->>
        []((("vx" <= VX.ub //\\ --"vx" <= VX.ub) //\\
           ("vy" <= VY.ub //\\ --"vy" <= VY.ub)) //\\
           (--P.ub_X <= "x" <= P.ub_X //\\
            --P.ub_Y <= "y" <= P.ub_Y)).
  Proof.
    charge_intros.
    unfold SpecPolarConstrainedR.
    rewrite PartialComposeRefine.
    rewrite_rename_pf SpecPolarR.
    rewrite PartialSysRename_sound
      by sysrename_side_cond.
    pose proof rect_velocity_safe.
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

(*
TODO : translate from polar to rectangular,
refine coupled contraint to a decoupled one
use disjointness lemma.
This will show that you can use disjointness,
even when the system is coupled.
Viewing things as logical formulas that
can be refined makes this process clear.
*)

  Theorem box_enabled :
    |-- SysSafe SpecPolarConstrainedR.
(*
    - apply SysSafe_rule. apply always_tauto.
      simpl. restoreAbstraction.
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
  Admitted.

End Box.
