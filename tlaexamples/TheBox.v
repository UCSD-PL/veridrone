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
Require Import Coq.Reals.Rtrigo1.
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

  Parameter theta_min : R.
  Definition theta_max := (-theta_min)%R.
  Axiom theta_min_bound : (-PI/2 < theta_min < 0)%R.

  (* Gravitational constant *)
  Parameter g : R.
  Axiom g_gt_0 : (g > 0)%R.
  Parameter amin_Y : R.
  Axiom amin_Y_lt_0 : (amin_Y < 0)%R.
  Axiom amin_Y_lt_g : (amin_Y > -g)%R.
  Definition amin_X :=
    ((amin_Y + g) * tan theta_min)%R.

  Parameter ubv_X : R.
  Parameter ubv_Y : R.
  Parameter ub_ubv_X :
    (ubv_X*d - ubv_X*ubv_X*(/2)*(/amin_X) <= ub_X)%R.
  Parameter ub_ubv_Y :
    (ubv_Y*d - ubv_Y*ubv_Y*(/2)*(/amin_Y) <= ub_Y)%R.

End BoxParams.

Module Box (P : BoxParams).
  Open Scope HP_scope.

  Module X <: UpperLowerSecondParams.
    Definition ub := P.ub_X.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin_X.
    Theorem amin_lt_0 : (amin < 0)%R.
    Proof.
      unfold amin, P.amin_X.
      pose proof P.theta_min_bound.
      assert (tan P.theta_min < 0)%R
      by (pose proof P.theta_min_bound;
          apply tan_lt_0; solve_linear).
      pose proof P.amin_Y_lt_0.
      pose proof P.g_gt_0.
      pose proof P.amin_Y_lt_g.
      solve_nonlinear.
    Qed.
    Definition ubv := P.ubv_X.
    Definition ub_ubv := P.ub_ubv_X.
  End X.

  Module Y <: UpperLowerSecondParams.
    Definition ub := P.ub_Y.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin_Y.
    Definition amin_lt_0 := P.amin_Y_lt_0.
    Definition ubv := P.ubv_Y.
    Definition ub_ubv := P.ub_ubv_Y.
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
  Definition SpecRectR :=
    SysCompose (projT1 UpperLower_X_SpecR)
               (projT1 UpperLower_Y_SpecR).
*)

(*
  Lemma RectEnabled :
    |-- Enabled (Discr SpecRectR.(Prog) SpecRectR.(maxTime)).
  Proof.
  Admitted.
*)
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
  Definition SpecVelocityR :=
    SysCompose (projT1 SpecVelocityR_X)
               (projT1 SpecVelocityR_Y).
*)

  Definition SpecXR :=
    SysCompose (projT1 SpecVelocityR_X)
               (projT1 UpperLower_X_SpecR).

  Definition SpecYR :=
    SysCompose (projT1 SpecVelocityR_Y)
               (projT1 UpperLower_Y_SpecR).

  (* The velocity and position monitors
     in rectangular coordinates without
     constraints on control inputs. *)
  Definition SpecRectR :=
    SysCompose SpecXR SpecYR.

  Definition InputConstraintRect : Formula :=
     "ay" + P.g > 0 //\\
     P.theta_min <= ArctanT ("ax"/("ay" + P.g))
                 <= P.theta_max.

  Definition XConstraint :=
    UpperLower_X.Params.amin <= "ax"
    <= --UpperLower_X.Params.amin.

  Definition YConstraint :=
    UpperLower_Y.Params.amin <= "ay"
    <= --UpperLower_Y.Params.amin.

  Definition XConstraintSysR : SysRec :=
    {| Init := XConstraint;
       Prog := next XConstraint;
       world := fun _ => TRUE;
       unch := nil;
       maxTime := P.d |}.

  Definition YConstraintSysR : SysRec :=
    {| Init := YConstraint;
       Prog := next YConstraint;
       world := fun _ => TRUE;
       unch := nil;
       maxTime := P.d |}.

  Definition SpecXConstrainedR :=
    SysCompose SpecXR XConstraintSysR.

  Definition SpecYConstrainedR :=
    SysCompose SpecYR YConstraintSysR.

  Definition RefinedConstraint :=
    XConstraint //\\ YConstraint.

  Lemma refined_constraint_ok :
    RefinedConstraint |-- InputConstraintRect.
  Proof.
    breakAbstraction. intros.
    generalize dependent (Stream.hd tr). intros.
    unfold UpperLower_X.Params.amin,
    UpperLower_Y.Params.amin, X.amin, Y.amin, P.amin_X in *.
    assert (tan P.theta_min < 0)%R
      by (pose proof P.theta_min_bound;
          apply tan_lt_0; solve_linear).
    pose proof P.theta_min_bound.
    pose proof P.amin_Y_lt_0.
    pose proof P.amin_Y_lt_g.
    pose proof P.g_gt_0.
    unfold P.theta_max.
    split; [ solve_linear | ].
    split.
    { apply ArithFacts.tan_increasing_1.
      { solve_linear. }
      { pose proof atan_bound as Hatan.
        match goal with
          |- context [atan ?e] => specialize (Hatan e)
        end. solve_linear. }
      { rewrite atan_right_inv.
        generalize dependent (tan P.theta_min).
        intuition. apply Rmult_le_algebra2; solve_linear.
        solve_nonlinear. } }
    { apply ArithFacts.tan_increasing_1.
      { pose proof atan_bound as Hatan.
        match goal with
          |- context [atan ?e] => specialize (Hatan e)
        end. solve_linear. }
      { solve_linear. }
      { rewrite atan_right_inv.
        rewrite tan_neg.
        generalize dependent (tan P.theta_min).
        intuition. apply Rmult_le_algebra; solve_linear.
        solve_nonlinear. } }
  Qed.

  Definition InputConstraintSysRectR : SysRec :=
    {| Init := InputConstraintRect;
       Prog := next InputConstraintRect;
       world := fun _ => TRUE;
       unch := nil;
       maxTime := P.d |}.

  Definition SpecRectVelocityConstrainedR :=
    SysCompose SpecRectVelocityR InputConstraintSysRectR.

  (* theta is the angle between the y axis and
     the a vector *)
  Let rename_polar : list (Var*Term) :=
    ("ax","a"*sin("theta"))::
    ("ay","a"*cos("theta") - P.g)::nil.

  Lemma rectangular_to_polar :
    forall (x y:R),
      { p : (R*R) |
        (0 <= fst p /\ -PI < snd p <= PI /\
         eq x ((fst p) * Rtrigo_def.cos (snd p)) /\
         eq y ((fst p) * Rtrigo_def.sin (snd p)))%R }.
  Admitted.

  Definition PolarBounds : Formula :=
    0 <= "a" //\\ --PI <= "theta" <= PI.

  Lemma polar_predicated_witness_function :
    exists f,
    forall xs,
      List.forallb (fun x => if String.string_dec x "a"
                             then false else true) xs =
      true ->
      List.forallb (fun x => if String.string_dec x "theta"
                             then false else true) xs =
      true ->
      predicated_witness_function
        (to_RenameMap rename_polar) f xs PolarBounds.
  Proof.
    exists
      (fun st x =>
         let witness :=
             proj1_sig
               (rectangular_to_polar (st "ay" + P.g)
                                     (st "ax")) in
         if String.string_dec x "a"
         then fst witness
         else if String.string_dec x "theta"
              then snd witness
              else st x)%R.
    unfold predicated_witness_function, witness_function.
    split.
    { intros. simpl.
      rewrite List.forallb_forall in *.
      specialize (H "a").
      specialize (H0 "theta").
      repeat match goal with
             | [ |- context [if ?e then _ else _] ]
               => destruct e; simpl
             end; subst; simpl.
      { destruct (rectangular_to_polar (st "ay" + P.g)
                                       (st "ax")).
        simpl. tauto. }
      { destruct (rectangular_to_polar (st "ay" + P.g)
                                       (st "ax")).
        simpl. unfold Value. solve_linear. }
      { destruct (String.string_dec "a" "a");
        intuition congruence. }
      { destruct (String.string_dec "theta" "theta");
        intuition congruence. }
      { reflexivity. } }
    { intros. destruct tr. simpl.
      destruct (rectangular_to_polar (s "ay" + P.g)
                                     (s "ax")).
      simpl. solve_linear. }
  Qed.

  Lemma polar_witness_function :
    exists f,
    forall xs,
      List.forallb (fun x => if String.string_dec x "a"
                             then false else true) xs =
      true ->
      List.forallb (fun x => if String.string_dec x "theta"
                             then false else true) xs =
      true ->
      witness_function (to_RenameMap rename_polar) f xs.
  Proof.
    exists
      (fun st x =>
         let witness :=
             proj1_sig
               (rectangular_to_polar (st "ay" + P.g)
                                     (st "ax")) in
         if String.string_dec x "a"
         then fst witness
         else if String.string_dec x "theta"
              then snd witness
              else st x)%R.
    unfold witness_function.
    intros. simpl.
    rewrite List.forallb_forall in *.
    specialize (H "a").
    specialize (H0 "theta").
    repeat match goal with
           | [ |- context [if ?e then _ else _] ]
             => destruct e; simpl
           end; subst; simpl.
    { destruct (rectangular_to_polar (st "ay" + P.g)
                                     (st "ax")).
      simpl. tauto. }
    { destruct (rectangular_to_polar (st "ay" + P.g)
                                     (st "ax")).
      simpl. unfold Value. solve_linear. }
    { destruct (String.string_dec "a" "a");
      intuition congruence. }
    { destruct (String.string_dec "theta" "theta");
      intuition congruence. }
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

  Definition InputConstraint : Formula :=
      P.theta_min <= "theta" <= P.theta_max.

  Lemma rect_input_refines_polar :
    Rename (to_RenameMap rename_polar) InputConstraintRect
    //\\ PolarBounds |--
    InputConstraint.
  Proof.
    rewrite <- Rename_ok by rw_side_condition.
    breakAbstraction. intros.
    generalize dependent (Stream.hd tr). intros.
    assert (tan P.theta_min < 0)%R
      by (pose proof P.theta_min_bound;
          apply tan_lt_0; solve_linear).
    pose proof P.theta_min_bound.
    pose proof P.amin_Y_lt_0.
    pose proof P.amin_Y_lt_g.
    pose proof P.g_gt_0.
    unfold P.theta_max in *.
    decompose [and] H. clear H.
    apply ArithFacts.tan_increasing_2 in H5.
    { apply ArithFacts.tan_increasing_2 in H9.
      { rewrite atan_right_inv in *. unfold tan in *.
        rewrite sin_antisym in *. rewrite <- cos_sym in *.
        unfold Rminus in *.
        repeat rewrite Raxioms.Rplus_assoc in *.
        rewrite RIneq.Rplus_opp_l in *.
        rewrite RIneq.Rplus_0_r in *.
        assert ((s "a" * cos (s "theta"))%R <> 0%R)
          by solve_linear.
        assert (s "a" <> R0) by solve_linear.
        assert (cos (s "theta") <> R0) by solve_linear.
        rewrite Raxioms.Rmult_comm
        with (r2:= cos (s "theta")) in *.
        rewrite RIneq.Rinv_mult_distr in *; auto.
        repeat rewrite Raxioms.Rmult_assoc in *.
        rewrite Raxioms.Rmult_comm in *.
        repeat rewrite Raxioms.Rmult_assoc in *.
        rewrite Raxioms.Rinv_l in *; auto.
        rewrite RIneq.Rmult_1_r in *.
        unfold Rdiv in *.
        rewrite RIneq.Ropp_mult_distr_l_reverse in H9.
        change (sin (s "theta") * / cos (s "theta"))%R
        with (tan (s "theta")) in *.
        change (sin P.theta_min * / cos P.theta_min)%R
        with (tan P.theta_min) in *.
        assert (-PI/2 < s "theta" < PI/2)%R.
        { apply cos_pos; [ solve_nonlinear | solve_linear ]. }
        { apply ArithFacts.tan_increasing_1 in H5; auto.
          { rewrite <- tan_neg in *.
            apply ArithFacts.tan_increasing_1 in H9; auto.
            solve_linear. }
          { solve_linear. } } }
      { pose proof atan_bound as Hatan.
        match goal with
          |- context [atan ?e] => specialize (Hatan e)
        end. solve_linear. }
      { solve_linear. } }
    { solve_linear. }
    { pose proof atan_bound as Hatan.
      match goal with
        |- context [atan ?e] => specialize (Hatan e)
      end. solve_linear. }
  Qed.

  Definition InputConstraintSysR : SysRec :=
    {| Init := InputConstraint;
       Prog := next InputConstraint;
       world := fun _ => TRUE;
       unch := nil;
       maxTime := P.d |}.

(*
  Lemma InputConstraint_equiv :
    InputConstraint -|-
    Rename (to_RenameMap rename_polar) InputConstraintRect.
  Proof.
    rewrite <- Rename_ok by rw_side_condition.
    split; breakAbstraction.
    simpl. restoreAbstraction.
  Admitted.
*)

  Lemma next_st_formula_equiv :
    forall A B,
      is_st_formula A ->
      is_st_formula B ->
      A -|- B ->
      next A -|- next B.
  Admitted.

  Lemma next_st_formula_entails :
    forall A B,
      is_st_formula A ->
      is_st_formula B ->
      A |-- B ->
      next A |-- next B.
  Admitted.

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

Axiom amin_ubv_X : (-P.amin_X*P.d <= P.ubv_X)%R.
Axiom amin_ubv_Y : (-P.amin_X*P.d <= P.ubv_Y)%R.

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

Lemma Prog_SysCompose :
  forall a b,
    Prog (SysCompose a b) -|- Prog a //\\ Prog b.
Proof.
  simpl. restoreAbstraction. intros. split; charge_tauto.
Qed.


  Theorem box_enabled :
    |-- SysSafe SpecPolarConstrainedR.
  Proof.
    apply SysSafe_rule. apply always_tauto.
    unfold SpecPolarConstrainedR.
    rewrite_rename_pf SpecPolarR.
    rewrite Prog_SysCompose.
    rewrite Prog_SysRename. unfold Discr.
    simpl maxTime.
    simpl (Prog InputConstraintSysR).
    pose proof rect_input_refines_polar.
    apply next_st_formula_entails in H;
      [ | simpl; tauto | simpl; tauto ].
    simpl (next InputConstraint) in H.
    restoreAbstraction. rewrite <- H. clear H.
    rewrite <- disjoint_state_enabled.
    { charge_split.
      { Opaque PolarBounds. simpl next. restoreAbstraction.
        repeat rewrite <- landA. rewrite <- Rename_and.
        Transparent PolarBounds.
        pose proof polar_predicated_witness_function.
        destruct H.
        eapply subst_enabled_predicated_witness_noenv
        with (f:=x).
(*
          => let H := fresh in
             assert (A -|- Rename m A)
               as H by (rewrite <- Rename_ok;
                        [ | rw_side_condition
                          | rw_side_condition;
                            destruct (string_dec x "ax");
                            try reflexivity;
                            destruct (string_dec x "ay");
                            try reflexivity ]; reflexivity);
               rewrite H; clear H
        end;
        repeat rewrite <- Rename_and.
repeat rewrite <- landA.*)
        { simpl; tauto. }
        { apply get_vars_next_state_vars; reflexivity. }
        { apply H; reflexivity. }
        { clear. pose proof refined_constraint_ok.
          apply next_st_formula_entails in H;
            [ | simpl; tauto | simpl; tauto ].
          simpl (next InputConstraintRect) in H.
          restoreAbstraction. rewrite landA.
          rewrite <- H. clear. simpl next.
          restoreAbstraction. unfold SpecRectVelocityR.
          unfold SpecVelocityR. unfold SpecRectR.


    SearchAbout 

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
