Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.ArithFacts.
Require Import TLA.EnabledLemmas.
Require Import TLA.DifferentialInduction.
Require Import Examples.System.
Require Import Examples.UpperLower.
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
  Axiom ub_ubv_X :
    (ubv_X*d - ubv_X*ubv_X*(/2)*(/amin_X) <= ub_X)%R.
  Axiom ub_ubv_Y :
    (ubv_Y*d - ubv_Y*ubv_Y*(/2)*(/amin_Y) <= ub_Y)%R.
  Axiom ubv_X_gt_amin_d : (ubv_X >= -amin_X*d)%R.
  Axiom ubv_Y_gt_amin_d : (ubv_Y >= -amin_Y*d)%R.

End BoxParams.

Module Box (P : BoxParams).
  Open Scope HP_scope.

  Module X_Params <: UpperLowerParams.
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
    Definition ubv_gt_amin_d := P.ubv_X_gt_amin_d.
  End X_Params.

  Module Y_Params <: UpperLowerParams.
    Definition ub := P.ub_Y.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin_Y.
    Definition amin_lt_0 := P.amin_Y_lt_0.
    Definition ubv := P.ubv_Y.
    Definition ub_ubv := P.ub_ubv_Y.
    Definition ubv_gt_amin_d := P.ubv_Y_gt_amin_d.
  End Y_Params.

  Module X := UpperLower X_Params.
  Module Y := UpperLower Y_Params.

  Let rename_y :=
    RenameListC (("A","Ay")::("V","Vy")::("Y","Y")::("y","y")
                 ::("v","vy")::("a","ay")::("Ymax","Ymax")::
                 ("Vmax","Vymax")::nil).
  Let rename_x :=
    RenameListC (("A","Ax")::("V","Vx")::("Y","X")::("y","x")
                 ::("v","vx")::("a","ax")::("Ymax","Xmax")::
                 ("Vmax","Vxmax")::nil).

  Definition X_SpecR :
    { x : SysRec &
          SysRec_equiv
            (SysRename
               (to_RenameMap rename_x)
               (deriv_term_RenameList rename_x)
               X.SpecR)
            x}.
  Proof.
    discharge_sysrec_equiv_rename.
  Defined.

  Definition Y_SpecR :
    { x : SysRec &
          SysRec_equiv
            (SysRename
               (to_RenameMap rename_y)
               (deriv_term_RenameList rename_y)
               Y.SpecR)
            x}.
  Proof.
    discharge_sysrec_equiv_rename.
  Defined.

  (* The velocity and position monitors
     in rectangular coordinates without
     constraints on control inputs. *)
  Definition SpecRectR :=
    SysCompose (projT1 X_SpecR)
               (projT1 Y_SpecR).

  (* theta is the angle between the y axis and
     the a vector *)
  Let rename_polar : list (Var*Term) :=
    ("ax","a"*sin("theta"))::
    ("ay","a"*cos("theta") - P.g)::nil.

  Definition SpecPolarR :
    { x : SysRec &
          SysRec_equiv
            (SysRename
               (to_RenameMap rename_polar)
               (deriv_term_RenameList rename_polar)
               SpecRectR)
            x}.
  Proof.
    discharge_sysrec_equiv_rename.
  Defined.

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
  Definition SpecR :=
    SysCompose (projT1 SpecPolarR) InputConstraintSysR.

  (* The safety of the full system. *)
  Theorem box_safe :
    |-- PartialSysD SpecR -->>
        []((--P.ubv_X <= "vx" <= P.ubv_X //\\
            --P.ub_X <= "x" <= P.ub_X) //\\
           (--P.ubv_Y <= "vy" <= P.ubv_Y //\\
            --P.ub_Y <= "y" <= P.ub_Y)).
  Proof.
    unfold SpecR. rewrite PartialComposeRefine.
    rewrite_rename_pf SpecPolarR.
    unfold SpecRectR. rewrite SysCompose_SysRename.
    apply PartialCompose.
    - rewrite PartialSysRename_sound
        by sysrename_side_cond.
      rewrite_rename_pf X_SpecR.
      rewrite PartialSysRename_sound
        by sysrename_side_cond.
      pose proof X.safety.
      rename_hyp rename_x H. rename_hyp rename_polar H.
      repeat rewrite Rename_True in H.
      repeat rewrite Rename_impl in H. apply landAdj in H.
      restoreAbstraction. rewrite landtrueL in H. rewrite H.
      clear. rewrite <- Rename_ok by rw_side_condition.
      simpl. restoreAbstraction. apply always_imp.
      unfold X.V.ub, X_Params.ubv,
      X.Position.Params.ub, X.Y.ub.
      charge_tauto.
    - rewrite PartialSysRename_sound
        by sysrename_side_cond.
      rewrite_rename_pf Y_SpecR.
      rewrite PartialSysRename_sound
        by sysrename_side_cond.
      pose proof Y.safety.
      rename_hyp rename_y H. rename_hyp rename_polar H.
      repeat rewrite Rename_True in H.
      repeat rewrite Rename_impl in H. apply landAdj in H.
      restoreAbstraction. rewrite landtrueL in H. rewrite H.
      clear. rewrite <- Rename_ok by rw_side_condition.
      simpl. restoreAbstraction. apply always_imp.
      unfold Y.V.ub, Y_Params.ubv,
      Y.Position.Params.ub, Y.Y.ub.
      charge_tauto.
  Qed.

(* The following helps generate code. *)
(*
Definition shift (ub lb:R) (x:Var) : list (Var*Term) :=
  (x,x - ((lb + ub)/2))::nil.
Variable ubx lbx uby lby ubvx ubvy lbvx lbvy : R.

Goal (Rename (to_RenameMap (shift ubx lbx "x"))
        (Rename (to_RenameMap (shift uby lby "y"))
           (Rename (to_RenameMap (shift ubvx lbvx "vx"))
              (Rename (to_RenameMap (shift ubvy lbvy "vy"))
                      (Prog SpecR))))) |-- TRUE.
  unfold SpecR. rewrite_rename_pf SpecPolarR.
  rewrite Prog_SysCompose. rewrite Prog_SysRename.
  unfold SpecRectR. rewrite_rename_pf X_SpecR.
  rewrite_rename_pf Y_SpecR. rewrite Prog_SysCompose.
  repeat rewrite Prog_SysRename. unfold X.SpecR, Y.SpecR.
  repeat rewrite Prog_SysCompose.
  unfold X.Vel.SpecR, X.Position.SpecR,
  Y.Vel.SpecR, Y.Position.SpecR.
  repeat rewrite Prog_SysCompose.
  repeat match goal with
         |- context [ projT1 ?X ]
         => rewrite_rename_pf X
         end.
  repeat rewrite Prog_SysRename.
  Opaque Unchanged.
  simpl Prog. restoreAbstraction.
  (* Get rid of all of the unchanged clauses that
     have no computational meaning. *)
  repeat match goal with
  |- context [ Unchanged ?l ] =>
    rewrite ltrueR with (C:=Unchanged l)
  end; repeat rewrite landtrueR.
  unfold X.Position.Monitor.Ctrl, Y.Position.Monitor.Ctrl,
  X.Vel.Vel.Ctrl, Y.Vel.Vel.Ctrl.
  Rename_rewrite.
  repeat rewrite X.Vel.Vel.Rename_SafeAcc
    by rw_side_condition.
  repeat rewrite X.Vel.Vel.Rename_Default
    by rw_side_condition.
  repeat rewrite Y.Vel.Vel.Rename_SafeAcc
    by rw_side_condition.
  repeat rewrite Y.Vel.Vel.Rename_Default
    by rw_side_condition.
  repeat rewrite X.Position.Monitor.Rename_SafeAcc
    by rw_side_condition.
  repeat rewrite X.Position.Monitor.Rename_Default
    by rw_side_condition.
  repeat rewrite Y.Position.Monitor.Rename_SafeAcc
    by rw_side_condition.
  repeat rewrite Y.Position.Monitor.Rename_Default
    by rw_side_condition.
  simpl rename_term.
  (* Get rid of history variables with no computational
     meaning. *)
  repeat match goal with
  |- context [ Rename ?m ?F ]
  => rewrite ltrueR with (C:=Rename m F)
  end; repeat rewrite landtrueR.
2: rw_side_condition.
2: rw_side_condition.
change RealT with ConstC.
restoreAbstraction.

simpl; restoreAbstraction.
Check SecondDerivUtil.tdist.
SecondDerivUtil.tdist "vx" ("a"!*sin("theta"!)) P.d = 0.
*)

  (* Now we move on to Enabled *)

  Definition InputConstraintRect : Formula :=
     "ay" + P.g > 0 //\\
     P.theta_min <= ArctanT ("ax"/("ay" + P.g))
                 <= P.theta_max.

  Definition XYConstraint :=
    Rename (to_RenameMap rename_x) X.Constraint //\\
    Rename (to_RenameMap rename_y) Y.Constraint.

  Lemma xy_constraint_refinement :
    XYConstraint |-- InputConstraintRect.
  Proof.
    unfold XYConstraint.
    repeat rewrite <- Rename_ok by rw_side_condition.
    breakAbstraction. intros.
    generalize dependent (Stream.hd tr). intros.
    unfold X_Params.amin, Y_Params.amin, P.amin_X in *.
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

  Definition PolarBounds : Formula :=
    0 <= "a" //\\ --PI <= "theta" <= PI.

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
                          (List.remove
                             String.string_dec "Y"
                             (List.remove
                                String.string_dec "y"
                                (get_image_vars rename_y)))))
        xs = true ->
      witness_function (to_RenameMap rename_y) f xs.
  Proof.
    exists (get_witness rename_y).
    intros. simpl. unfold witness_function. intros.
    repeat (destruct_ite; simpl); subst; try reflexivity;
    try (rewrite List.forallb_forall in H;
         specialize (H _ H0); discriminate).
  Qed.

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

  Theorem box_enabled :
    |-- SysSafe SpecR.
  Proof.
    apply SysSafe_rule. apply always_tauto.
    unfold SpecR.
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
      { Opaque PolarBounds to_RenameMap. simpl next.
        restoreAbstraction.
        repeat rewrite <- landA. rewrite <- Rename_and.
        Transparent PolarBounds.
        pose proof polar_predicated_witness_function.
        destruct H.
        eapply subst_enabled_predicated_witness_noenv
        with (f:=x).
        { simpl; tauto. }
        { apply get_vars_next_state_vars; reflexivity. }
        { apply H; reflexivity. }
        { clear. pose proof xy_constraint_refinement.
          apply next_st_formula_entails in H;
            [ | simpl; tauto | simpl; tauto ].
          simpl (next InputConstraintRect) in H.
          restoreAbstraction. rewrite landA.
          rewrite <- H. clear. simpl next.
          restoreAbstraction. unfold SpecRectR.
          rewrite Prog_SysCompose.
          rewrite_rename_pf X_SpecR.
          rewrite_rename_pf Y_SpecR.
          repeat rewrite Prog_SysRename.
          match goal with
          |- context [(Rename ?mx ?x //\\ Rename ?my ?y) //\\
                       Rename ?mx ?xc //\\ Rename ?my ?yx ]
          => assert ((Rename mx x //\\ Rename mx xc) //\\
                     (Rename my y //\\ Rename my yx) |--
                     (Rename mx x //\\ Rename my y) //\\
                      Rename mx xc //\\ Rename my yx)
            by charge_tauto
          end. rewrite <- H. clear.
          rewrite <- disjoint_state_enabled.
          { charge_split.
            { rewrite <- Rename_and.
              pose proof x_witness_function. destruct H.
              eapply subst_enabled_noenv with (f:=x).
              { apply get_vars_next_state_vars; reflexivity. }
              { apply H; reflexivity. }
              { apply X.Prog_constrained_enabled. } }
            { rewrite <- Rename_and.
              pose proof y_witness_function. destruct H.
              eapply subst_enabled_noenv with (f:=x).
              { apply get_vars_next_state_vars; reflexivity. }
              { apply H; reflexivity. }
              { apply Y.Prog_constrained_enabled. } } }
          { repeat rewrite <- Rename_ok by rw_side_condition.
            apply formulas_disjoint_state; reflexivity. } } }
      { enable_ex_st. smart_repeat_eexists. solve_linear. } }
    { simpl next.
      repeat rewrite <- Rename_ok by rw_side_condition.
      apply formulas_disjoint_state; reflexivity. }
  Qed.

End Box.
