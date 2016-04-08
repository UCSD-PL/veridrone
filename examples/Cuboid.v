Require Import Coq.Reals.Reals.
Require Import Logic.Logic.
Require Import Logic.ArithFacts.
Require Import Logic.EnabledLemmas.
Require Import Logic.DifferentialInduction.
Require Import Logic.ProofRules.
Require Import Examples.System.
Require Import Examples.Interval.
Require Import Examples.Rectangle.
Require Import Examples.Quadcopter.
Require Import ChargeCore.Tactics.Lemmas.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

Module Type CuboidParams.
  Parameter ub_X : R.
  Parameter ub_Y : R.
  Parameter ub_Z : R.

  Parameter d : R.
  Axiom d_gt_0 : (d > 0)%R.

  Parameter angle_min : R.
  Definition angle_max := (-angle_min)%R.
  Axiom angle_min_bound : (-PI/2 < angle_min < 0)%R.

  (* Gravitational constant *)
  Parameter g : R.
  Axiom g_gt_0 : (g > 0)%R.
  Parameter amin_Z : R.
  Axiom amin_Z_lt_0 : (amin_Z < 0)%R.
  Axiom amin_Z_lt_g : (amin_Z > -g)%R.
  Definition amin_X :=
    ((amin_Z + g) * tan angle_min)%R.
  Definition amin_Y :=
    ((amin_Z + g) * tan angle_min)%R.

  Parameter ubv_X : R.
  Parameter ubv_Y : R.
  Parameter ubv_Z : R.
  Axiom ubv_X_gt_0 : (ubv_X > 0)%R.
  Axiom ubv_Y_gt_0 : (ubv_Y > 0)%R.
  Axiom ubv_Z_gt_0 : (ubv_Z > 0)%R.
  Axiom ub_ubv_X :
    (ubv_X*d + ubv_X*ubv_X*(0 - /2)*(/amin_X) <= ub_X)%R.
  Axiom ub_ubv_Y :
    (ubv_Y*d + ubv_Y*ubv_Y*(0 - /2)*(/amin_Y) <= ub_Y)%R.
  Axiom ub_ubv_Z :
    (ubv_Z*d + ubv_Z*ubv_Z*(0 - /2)*(/amin_Z) <= ub_Z)%R.
  Axiom ubv_X_gt_amin_d : (ubv_X >= -amin_X*d)%R.
  Axiom ubv_Y_gt_amin_d : (ubv_Y >= -amin_Y*d)%R.
  Axiom ubv_Z_gt_amin_d : (ubv_Z >= -amin_Z*d)%R.

End CuboidParams.

Module CuboidShim (Import P : CuboidParams).
  Open Scope HP_scope.

  Module XZ_Params <: RectangleParams.
    Definition ub_X := P.ub_X.
    Definition ub_Z := P.ub_Z.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition pitch_min := P.angle_min.
    Definition pitch_max := (-P.angle_min)%R.
    Definition pitch_min_bound := P.angle_min_bound.
    Definition g := P.g.
    Definition g_gt_0 := P.g_gt_0.
    Definition amin_Z := P.amin_Z.
    Definition amin_Z_lt_0 := P.amin_Z_lt_0.
    Definition amin_Z_lt_g := P.amin_Z_lt_g.
    Definition amin_X := P.amin_X.
    Definition ubv_X := P.ubv_X.
    Definition ubv_Z := P.ubv_Z.
    Definition ub_ubv_X := P.ub_ubv_X.
    Definition ub_ubv_Z := P.ub_ubv_Z.
    Definition ubv_X_gt_amin_d := P.ubv_X_gt_amin_d.
    Definition ubv_Z_gt_amin_d := P.ubv_Z_gt_amin_d.
    Definition ubv_X_gt_0 := P.ubv_X_gt_0.
    Definition ubv_Z_gt_0 := P.ubv_Z_gt_0.
  End XZ_Params.

  Module Y_Params <: IntervalParams.
    Definition ub := P.ub_Y.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin_Y.
    Lemma amin_lt_0 : (amin < 0)%R.
    Proof.
      unfold amin, P.amin_Y.
      pose proof P.angle_min_bound.
      assert (tan P.angle_min < 0)%R
      by (pose proof P.angle_min_bound;
          apply tan_lt_0; solve_linear).
      pose proof P.amin_Z_lt_0.
      pose proof P.g_gt_0.
      pose proof P.amin_Z_lt_g.
      solve_nonlinear.
    Qed.
    Definition ubv := P.ubv_Y.
    Definition ub_ubv := P.ub_ubv_Y.
    Definition ubv_gt_amin_d := P.ubv_Y_gt_amin_d.
    Definition ubv_gt_0 := P.ubv_Y_gt_0.
  End Y_Params.

  Module XZ := RectangleShim XZ_Params.
  Module Y := IntervalShim Y_Params.

  Let rename_y : RenameList :=
    {{ "y" ~> "y" & "v" ~> "vy" & "a" ~> "ay" }}%rn.

  Let rename_polar : RenameList :=
    {{ "ay" ~> --"A"*sin("roll") &
       "a" ~> "A"*cos("roll") }}%rn.

  Definition Next_no_roll_constraint : ActionFormula :=
    SysRename rename_polar (deriv_term_RenameList rename_polar)
              (SysCompose
                 (SysRename rename_y
                            (deriv_term_RenameList rename_y)
                            Y.Next)
                 XZ.Next).

  Definition InputConstraint : Formula :=
    P.angle_min <= "roll" <= P.angle_max //\\ 0 <= "A".

  (* The full system, with roll input constraints. *)
  Definition Next : ActionFormula :=
    SysCompose Next_no_roll_constraint
               (Sys (next InputConstraint) ltrue d).

  Definition IndInv : ActionFormula :=
    Rename rename_polar (Rename rename_y Y.IndInv //\\
                         XZ.IndInv).

  Transparent ILInsts.ILFun_Ops.

  Lemma TimedPreserves_Next :
    |-- TimedPreserves d IndInv Next.
  Proof with eauto with rw_rename.
    unfold IndInv, Next.
    rewrite SysCompose_abstract.
    unfold Next_no_roll_constraint.
    unfold SysRename.
    rewrite Sys_rename_formula...
    rewrite SysRename_rule...
    rewrite TimedPreserves_Rename...
    unfold SysCompose.
    rewrite SysCompose_simpl.
    rewrite <- TimedPreserves_And_simple
      by (compute; tauto).
    Rename_rewrite.
    charge_split.
    { rewrite Sys_rename_formula...
      rewrite SysRename_rule...
      rewrite TimedPreserves_Rename...
      rewrite <- Y.TimedPreserves_Next.
      Rename_rewrite. charge_tauto. }
    { rewrite <- XZ.TimedPreserves_Next.
      Rename_rewrite. charge_tauto. }
  Qed.

  Opaque ILInsts.ILFun_Ops.

  (* Now we move on to Enabled *)

  Definition YWConstraint :=
    Rename rename_y Y.Constraint //\\ amin_Z + g <= "a".

  Definition RollConstraintRect : Formula :=
    P.angle_min <= ArctanT (--"ay"/"a") <= P.angle_max.

  Lemma yw_constraint_refinement :
    YWConstraint |-- RollConstraintRect.
  Proof.
    unfold YWConstraint, XZ.InputConstraint.
    repeat rewrite <- Rename_ok by rw_side_condition.
    breakAbstraction. intros.
    generalize dependent (Stream.hd tr). intros.
    unfold Y_Params.amin, amin_Y in *.
    pose proof P.angle_min_bound.
    pose proof P.amin_Z_lt_0.
    pose proof P.amin_Z_lt_g.
    pose proof P.g_gt_0.
    apply arctan_constraint_refinement
    with (b:=(-(amin_Z + P.g))%R);
      solve_linear.
  Qed.

  Let polar_inv : RenameList :=
    {{ "A" ~> SqrtT ("a"*"a" + "ay" * "ay") &
       "roll" ~> ArctanT (--"ay"/"a") }}%rn.

  Lemma inv_input_constraint :
    YWConstraint |-- Rename polar_inv InputConstraint.
  Proof.
    rewrite yw_constraint_refinement.
    rewrite <- Rename_ok by eauto with rw_rename.
    simpl. restoreAbstraction. unfold RollConstraintRect.
    charge_split; [ charge_assumption | ].
    breakAbstraction. intros. apply sqrt_pos.
  Qed.

  Lemma polar_inv_ok :
    forall xs,
      List.forallb (fun x => if String.string_dec x "A"
                             then false else true) xs =
      true ->
      List.forallb (fun x => if String.string_dec x "roll"
                             then false else true) xs =
      true ->
      forall st x,
        List.In x xs ->
        eval_formula YWConstraint (Stream.forever st) ->
        subst_state rename_polar
                    (subst_state polar_inv st) x = st x.
  Proof.
    simpl. unfold Value, subst_state. simpl. intros.
    pose proof
         (rectangular_to_polar1 (st "a") (-(st "ay"))).
    destruct H3 as [Hw Hy].
    { pose proof P.amin_Z_lt_0. pose proof P.amin_Z_lt_g.
      solve_linear. }
    { rewrite List.forallb_forall in *.
      specialize (H "A"). specialize (H0 "roll").
      pose proof (Rsqr_neg (st "ay")). unfold Rsqr in H3.
      rewrite <- H3 in Hy. rewrite <- H3 in Hw.
      repeat destruct_ite; subst; simpl in *.
      { repeat rewrite Rminus_0_l. solve_linear. }
      { repeat rewrite Rminus_0_l. solve_linear. }
      repeat destruct_ite; subst.
      { specialize (H H1). simpl in *; discriminate. }
      { specialize (H0 H1). simpl in *; discriminate. }
      { reflexivity. } }
  Qed.

  Lemma y_witness_function :
    exists f,
    forall xs,
      List.forallb
        (fun y => negb (List.existsb
                          (fun x => if String.string_dec x y
                                    then true else false)
                          (List.remove
                                String.string_dec "y"
                                (get_image_vars rename_y))))
        xs = true ->
      witness_function (to_RenameMap rename_y) f xs.
  Proof.
    exists (get_witness rename_y).
    intros. simpl. unfold witness_function. intros.
    repeat (destruct_ite; simpl); subst; try reflexivity;
    try (rewrite List.forallb_forall in H;
         specialize (H _ H0); discriminate).
  Qed.

  Theorem SysNeverStuck_Discr :
    IndInv //\\ "T" = 0 |-- Enabled (Sys_D Next).
  Proof.
    unfold Sys_D, IndInv.
    rewrite_rename_equiv ("T" = 0) rename_polar.
    rewrite <- Rename_and.
    rewrite Rename_ok by eauto with rw_rename.
    eapply subst_enabled_full
    with (R:=YWConstraint) (Q:= InputConstraint).
    { tlaIntuition. }
    { tlaIntuition. }
    { apply is_action_formula_ok; simpl; tauto. }
    { apply get_vars_next_state_vars; reflexivity. }
    { intros. eapply polar_inv_ok. 3: apply H.
      reflexivity. reflexivity. auto. }
    { apply inv_input_constraint. }
    { repeat rewrite landA. unfold YWConstraint.
      rewrite next_And. repeat rewrite next_Rename.
      match goal with
        |- _ |-- Enabled (?X //\\ ?Z //\\ ?XC //\\ ?ZC) =>
        assert (X //\\ Z //\\ XC //\\ ZC -|-
                  (X //\\ XC) //\\ (Z //\\ ZC))
          as H by (split; charge_tauto);
          rewrite H; clear H
      end.
      rewrite <- Rename_ok
      with (m:=rename_y) (F:=next Y.Constraint)
        by eauto with rw_rename.
      rewrite <- disjoint_state_enabled.
      { charge_split.
        { pose proof y_witness_function. destruct H.
          charge_assert (Rename rename_y Y.IndInv //\\ "T"=0);
            [ charge_tauto | charge_clear; charge_intros ].
          rewrite_rename_equiv ("T" = 0) rename_y.
          repeat rewrite Rename_ok
          with (m:=rename_y) by eauto with rw_rename.
          repeat rewrite <- Rename_and.
          eapply subst_enabled with (f:=x).
          { apply get_vars_next_state_vars; reflexivity. }
          { apply H; reflexivity. }
          { clear. pose proof Y.SysNeverStuck_Discr.
            etransitivity;
              [ apply H | apply Proper_Enabled_lentails ].
            charge_tauto. } }
        { assert (XZ.InputConstraint |--
                  XZ.InputConstraint //\\ amin_Z + g <= "a").
          { unfold XZ.InputConstraint, XZ_Params.amin_Z,
            XZ_Params.g. charge_tauto. }
          repeat rewrite landA. rewrite <- next_And.
          apply next_st_formula_entails in H;
            [ | tlaIntuition | tlaIntuition ].
          rewrite <- H. rewrite <- XZ.SysNeverStuck_Discr.
          charge_tauto. } }
      { apply formulas_disjoint_state; reflexivity. } }
  Qed.

  Theorem SysNeverStuck_Next : |-- SysNeverStuck d IndInv Next.
  Proof.
    eapply SysNeverStuck_Sys;
    [ pose proof d_gt_0 ; solve_linear | | ].
    { rewrite <- disjoint_state_enabled.
      { charge_split.
        { charge_clear. apply Enabled_TimeBound. pose proof P.d_gt_0.
          unfold Y.X_Params.d, Y_Params.d. assumption. }
        {  apply SysNeverStuck_Discr. } }
      { apply formulas_disjoint_state; reflexivity. } }
    { admit. (** Provable, but we won't worry about it *) }
  Admitted.

  Definition Safe : StateFormula :=
    Rename rename_polar (XZ.Safe //\\ Rename rename_y Y.Safe).

  Lemma IndInv_impl_Safe : IndInv //\\ TimeBound P.d |-- Safe.
  Proof with (eauto with rw_rename).
    unfold Safe, TimeBound, IndInv.
    rewrite_rename_equiv (0 <= "T" <= P.d) rename_polar.
    rewrite <- Rename_and.
    apply Proper_Rename_lentails; try reflexivity.
    charge_split.
    { rewrite <- XZ.IndInv_impl_Safe.
      unfold IndInv, TimeBound. repeat rewrite Rename_and.
      charge_split; [ charge_assumption | ].
      charge_revert. charge_clear.
      repeat rewrite <- (Rename_ok _ rename_x)...
      repeat rewrite <- Rename_ok...
      simpl. restoreAbstraction. charge_tauto. }
    { rewrite <- Y.IndInv_impl_Safe. unfold IndInv, TimeBound.
      repeat rewrite Rename_and.
      charge_split; [ charge_assumption | ].
      charge_revert. charge_clear.
      repeat rewrite <- (Rename_ok _ rename_y)...
      repeat rewrite <- Rename_ok...
      simpl. restoreAbstraction. charge_tauto. }
  Qed.

  Lemma W_quad_refines :
    W_quad P.g |-- Sys_w Next.
  Proof.
    (* Mechanical reasoning about abstractions of
       differential equations. *)
  Admitted.

  Lemma constraints_small_angle :
    Rename rename_polar XZ.InputConstraint //\\
    InputConstraint |-- small_angle angle_min.
  Proof.
    rewrite <- Rename_ok by eauto with rw_rename.
    breakAbstraction. intros. solve_linear.
  Qed.

  Definition Next_quad :=
    Quadcopter P.d P.g P.angle_min (Sys_D Next).
  
  Lemma SafeAndReactive_Next_quad :
    |-- SafeAndReactive d IndInv Next_quad.
  Proof.
    unfold Next_quad, Quadcopter.
    eapply Quadcopter_refine.
      { apply P.d_gt_0. }
      { pose proof P.angle_min_bound. solve_linear. }
      { apply TimedPreserves_Next. }
      { apply SysNeverStuck_Next. }
      { unfold Sys_D. pose proof constraints_small_angle.
        apply next_st_formula_entails in H;
          [ | intuition | intuition ]. rewrite <- H.
        rewrite Rename_ok by eauto with rw_rename.
        repeat rewrite Rename_and. rewrite next_And.
        rewrite next_Rename. charge_tauto. }
      { apply W_quad_refines. }
  Qed.

  Theorem Cuboid_safe_quad :
    |-- (IndInv //\\ TimeBound P.d) //\\
        []SysSystem (Quadcopter P.d P.g P.angle_min
                                (Sys_D Next))
        -->> []Safe.
  Proof.
    rewrite Inductively.Preserves_Inv_simple.
    { rewrite IndInv_impl_Safe.
      charge_tauto. }
    { compute; tauto. }
    { apply SafeAndReactive_TimedPreserves.
      apply SafeAndReactive_Next_quad. }
  Qed.

End CuboidShim.
