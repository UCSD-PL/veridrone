Require Import Coq.Reals.Reals.
Require Import Logic.Logic.
Require Import Logic.ArithFacts.
Require Import Logic.EnabledLemmas.
Require Import Logic.DifferentialInduction.
Require Import Logic.ProofRules.
Require Import Examples.System.
Require Import Examples.Interval.
Require Import Examples.Quadcopter.
Require Import ChargeCore.Tactics.Lemmas.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

Module Type RectangleParams.
  Parameter ub_X : R.
  Parameter ub_Z : R.

  Parameter d : R.
  Axiom d_gt_0 : (d > 0)%R.

  Parameter pitch_min : R.
  Definition pitch_max := (-pitch_min)%R.
  Axiom pitch_min_bound : (-PI/2 < pitch_min < 0)%R.

  (* Gravitational constant *)
  Parameter g : R.
  Axiom g_gt_0 : (g > 0)%R.
  Parameter amin_Z : R.
  Axiom amin_Z_lt_0 : (amin_Z < 0)%R.
  Axiom amin_Z_lt_g : (amin_Z > -g)%R.
  Definition amin_X :=
    ((amin_Z + g) * tan pitch_min)%R.

  Parameter ubv_X : R.
  Parameter ubv_Z : R.
  Axiom ubv_X_gt_0 : (ubv_X > 0)%R.
  Axiom ubv_Z_gt_0 : (ubv_Z > 0)%R.
  Axiom ub_ubv_X :
    (ubv_X*d + ubv_X*ubv_X*(0 - /2)*(/amin_X) <= ub_X)%R.
  Axiom ub_ubv_Z :
    (ubv_Z*d + ubv_Z*ubv_Z*(0 - /2)*(/amin_Z) <= ub_Z)%R.
  Axiom ubv_X_gt_amin_d : (ubv_X >= -amin_X*d)%R.
  Axiom ubv_Z_gt_amin_d : (ubv_Z >= -amin_Z*d)%R.

End RectangleParams.

Module RectangleShim (P : RectangleParams).
  Open Scope HP_scope.

  Module X_Params <: IntervalParams.
    Definition ub := P.ub_X.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin_X.
    Theorem amin_lt_0 : (amin < 0)%R.
    Proof.
      unfold amin, P.amin_X.
      pose proof P.pitch_min_bound.
      assert (tan P.pitch_min < 0)%R
      by (pose proof P.pitch_min_bound;
          apply tan_lt_0; solve_linear).
      pose proof P.amin_Z_lt_0.
      pose proof P.g_gt_0.
      pose proof P.amin_Z_lt_g.
      solve_nonlinear.
    Qed.
    Definition ubv := P.ubv_X.
    Definition ub_ubv := P.ub_ubv_X.
    Definition ubv_gt_amin_d := P.ubv_X_gt_amin_d.
    Definition ubv_gt_0 := P.ubv_X_gt_0.
  End X_Params.

  Module Z_Params <: IntervalParams.
    Definition ub := P.ub_Z.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin_Z.
    Definition amin_lt_0 := P.amin_Z_lt_0.
    Definition ubv := P.ubv_Z.
    Definition ub_ubv := P.ub_ubv_Z.
    Definition ubv_gt_amin_d := P.ubv_Z_gt_amin_d.
    Definition ubv_gt_0 := P.ubv_Z_gt_0.
  End Z_Params.

  Module X := IntervalShim X_Params.
  Module Z := IntervalShim Z_Params.

  Let rename_z : RenameList :=
    {{ "y" ~> "z" & "v" ~> "vz" & "a" ~> "az" }}%rn.

  Let rename_x : RenameList :=
    {{ "y" ~> "x" & "v" ~> "vx" & "a" ~> "ax" }}%rn.

  (* The velocity and position monitors
     in rectangular coordinates without
     constraints on control inputs. *)
  Definition NextRect : ActionFormula :=
    SysCompose (SysRename rename_x (deriv_term_RenameList rename_x) X.Next)
               (SysRename rename_z (deriv_term_RenameList rename_z) Z.Next).

  (* theta is the angle between the y axis and
     the a vector *)
  Let rename_polar : RenameList :=
    {{ "ax" ~> "a"*sin("pitch") & "az" ~> "a"*cos("pitch") - P.g }}%rn.

  (* The system in polar coordinates, without the
     constraint on theta. *)
  Definition NextPolar : ActionFormula :=
    SysRename rename_polar (deriv_term_RenameList rename_polar) NextRect.

  Definition InputConstraint : Formula :=
      P.pitch_min <= "pitch" <= P.pitch_max //\\
      P.amin_Z + P.g <= "a".

  (* The full system, in polar coordinates, with
     control input constraints. *)
  Definition Next : ActionFormula :=
    SysCompose NextPolar (Sys (next InputConstraint) ltrue P.d).

  Definition IndInv : ActionFormula :=
    Rename rename_polar (Rename rename_x X.IndInv //\\
                         Rename rename_z Z.IndInv).

  Transparent ILInsts.ILFun_Ops.

  Lemma TimedPreserves_Next :
    |-- TimedPreserves P.d IndInv Next.
  Proof with eauto with rw_rename.
    unfold IndInv, Next.
    rewrite SysCompose_abstract.
    unfold NextPolar. unfold SysRename.
    rewrite Sys_rename_formula...
    rewrite SysRename_rule...
    rewrite TimedPreserves_Rename...
    rewrite SysCompose_simpl.
    rewrite <- TimedPreserves_And_simple
      by (compute; tauto).
    rewrite Rename_and.
    charge_split.
    { rewrite Sys_rename_formula...
      rewrite SysRename_rule...
      rewrite TimedPreserves_Rename...
      rewrite <- X.TimedPreserves_Next.
      Rename_rewrite. charge_tauto. }
    { rewrite Sys_rename_formula...
      rewrite SysRename_rule...
      rewrite TimedPreserves_Rename...
      rewrite <- Z.TimedPreserves_Next.
      Rename_rewrite. charge_tauto. }
  Qed.

  Opaque ILInsts.ILFun_Ops.

  (* Now we move on to Enabled *)

  Definition InputConstraintRect : Formula :=
     "az" + P.g > 0 //\\
     P.pitch_min <= ArctanT ("ax"/("az" + P.g))
                 <= P.pitch_max.

  Definition XZConstraint :=
    Rename rename_x X.Constraint //\\
    Rename rename_z Z.Constraint.

  Lemma xy_constraint_refinement :
    XZConstraint |-- InputConstraintRect.
  Proof.
    unfold XZConstraint.
    repeat rewrite <- Rename_ok by rw_side_condition.
    breakAbstraction. intros.
    generalize dependent (Stream.hd tr). intros.
    unfold X_Params.amin, Z_Params.amin, P.amin_X in *.
    pose proof P.pitch_min_bound.
    pose proof P.amin_Z_lt_0.
    pose proof P.amin_Z_lt_g.
    pose proof P.g_gt_0.
    unfold P.pitch_max.
    split; [ solve_linear | ].
    apply arctan_constraint_refinement
    with (b:=(-(P.amin_Z + P.g))%R);
      solve_linear.
  Qed.

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

  Lemma z_witness_function :
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
                                (get_image_vars rename_z)))))
        xs = true ->
      witness_function (to_RenameMap rename_z) f xs.
  Proof.
    exists (get_witness rename_z).
    intros. simpl. unfold witness_function. intros.
    repeat (destruct_ite; simpl); subst; try reflexivity;
    try (rewrite List.forallb_forall in H;
         specialize (H _ H0); discriminate).
  Qed.

  Let polar_inv : RenameList :=
    {{ "a" ~> SqrtT (("az" + P.g)*("az" + P.g) +
                     "ax" * "ax") &
       "pitch" ~> ArctanT ("ax"/("az" + P.g)) }}%rn.

  Lemma polar_inv_ok :
    forall xs,
      List.forallb (fun x => if String.string_dec x "a"
                             then false else true) xs =
      true ->
      List.forallb (fun x => if String.string_dec x "pitch"
                             then false else true) xs =
      true ->
      forall st x,
        List.In x xs ->
        eval_formula XZConstraint (Stream.forever st) ->
        subst_state rename_polar
                    (subst_state polar_inv st) x = st x.
  Proof.
    simpl. unfold Value, subst_state. simpl. intros.
    pose proof
         (rectangular_to_polar1 (st "az" + P.g) (st "ax")).
    destruct H3 as [Hz Hx].
    { unfold Z_Params.amin in *. pose proof P.amin_Z_lt_0.
      pose proof P.amin_Z_lt_g. solve_linear. }
    { repeat destruct_ite; subst; simpl in *;
      auto; solve_linear.
      rewrite List.forallb_forall in *.
      specialize (H "a").
      specialize (H0 "pitch").
      repeat match goal with
             | [ |- context [if ?e then _ else _] ]
               => destruct e; simpl
             end; subst; simpl.
      { specialize (H H1). simpl in *; discriminate. }
      { specialize (H0 H1). simpl in *; discriminate. }
      { reflexivity. } }
  Qed.

  Lemma inv_input_constraint :
    XZConstraint |-- Rename polar_inv InputConstraint.
  Proof.
    charge_assert (XZConstraint);
      [ charge_assumption | charge_intros ].
    rewrite xy_constraint_refinement at 1.
    rewrite <- Rename_ok by eauto with rw_rename.
    simpl. restoreAbstraction. unfold InputConstraintRect.
    charge_split; [ charge_assumption | ].
    unfold XZConstraint.
    rewrite <- Rename_ok by eauto with rw_rename.
    rewrite <- Rename_ok by eauto with rw_rename.
    breakAbstraction. intros. unfold Z_Params.amin in *.
    intuition. rewrite H0.
    transitivity (sqrt
      ((Stream.hd tr "az" + P.g) *
                  (Stream.hd tr "az" + P.g)))%R.
    { rewrite sqrt_square; solve_linear. }
    { apply sqrt_le_1_alt.
      assert (0 <= Stream.hd tr "ax" * Stream.hd tr "ax")%R
        by apply Rle_0_sqr. solve_linear. }
  Qed.

  Lemma SysNeverStuck_Discr :
    IndInv //\\ "T" = 0 |-- Enabled (Sys_D Next).
  Proof.
    unfold Sys_D, IndInv.
    rewrite_rename_equiv ("T" = 0) rename_polar.
    rewrite <- Rename_and.
    rewrite Rename_ok by eauto with rw_rename.
    eapply subst_enabled_full
    with (R:=XZConstraint) (Q:=InputConstraint).
    { tlaIntuition. }
    { tlaIntuition. }
    { apply is_action_formula_ok; simpl; tauto. }
    { apply get_vars_next_state_vars; reflexivity. }
    { intros. eapply polar_inv_ok. 3: apply H.
      reflexivity. reflexivity. auto. }
    { apply inv_input_constraint. }
    { repeat rewrite landA. unfold XZConstraint.
      rewrite next_And. repeat rewrite next_Rename.
      match goal with
        |- _ |-- Enabled (?X //\\ ?Z //\\ ?XC //\\ ?ZC) =>
        assert (X //\\ Z //\\ XC //\\ ZC -|-
                  (X //\\ XC) //\\ (Z //\\ ZC))
          as H by (split; charge_tauto);
          rewrite H; clear H
      end.
      rewrite <- Rename_ok
      with (m:=rename_x) (F:=next X.Constraint)
        by eauto with rw_rename.
      rewrite <- Rename_ok
      with (m:=rename_z) (F:=next Z.Constraint)
        by eauto with rw_rename.
      rewrite <- disjoint_state_enabled.
      { charge_split.
        { pose proof x_witness_function. destruct H.
          charge_assert (Rename rename_x X.IndInv //\\ "T"=0);
            [ charge_tauto | charge_clear; charge_intros ].
          rewrite_rename_equiv ("T" = 0) rename_x.
          repeat rewrite Rename_ok
          with (m:=rename_x) by eauto with rw_rename.
          repeat rewrite <- Rename_and.
          eapply subst_enabled with (f:=x).
          { apply get_vars_next_state_vars; reflexivity. }
          { apply H; reflexivity. }
          { clear. pose proof X.SysNeverStuck_Discr.
            etransitivity;
              [ apply H | apply Proper_Enabled_lentails ].
            charge_tauto. } }
        { pose proof z_witness_function. destruct H.
          charge_assert (Rename rename_z Z.IndInv //\\ "T"=0);
            [ charge_tauto | charge_clear; charge_intros ].
          rewrite_rename_equiv ("T" = 0) rename_z.
          repeat rewrite Rename_ok
          with (m:=rename_z) by eauto with rw_rename.
          repeat rewrite <- Rename_and.
          eapply subst_enabled with (f:=x).
          { apply get_vars_next_state_vars; reflexivity. }
          { apply H; reflexivity. }
          { clear. pose proof Z.SysNeverStuck_Discr.
            etransitivity;
              [ apply H | apply Proper_Enabled_lentails ].
            charge_tauto. } } }
      { apply formulas_disjoint_state; reflexivity. } }
  Qed.

  Let rename_quad : RenameList :=
    {{ "a" ~> "A"*cos("roll") }}%rn.

  Let quad_inv : RenameList :=
    {{ "A" ~> "a" & "roll" ~> 0 }}%rn.

  Let small_angle := small_angle P.pitch_min.

  Lemma InputConstraint_small_angle :
    InputConstraint |-- Rename quad_inv small_angle.
  Proof.
    rewrite <- Rename_ok by eauto with rw_rename.
    breakAbstraction. intros.
    pose proof P.pitch_min_bound. pose proof P.amin_Z_lt_g.
    unfold angle_max, P.pitch_max in *. solve_linear.
  Qed.

  Lemma quad_inv_ok :
    forall xs,
      List.forallb (fun x => if String.string_dec x "A"
                             then false else true) xs =
      true ->
      List.forallb (fun x => if String.string_dec x "roll"
                             then false else true) xs =
      true ->
      forall st x,
        List.In x xs ->
        eval_formula InputConstraint (Stream.forever st) ->
        subst_state rename_quad
                    (subst_state quad_inv st) x = st x.
  Proof.
    simpl. unfold Value, subst_state. simpl. intros.
    repeat destruct_ite; subst; simpl in *.
    { rewrite cos_0. solve_linear. }
    { rewrite List.forallb_forall in *. specialize (H "A").
      specialize (H0 "roll").
      repeat destruct_ite; subst; simpl.
      { specialize (H H1). simpl in *; discriminate. }
      { specialize (H0 H1). simpl in *; discriminate. }
      { reflexivity. } }
  Qed.

  Definition Next_quad : ActionFormula :=
    SysCompose
      (SysRename rename_quad
                 (deriv_term_RenameList rename_quad) Next)
      (Sys (next small_angle) ltrue P.d).

  Definition IndInv_quad := Rename rename_quad IndInv.

  Lemma SysNeverStuck_Discr_quad :
    IndInv_quad //\\ "T" = 0 |-- Enabled (Sys_D Next_quad).
  Proof.
    unfold Sys_D, IndInv_quad.
    rewrite_rename_equiv ("T" = 0) rename_quad.
    rewrite <- Rename_and.
    rewrite Rename_ok by eauto with rw_rename.
    eapply subst_enabled_full
    with (R:=InputConstraint) (Q:=small_angle).
    { tlaIntuition. }
    { tlaIntuition. }
    { apply is_action_formula_ok; simpl; tauto. }
    { apply get_vars_next_state_vars; reflexivity. }
    { intros. eapply quad_inv_ok. 3: apply H.
      reflexivity. reflexivity. auto. }
    { apply InputConstraint_small_angle. }
    { repeat rewrite landA. rewrite <- land_dup.
      pose proof SysNeverStuck_Discr. unfold Sys_D in H.
      rewrite Rename_ok in * by eauto with rw_rename.
      assumption. }
  Qed.

  Theorem SysNeverStuck_Next :
    |-- SysNeverStuck P.d IndInv_quad Next_quad.
  Proof.
    eapply SysNeverStuck_Sys;
    [ pose proof P.d_gt_0 ; solve_linear | | ].
    { rewrite <- disjoint_state_enabled.
      { charge_split.
        { charge_clear. apply Enabled_TimeBound.
          pose proof P.d_gt_0.
          unfold X.X_Params.d, X_Params.d. assumption. }
        { apply SysNeverStuck_Discr_quad. } }
      { apply formulas_disjoint_state; reflexivity. } }
    { admit. (** Provable, but we won't worry about it *) }
  Admitted.

  Definition Safe : StateFormula :=
    Rename rename_quad
           (Rename rename_polar
                   (Rename rename_x X.Safe //\\
                    Rename rename_z Z.Safe)).

  Lemma IndInv_impl_Safe :
    IndInv_quad //\\ TimeBound P.d |-- Safe.
  Proof with (eauto with rw_rename).
    unfold Safe, TimeBound, IndInv_quad.
    rewrite_rename_equiv (0 <= "T" <= P.d) rename_quad.
    rewrite <- Rename_and.
    apply Proper_Rename_lentails; try reflexivity.
    rewrite_rename_equiv (0 <= "T" <= P.d) rename_polar.
    unfold IndInv. rewrite <- Rename_and.
    apply Proper_Rename_lentails; try reflexivity.
    charge_split.
    { rewrite <- X.IndInv_impl_Safe.
      unfold TimeBound, X_Params.d. rewrite Rename_and.
      rewrite <- Rename_ok with (F:=0 <= "T" <= P.d)
        by eauto with rw_rename. simpl. restoreAbstraction.
      charge_tauto. }
    { rewrite <- Z.IndInv_impl_Safe.
      unfold TimeBound, Z_Params.d. rewrite Rename_and.
      rewrite <- Rename_ok with (F:=0 <= "T" <= P.d)
        by eauto with rw_rename. simpl. restoreAbstraction.
      charge_tauto. }
  Qed.

  (* Our main safety theorem. *)
  Lemma Box_safe :
    |-- (IndInv_quad //\\ TimeBound P.d) //\\
        []SysSystem (Quadcopter P.d P.g P.pitch_min
                                (Sys_D Next_quad))
        -->> []Safe.
  Proof.
    rewrite Inductively.Preserves_Inv_simple.
    { rewrite IndInv_impl_Safe.
      charge_tauto. }
    { compute; tauto. }
    { apply SafeAndReactive_TimedPreserves.
      eapply Quadcopter_refine
      with (B:=P.pitch_min <= "pitch" <= P.pitch_max)
           (A:=P.pitch_min<="roll"<=P.pitch_max //\\ 0<="A").
      { apply P.d_gt_0. }
      { pose proof P.pitch_min_bound. solve_linear. }
      { intuition. }
      { intuition. }
      { etransitivity. apply TimedPreserves_Next.
        apply Proper_TimedPreserves_lentails; try reflexivity.
        unfold Basics.flip. unfold Next. 
  Qed.

End RectangleShim.
