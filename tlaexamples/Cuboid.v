Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.ArithFacts.
Require Import TLA.EnabledLemmas.
Require Import TLA.DifferentialInduction.
Require Import TLA.ProofRules.
Require Import Examples.System2.
Require Import Examples.UpperLower.
Require Import Examples.TheBox.
Require Import ChargeTactics.Lemmas.
Require Import Coq.Reals.Reals.
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

Module Cuboid (Import P : CuboidParams).
  Open Scope HP_scope.

  Module XZ_Params <: BoxParams.
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
  End XZ_Params.

  Module Y_Params <: UpperLowerParams.
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
(*
      unfold amin, P.amin_Y.
      pose proof P.angle_min_bound.
      assert (tan P.angle_min < 0)%R
        by (apply tan_lt_0; solve_linear).
      pose proof P.amin_Z_lt_0.
      pose proof P.g_gt_0.
      pose proof P.amin_Z_lt_g.
      assert (0 < / cos angle_min)%R
        by (apply RIneq.Rinv_0_lt_compat;
            apply cos_gt_0; solve_linear).
      unfold Rdiv. solve_nonlinear.
*)
    Qed.
    Definition ubv := P.ubv_Y.
    Definition ub_ubv := P.ub_ubv_Y.
    Definition ubv_gt_amin_d := P.ubv_Y_gt_amin_d.
  End Y_Params.

  Module XZ := Box XZ_Params.
  Module Y := UpperLower Y_Params.

  Let rename_y : RenameList :=
    {{ "y" ~> "y" & "v" ~> "vy" & "a" ~> "ay" }}%rn.

  Let rename_polar : RenameList :=
    {{ "ay" ~> "A"*sin("roll") &
       "a" ~> "A"*cos("roll") }}%rn.

  Definition Next_no_roll_constraint : ActionFormula :=
    SysRename rename_polar (deriv_term_RenameList rename_polar)
              (SysCompose
                 (SysRename rename_y
                            (deriv_term_RenameList rename_y)
                            Y.Next)
                 XZ.Next).

  Definition RollConstraint : Formula :=
      P.angle_min <= "roll" <= P.angle_max.

  (* The full system, with roll input constraints. *)
  Definition Next : ActionFormula :=
    SysCompose Next_no_roll_constraint
               (Sys (next RollConstraint) ltrue d).

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

  Definition aw : Term := SqrtT("ax"*"ax" + ("az" + g)*("az" + g)).

  Definition RollConstraintRect : Formula :=
    0 < aw //\\
    P.angle_min <= ArctanT ("ay"/aw) <= P.angle_max.

  Definition YWConstraint :=
    Rename rename_y Y.Constraint //\\
    XZ.XZConstraint.

  Lemma yw_constraint_refinement :
    YWConstraint |-- RollConstraintRect.
  Proof.
    unfold YWConstraint, XZ.XZConstraint.
    repeat rewrite <- Rename_ok by rw_side_condition.
    breakAbstraction. intros.
    generalize dependent (Stream.hd tr). intros.
    pose proof XZ.X_Params.amin_lt_0.
    pose proof P.angle_min_bound.
    pose proof P.amin_Z_lt_g.
    unfold Y_Params.amin, amin_Y,
    XZ.X_Params.amin, XZ_Params.amin_X,
    XZ.Z_Params.amin, XZ_Params.amin_Z, amin_X in *.
    split.
    { apply sqr_lt_compat.
      { reflexivity. }
      { apply sqrt_pos. }
      { rewrite_real_zeros. rewrite sqrt_sqrt.
        { apply RIneq.Rplus_le_lt_0_compat.
          { solve_nonlinear. }
          { apply Rmult_0_lt; solve_linear. } }
        { solve_nonlinear. } } }
    { apply arctan_constraint_refinement
      with (b:=(-(amin_Z + g))%R).
      { apply sqr_le_compat.
        { assert (/ cos angle_min > 0)%R
            by (pose proof (cos_gt_0 angle_min) as Hmin;
                specialize_arith_hyp Hmin; solve_linear).
          unfold Rdiv. solve_nonlinear. }
        { apply sqrt_pos. }
        { rewrite sqrt_sqrt.
          { solve_nonlinear. }
          { solve_nonlinear. } } }
      { solve_linear. }
      { solve_linear. }
      { assumption. } }
  Qed.
  
  Definition SphericalBounds : Formula :=
    0 <= "A" //\\ --PI/2 <= "roll" <= PI/2.

  Lemma rect_input_refines_polar :
    Rename rename_polar
           (Rename XZ.rename_polar RollConstraintRect)
    //\\ SphericalBounds |--
    RollConstraint.
  Proof.
    rewrite <- Rename_ok by rw_side_condition.
    simpl rename_formula.
    breakAbstraction. intros.
    generalize dependent (Stream.hd tr). intros.
    match goal with
    | [ _ : context [ sqrt ?e ] |- _ ]
      => replace e with  (Rsqr (s "A" * cos (s "roll")))%R in *
    end.
    { assert (- PI/ 2 < s "roll" < PI / 2)%R.
      { decompose [and] H.
        rewrite <- sqrt_0 in H2. apply sqrt_lt_0_alt in H2.
        unfold Rsqr in *.
        destruct H1; destruct H6.
        { solve_linear. }
        { rewrite H5 in H2.
          change (PI * / 2)%R with (PI / 2)%R in *.
          rewrite cos_PI2 in H2. rewrite Rmult_0_r in H2.
          unfold Rsqr in *. solve_linear. }
        { rewrite <- H1 in H2. rewrite Rminus_0_l in H2.
          change (- PI * / 2)%R with (- PI / 2)%R in *.
          assert (eq (- PI / 2) (- (PI / 2)))%R by solve_linear.
          rewrite H6 in H2. rewrite cos_neg in H2.
          rewrite cos_PI2 in H2. rewrite Rmult_0_r in H2.
          unfold Rsqr in *. solve_linear. }
        { rewrite H5 in H2.
          change (PI * / 2)%R with (PI / 2)%R in *.
          rewrite cos_PI2 in H2. rewrite Rmult_0_r in H2.
          unfold Rsqr in *. solve_linear. } }
      { match goal with
        | [ _ : context [ atan ?e ] |- _ ]
          => replace e with  (tan (s "roll")) in *
        end.
        { rewrite <- atan_tan with (x:=s "roll");
          [ tauto | ]. assumption. }
        { unfold tan, Rdiv.
          assert (0 < cos (s "roll"))%R
            by (apply cos_gt_0; solve_linear).
          rewrite sqrt_Rsqr.
          { field. split; [ solve_linear | ].
            decompose [and] H. rewrite <- sqrt_0 in H4.
            apply sqrt_lt_0_alt in H4. unfold Rsqr in *.
            clear -H4 H1. solve_nonlinear. }
          { solve_nonlinear. } } } }
    { unfold Rsqr, XZ_Params.g.
      transitivity ((Rsqr (s "A" * cos (s "roll")))*
                 ((Rsqr (sin (s "pitch"))) + (Rsqr (cos (s "pitch")))))%R.
      { rewrite sin2_cos2. rewrite Rmult_1_r. unfold Rsqr. reflexivity. }
      {  unfold Rsqr. field. } }
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

  Lemma spherical_predicated_witness_function :
    exists f,
    forall xs,
      List.forallb (fun x => if String.string_dec x "A"
                             then false else true) xs =
      true ->
      List.forallb (fun x => if String.string_dec x "roll"
                             then false else true) xs =
      true ->
      predicated_witness_function rename_polar f xs
                                  XZ.PolarBounds SphericalBounds.
  Proof.
    exists
      (fun st x =>
         if Req_EM_T (st "a") R0
         then if Rle_dec R0 (st "ay")
              then if String.string_dec x "A"
                   then st "ay"
                   else if String.string_dec x "roll"
                        then PI/2
                        else st x
              else if String.string_dec x "A"
                   then -(st "ay")
                   else if String.string_dec x "roll"
                        then -(PI/2)
                        else st x
         else let witness :=
                  proj1_sig
                    (rectangular_to_polar (st "a")
                                          (st "ay")) in
              if String.string_dec x "A"
              then fst witness
              else if String.string_dec x "roll"
                   then snd witness
                   else st x)%R.
    intros.
    split.
    { unfold witness_function. intros. simpl.
      rewrite List.forallb_forall in *.
      specialize (H "A").
      specialize (H0 "roll").
      repeat match goal with
             | [ |- context [if ?e then _ else _] ]
               => destruct e; simpl
             end; subst; simpl;
      try solve [destruct (String.string_dec "A" "A");
                  intuition congruence |
                 destruct (String.string_dec "roll" "roll");
                   intuition congruence ].
      { rewrite sin_PI2. solve_linear. }
      { rewrite sin_neg. rewrite sin_PI2.
        unfold Value. solve_linear. }
      { destruct (rectangular_to_polar (st "a")
                                       (st "ay")).
        simpl. tauto. }
      { rewrite cos_PI2. rewrite_real_zeros. assumption. }
      { rewrite cos_neg. rewrite cos_PI2. rewrite_real_zeros. assumption. }
      { destruct (rectangular_to_polar (st "a")
                                       (st "ay")).
        simpl. unfold Value. solve_linear. } }
    { intros. destruct tr. simpl in *.
      repeat destruct_ite.
      { solve_linear. }
      { solve_linear. }
      { destruct (rectangular_to_polar (s "a")
                                       (s "ay")).
        simpl. split; [ tauto | ].
        assert (-PI/2 < snd x < PI/2)%R.
        { apply cos_pos.
          { solve_nonlinear. }
          { solve_linear. } }
        { solve_linear. } } }
  Qed.

  Lemma Rename_polar_y_noop :
    Rename XZ.rename_polar (Rename rename_y Y.Constraint) -|-
           Rename rename_y Y.Constraint.
  Proof.
    rewrite <- Rename_ok. simpl.
    rewrite <- Rename_ok. reflexivity.
    eauto with rw_rename.
    unfold RenameMapOk. is_st_term_list.
    is_st_term_list.
    repeat split. 
    intros. is_st_term_list.
    eauto with rw_rename.
  Qed.

  Theorem SysNeverStuck_Next : |-- SysNeverStuck d IndInv Next.
  Proof.
    eapply SysNeverStuck_Sys;
    [ pose proof d_gt_0 ; solve_linear | | ].
    { rewrite <- disjoint_state_enabled.
      { charge_split.
        { charge_clear. enable_ex_st.
          pose proof P.d_gt_0.
          unfold Y.Vel.V.d, Y.V.d, Y_Params.d. 
          exists R0. solve_linear. }
        { pose proof rect_input_refines_polar.
          apply next_st_formula_entails in H;
            [ | simpl; tauto | simpl; tauto ].
          rewrite <- H. clear H.
          rewrite Rename_ok by eauto with rw_rename.
          rewrite next_And. rewrite next_Rename.
          (* Annoying manipulation. *)
          rewrite landC. charge_revert.
          charge_clear. charge_intros.
          rewrite <- landA. rewrite <- Rename_and.
          pose proof spherical_predicated_witness_function.
          destruct H.
          rewrite next_Rename.
          rewrite <- Rename_ok with (m:=to_RenameMap XZ.rename_polar)
            by eauto with rw_rename.
          eapply subst_enabled_predicated_witness
          with (f:=x) (P:=XZ.PolarBounds).
          { compute; tauto. }
          { compute; tauto. }
          { apply get_vars_next_state_vars; reflexivity. }
          { apply H; reflexivity. }
          { clear. pose proof yw_constraint_refinement.
            apply next_st_formula_entails in H;
              [ | simpl; tauto | simpl; tauto ].
            rewrite Rename_ok
            with (m:=to_RenameMap XZ.rename_polar) (F:=(next RollConstraintRect))
              by eauto with rw_rename.
            rewrite <- H. clear.
            unfold YWConstraint. rewrite next_And.
            (* Very brittle match ahead. Basically
               just want to group the X monitor
               with the X constraint and the Y monitor
               with the Y constraint. *)
            rewrite Rename_and. repeat rewrite <- next_Rename.
            repeat rewrite landA.
            match goal with
            |- _ |-- Enabled (?Y //\\ ?W //\\ ?YC //\\ ?WC1 //\\ ?WC2) =>
            assert (Y //\\ W //\\ YC //\\ WC1 //\\ WC2 -|-
                    (Y //\\ YC) //\\ (W //\\ WC1 //\\ WC2))
              as H by (split; charge_tauto);
              rewrite H; clear H
            end.
            rewrite <- next_st_formula_entails
            with (A:=Rename rename_y Y.Constraint)
                   (B:=Rename XZ.rename_polar (Rename rename_y Y.Constraint));
              [ | compute; tauto | compute; tauto | rewrite Rename_polar_y_noop; reflexivity ].
            rewrite <- disjoint_state_enabled.
            { charge_split.
              { rewrite Rename_ok by eauto with rw_rename.
                rewrite next_Rename. rewrite <- Rename_and.
                apply landL1.
                pose proof y_witness_function. destruct H.
                eapply subst_enabled with (f:=x).
                { apply get_vars_next_state_vars; reflexivity. }
                { apply H; reflexivity. }
                { clear. pose proof Y.SysNeverStuck_Discr.
                  charge_clear.
                  etransitivity; [ apply H |
                                   apply Proper_Enabled_lentails ].
                  charge_tauto. } }
              { rewrite next_Rename. charge_clear.
                apply XZ.SysNeverStuck_Discr. } }
            { repeat rewrite next_Rename.
              repeat rewrite <- Rename_ok by eauto with rw_rename.
              rewrite <- Rename_ok
                by (eauto with rw_rename || simpl; repeat split; is_st_term_list).
              apply formulas_disjoint_state; reflexivity. } } } }
      { apply formulas_disjoint_state; reflexivity. } }
    { admit. (** Provable, but we won't worry about it *) }
  Qed.

  Definition Safe : StateFormula :=
    Rename rename_polar
           (Rename rename_x X.Safe //\\ Rename rename_y Y.Safe).

  Lemma IndInv_impl_Safe : IndInv //\\ TimeBound P.d |-- Safe.
  Proof with (eauto with rw_rename).
    unfold Safe. rewrite Rename_and.
    charge_split.
    { rewrite <- X.IndInv_impl_Safe.
      unfold IndInv, TimeBound.
      repeat rewrite Rename_and.
      charge_split; [ charge_assumption | ].
      charge_revert. charge_clear.
      repeat rewrite <- (Rename_ok _ rename_x)...
      repeat rewrite <- Rename_ok...
      simpl. restoreAbstraction. charge_tauto. }
    { rewrite <- Y.IndInv_impl_Safe.
      unfold IndInv, TimeBound.
      repeat rewrite Rename_and.
      charge_split; [ charge_assumption | ].
      charge_revert. charge_clear.
      repeat rewrite <- (Rename_ok _ rename_y)...
      repeat rewrite <- Rename_ok...
      simpl. restoreAbstraction. charge_tauto. }
  Qed.

  Lemma Box_safe :
    |-- (IndInv //\\ TimeBound P.d) //\\ []Next -->> []Safe.
  Proof.
    rewrite <- IndInv_impl_Safe.
    eapply Inductively.Preserves_Inv.
    3: apply TimedPreserves_Next.
    - compute; tauto.
    - apply always_tauto. charge_tauto.
  Qed.

End Box.
