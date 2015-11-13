Require Import Coq.Reals.Reals.
Require Import TLA.TLA.
Require Import TLA.ArithFacts.
Require Import TLA.EnabledLemmas.
Require Import TLA.DifferentialInduction.
Require Import TLA.ProofRules.
Require Import Examples.System2.
Require Import Examples.UpperLower.
Require Import ChargeTactics.Lemmas.
Require Import Coq.Reals.R_sqrt.
Require Import Coq.Reals.Ratan.
Require Import Coq.Reals.Rtrigo1.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

Module Type BoxParams.
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
  Axiom ub_ubv_X :
    (ubv_X*d + ubv_X*ubv_X*(0 - /2)*(/amin_X) <= ub_X)%R.
  Axiom ub_ubv_Z :
    (ubv_Z*d + ubv_Z*ubv_Z*(0 - /2)*(/amin_Z) <= ub_Z)%R.
  Axiom ubv_X_gt_amin_d : (ubv_X >= -amin_X*d)%R.
  Axiom ubv_Z_gt_amin_d : (ubv_Z >= -amin_Z*d)%R.

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
  End X_Params.

  Module Z_Params <: UpperLowerParams.
    Definition ub := P.ub_Z.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin_Z.
    Definition amin_lt_0 := P.amin_Z_lt_0.
    Definition ubv := P.ubv_Z.
    Definition ub_ubv := P.ub_ubv_Z.
    Definition ubv_gt_amin_d := P.ubv_Z_gt_amin_d.
  End Z_Params.

  Module X := UpperLower X_Params.
  Module Z := UpperLower Z_Params.

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
      P.pitch_min <= "pitch" <= P.pitch_max.

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

(* The following helps generate code. *)
(*
Definition shift (ub lb:R) (x:Var) : list (Var*Term) :=
  (x,x - ((lb + ub)/2))::nil.
Variable ubx lbx uby lby ubvx ubvy lbvx lbvy : R.

Goal (Rename (to_RenameMap (shift ubx lbx "x"))
        (Rename (to_RenameMap (shift uby lby "z"))
           (Rename (to_RenameMap (shift ubvx lbvx "vx"))
              (Rename (to_RenameMap (shift ubvy lbvy "vy"))
                      (Prog SpecR))))) |-- TRUE.
  unfold SpecR. rewrite_rename_pf SpecPolarR.
  rewrite Prog_SysCompose. rewrite Prog_SysRename.
  unfold SpecRectR. rewrite_rename_pf X_SpecR.
  rewrite_rename_pf Z_SpecR. rewrite Prog_SysCompose.
  repeat rewrite Prog_SysRename. unfold X.SpecR, Z.SpecR.
  repeat rewrite Prog_SysCompose.
  unfold X.Vel.SpecR, X.Position.SpecR,
  Z.Vel.SpecR, Z.Position.SpecR.
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
  unfold X.Position.Monitor.Ctrl, Z.Position.Monitor.Ctrl,
  X.Vel.Vel.Ctrl, Z.Vel.Vel.Ctrl.
  Rename_rewrite.
  repeat rewrite X.Vel.Vel.Rename_SafeAcc
    by rw_side_condition.
  repeat rewrite X.Vel.Vel.Rename_Default
    by rw_side_condition.
  repeat rewrite Z.Vel.Vel.Rename_SafeAcc
    by rw_side_condition.
  repeat rewrite Z.Vel.Vel.Rename_Default
    by rw_side_condition.
  repeat rewrite X.Position.Monitor.Rename_SafeAcc
    by rw_side_condition.
  repeat rewrite X.Position.Monitor.Rename_Default
    by rw_side_condition.
  repeat rewrite Z.Position.Monitor.Rename_SafeAcc
    by rw_side_condition.
  repeat rewrite Z.Position.Monitor.Rename_Default
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
SecondDerivUtil.tdist "vx" ("a"!*sin("pitch"!)) P.d = 0.
*)

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

  Definition PolarBounds : Formula :=
    0 <= "a" //\\ --PI <= "pitch" <= PI.

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

  Lemma polar_predicated_witness_function :
    exists f,
    forall xs,
      List.forallb (fun x => if String.string_dec x "a"
                             then false else true) xs =
      true ->
      List.forallb (fun x => if String.string_dec x "pitch"
                             then false else true) xs =
      true ->
      predicated_witness_function
        (to_RenameMap rename_polar) f xs ltrue PolarBounds.
  Proof.
    exists
      (fun st x =>
         let witness :=
             proj1_sig
               (rectangular_to_polar (st "az" + P.g)
                                     (st "ax")) in
         if String.string_dec x "a"
         then fst witness
         else if String.string_dec x "pitch"
              then snd witness
              else st x)%R.
    unfold predicated_witness_function, witness_function.
    split.
    { intros. simpl.
      rewrite List.forallb_forall in *.
      specialize (H "a").
      specialize (H0 "pitch").
      repeat match goal with
             | [ |- context [if ?e then _ else _] ]
               => destruct e; simpl
             end; subst; simpl.
      { destruct (rectangular_to_polar (st "az" + P.g)
                                       (st "ax")).
        simpl. tauto. }
      { destruct (rectangular_to_polar (st "az" + P.g)
                                       (st "ax")).
        simpl. unfold Value. solve_linear. }
      { destruct (String.string_dec "a" "a");
        intuition congruence. }
      { destruct (String.string_dec "pitch" "pitch");
        intuition congruence. }
      { reflexivity. } }
    { intros. destruct tr. simpl.
      destruct (rectangular_to_polar (s "az" + P.g)
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
    match goal with
    | [ _ : context [ atan ?e ] |- _ ]
      => replace e with  (tan (s "pitch")) in *
    end.
    { rewrite <- atan_tan with (x:=s "pitch");
      [ tauto | ].
      apply cos_pos; [ | solve_linear ].
      generalize dependent (cos (s "pitch")).
      solve_nonlinear. }
    { unfold tan, Rdiv. field.
      split. solve_linear. decompose [and] H. clear H.
      generalize dependent (cos (s "pitch")). intros.
      solve_nonlinear. }
  Qed.

  Lemma SysNeverStuck_Discr :
    |-- Enabled (Sys_D Next //\\
                       Rename rename_polar (next XZConstraint) //\\ next PolarBounds).
  Proof.
    unfold Sys_D.
    pose proof rect_input_refines_polar.
    apply next_st_formula_entails in H;
      [ | simpl; tauto | simpl; tauto ].
    rewrite <- H. clear H.
    pose proof xy_constraint_refinement.
    apply next_st_formula_entails in H;
      [ | simpl; tauto | simpl; tauto ].
    rewrite next_And. rewrite next_Rename.
    rewrite <- H. clear H.
    match goal with
      |- |-- Enabled ((?S //\\ ?X) //\\ ?X) =>
      assert ((S //\\ X) //\\ X -|- S //\\ (X //\\ X))
        as H by (split; charge_tauto); rewrite H; clear H
    end.
    rewrite <- land_dup.
    rewrite Rename_ok by eauto with rw_rename.
    rewrite <- landA. rewrite <- Rename_and.
    unfold XZConstraint. rewrite next_And. repeat rewrite next_Rename.
    rewrite <- Rename_ok with (m:=to_RenameMap rename_x) by eauto with rw_rename.
    rewrite <- Rename_ok with (m:=to_RenameMap rename_z) by eauto with rw_rename.
    pose proof polar_predicated_witness_function.
    destruct H.
    eapply subst_enabled_predicated_witness_simple_noenv
    with (f:=x).
    { simpl; tauto. }
    { apply get_vars_next_state_vars; reflexivity. }
    { apply H; reflexivity. }
    { clear.
      (* Very brittle match ahead. Basically
               just want to group the X monitor
               with the X constraint and the Z monitor
               with the Z constraint. *)
      repeat rewrite landA.
      match goal with
        |- _ |-- Enabled (?X //\\ ?Z //\\ ?XC //\\ ?ZC) =>
        assert (X //\\ Z //\\ XC //\\ ZC -|-
                  (X //\\ XC) //\\ (Z //\\ ZC))
          as H by (split; charge_tauto);
          rewrite H; clear H
      end.
      rewrite <- disjoint_state_enabled.
      { charge_split.
        { pose proof x_witness_function. destruct H.
          repeat rewrite Rename_ok with (m:=to_RenameMap rename_x) by eauto with rw_rename.
          rewrite <- Rename_and.
          eapply subst_enabled_noenv with (f:=x).
          { apply get_vars_next_state_vars; reflexivity. }
          { apply H; reflexivity. }
          { clear. pose proof X.SysNeverStuck_Discr.
            charge_clear.
            etransitivity; [ apply H |
                             apply Proper_Enabled_lentails ].
            charge_tauto. } }
        { pose proof z_witness_function. destruct H.
          repeat rewrite Rename_ok with (m:=to_RenameMap rename_z) by eauto with rw_rename.
          rewrite <- Rename_and.
          eapply subst_enabled_noenv with (f:=x).
          { apply get_vars_next_state_vars; reflexivity. }
          { apply H; reflexivity. }
          { clear. pose proof Z.SysNeverStuck_Discr.
            charge_clear.
            etransitivity; [ apply H |
                             apply Proper_Enabled_lentails ].
            charge_tauto. } } }
      { apply formulas_disjoint_state; reflexivity. } }
  Qed.

  Theorem SysNeverStuck_Next : |-- SysNeverStuck P.d IndInv Next.
  Proof.
    eapply SysNeverStuck_Sys;
    [ pose proof P.d_gt_0 ; solve_linear | | ].
    { rewrite <- disjoint_state_enabled.
      { charge_split.
        { charge_clear. enable_ex_st.
          pose proof P.d_gt_0.
          unfold X.Vel.V.d, X.V.d, X_Params.d. 
          exists R0. solve_linear. }
        { rewrite land_dup with (A:=next InputConstraint).
          pose proof rect_input_refines_polar.
          apply next_st_formula_entails in H;
            [ | simpl; tauto | simpl; tauto ].
          rewrite <- H at 2. clear H.
          pose proof xy_constraint_refinement.
          apply next_st_formula_entails in H;
            [ | simpl; tauto | simpl; tauto ].
          rewrite next_And. rewrite next_Rename.
          rewrite <- H. clear H.
          charge_clear. pose proof SysNeverStuck_Discr.
          unfold Sys_D in *. repeat rewrite landA in H.
          apply H. } }
      { apply formulas_disjoint_state; reflexivity. } }
    { admit. (** Provable, but we won't worry about it *) }
  Qed.

  Definition Safe : StateFormula :=
    Rename rename_polar
           (Rename rename_x X.Safe //\\ Rename rename_z Z.Safe).

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
    { rewrite <- Z.IndInv_impl_Safe.
      unfold IndInv, TimeBound.
      repeat rewrite Rename_and.
      charge_split; [ charge_assumption | ].
      charge_revert. charge_clear.
      repeat rewrite <- (Rename_ok _ rename_z)...
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
