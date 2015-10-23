Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rtrigo_def.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import Examples.DiffEqSolutions.
Require Import Coq.Lists.List.

Lemma concave_quadratic_ineq :
    forall a b c x,
      ((-b + R_sqrt.sqrt (b*b - 4*a*c))*/2*/a <= x
       <= (-b - R_sqrt.sqrt (b*b - 4*a*c))*/2*/a ->
       a < 0 ->
       0 <= b*b - 4*a*c ->
       a*x*x + b*x + c >= 0)%R.
  Admitted.

  Lemma quadratic_axis_of_symmetry :
    forall a b c,
      (0 <= b*b - 4*a*c ->
       a < 0 ->
       (- b + R_sqrt.sqrt (b*b - 4*a*c))*/2*/a <= -b*/2*/a
       <= (- b - R_sqrt.sqrt (b*b - 4*a*c))*/2*/a)%R.
  Proof.
    intros. pose proof (R_sqrt.sqrt_pos (b*b - 4*a*c)).
    generalize dependent (R_sqrt.sqrt (b*b - 4*a*c)).
    intros. assert (eq (a * /a) 1)%R by solve_linear.
    generalize dependent (/a)%R. intros.
    solve_nonlinear.
  Qed.

  Require Import Coq.Reals.RIneq.
  Lemma SafeAcc_quadratic :
    forall y v a t ub amin,
      (amin < 0 ->
       t <> 0 ->
       (-t*t)*a*a + (amin*t*t-2*v*t)*a +
       (2*amin*y - 2*amin*ub + 2*amin*v*t - v*v) >= 0 ->
       y + (v*t + /2*a*t*t) + (v + a*t)*(v + a*t)*(-/2)*/amin
       <= ub)%R.
  Proof.
    intros.
    apply Rmult_le_reg_l with (r:=2%R);
      [ solve_linear | ].
    apply Rmult_le_reg_l with (r:=(-amin)%R);
      [ solve_linear | ].
    ring_simplify. simpl. field_simplify. simpl.
    unfold Rdiv in *. solve_nonlinear.
    solve_linear.
  Qed.

  Lemma sqrt_fact :
    forall u y b t v,
      (0 < t ->
       b < 0 ->
       2*b*u <= 2*b*y - v*v ->
       b*t*t + 4*t*v-8*u+8*y <= 0)%R.
  Proof. solve_nonlinear. Qed.

Open Scope HP_scope.
Open Scope string_scope.

Module Type Params.

  Parameter ub : R.
  Parameter d : R.
  Axiom d_gt_0 : (d > 0)%R.

  Parameter amin : R.
  Axiom amin_lt_0 : (amin < 0)%R.

End Params.

Module AbstractShim (Import P : Params).

  (* The distance traveled before stopping when
     applying acceleration amin, starting with
     velocity v. *)
  Definition sdist (v:Term) : Term :=
    (v^^2)*(--(/2)%R)*(/amin)%R.

  (* The distance traveled starting with velocity
   v, acceleration a, traveling for time t. *)
  Definition tdist (v:Term) (a:Term) (t:Term) : Term :=
    v*t + (/2)%R*a*t^^2.

  Definition error (y v : Term) : Term :=
    MAX(y + sdist MAX(v, 0) - ub, 0).

  Definition ExponentiallyStable : Formula :=
    Exists y0 : R, "y" = y0 //\\
    Exists v0 : R, "v" = v0 //\\
    Exists a : R, a > 0 //\\
    Exists b : R, b > 0 //\\
      []error "y" "v" <= a * error y0 v0 * exp(--b * "t").

  (* Convenience functions to say that all variables in a list
   have derivative 0. *)
  Definition AllConstant (vars : list Var) : state->Formula :=
    fun st' => List.fold_right
                 (fun x a => st' x = 0 //\\ a)
                 TRUE vars.

  Definition World : Evolution :=
    fun st' =>
      st' "y" = "v" //\\ st' "v" = "a" //\\ st' "t" = 1 //\\
      AllConstant ("T"::"a"::nil) st'.

  Definition SafeAcc (a : Term) (d : Term) : Formula :=
    Forall t : R,
      (0 <= t //\\ t <= d) -->>
      "y" + tdist "v" a t + sdist MAX("v" + a*t, 0) <= ub.

  Definition SafeAccZeroOrder (a : Term) (d : Term)
    : Formula :=
    (0 <= "v" + a*d -->>
     "y" + tdist "v" a d + sdist ("v" + a*d) <= ub) //\\
    (("v" + a*d <= 0 //\\ 0 < "v") -->>
     "y" + tdist "v" a (--"v"/a) <= ub).

  Lemma SafeAccZeroOrder_refines :
    forall a,
      SafeAccZeroOrder a d //\\ "y" <= ub //\\ SafeAcc amin d
      |-- SafeAcc a d.
  Proof.
    intros. reason_action_tac.
    pose proof d_gt_0.
    unfold Rbasic_fun.Rmax. destruct_ite.
    - rewrite_real_zeros.
      destruct (RIneq.Rlt_dec 0 (pre "v"))%R.
      + assert (pre "v" + eval_term a pre post * d <= 0)%R
          by solve_nonlinear. intuition.
        assert (eval_term a pre post <> 0%R)
          by solve_nonlinear. intuition.
        eapply Rle_trans; eauto.
        field_simplify; auto. simpl.
        apply Rmult_le_reg_r with (r:=2%R);
          [ solve_linear | ].
        apply Rmult_le_reg_r
        with (r:=(-(eval_term a pre post))%R);
          [ solve_nonlinear | ].
        repeat rewrite Ropp_mult_distr_r_reverse.
        field_simplify; auto. simpl.
        unfold Rdiv. repeat rewrite RMicromega.Rinv_1.
        solve_nonlinear.
      + solve_nonlinear.
    - destruct (RIneq.Rle_dec
                  (pre "v" + eval_term a pre post * d) 0)%R.
      + destruct (RIneq.Rlt_dec 0 (pre "v"))%R.
        * intuition.
          assert (eval_term a pre post <> 0%R)
            by solve_nonlinear. intuition.
          pose proof amin_lt_0.
          assert (amin <> 0%R) by solve_linear.
          destruct
            (RIneq.Rle_dec amin (eval_term a pre post)).
          { eapply Rle_trans; eauto.
            field_simplify; auto. simpl.
            apply Rmult_le_reg_r with (r:=2%R);
              [ solve_linear | ].
            apply Rmult_le_reg_r
            with (r:=(-(eval_term a pre post))%R);
              [ solve_nonlinear | ].
            apply Rmult_le_reg_r with (r:=(-amin)%R);
              [ solve_linear | ].
            repeat rewrite Ropp_mult_distr_r_reverse.
            field_simplify; auto. simpl.
            unfold Rdiv. repeat rewrite RMicromega.Rinv_1.
            clear - r1. solve_nonlinear. }
          { specialize (H6 0%R). specialize_arith_hyp H6.
            revert H6. unfold Rbasic_fun.Rmax.
            repeat destruct_ite; rewrite_real_zeros.
            { solve_linear. }
            { intros. eapply Rle_trans; eauto.
              assert (pre "v"+eval_term a pre post*x > 0)%R
                by solve_linear.
              field_simplify; auto. simpl.
              apply Rmult_le_reg_r with (r:=2%R);
                [ solve_linear | ].
              apply Rmult_le_reg_r
              with (r:=(-(eval_term a pre post))%R);
                [ solve_nonlinear | ].
              apply Rmult_le_reg_r with (r:=(-amin)%R);
                [ solve_linear | ].
              repeat rewrite Ropp_mult_distr_r_reverse.
              field_simplify; auto. simpl.
              unfold Rdiv. repeat rewrite RMicromega.Rinv_1.
              clear - H9 n0 H7 H1 H. solve_nonlinear. } }
        * solve_nonlinear.
      + assert (0 <= pre "v" + eval_term a pre post * d)%R
          as Hvd by solve_linear. intuition.
        destruct
            (RIneq.Rle_dec amin (eval_term a pre post)).
        { eapply Rle_trans; eauto.
          pose proof amin_lt_0.
          assert (amin <> 0%R) by solve_linear.
          assert (0 <= pre "v" + eval_term a pre post * x)%R
            as Hvx by solve_linear.
          apply Rmult_le_reg_l with (r:=(-amin)%R);
            [ solve_linear | ].
          ring_simplify; simpl; field_simplify; auto; simpl.
          apply Rmult_le_reg_r with (r:=2%R);
            [ solve_linear | ].
          field_simplify; simpl.
          unfold Rdiv. repeat rewrite RMicromega.Rinv_1.
          clear - Hvd Hvx H4 r. solve_nonlinear. }
        { pose proof amin_lt_0.
          assert (amin <> 0%R) by solve_linear.
          specialize (H6 0%R). specialize_arith_hyp H6.
          revert H6. unfold Rbasic_fun.Rmax.
          repeat destruct_ite; rewrite_real_zeros.
          { intros. eapply Rle_trans; eauto.
            assert (pre "v"+eval_term a pre post*x > 0)%R
              by solve_linear.
            field_simplify; auto. simpl.
            apply Rmult_le_reg_r with (r:=2%R);
              [ solve_linear | ].
            apply Rmult_le_reg_r
            with (r:=(-(eval_term a pre post))%R);
              [ solve_nonlinear | ].
            apply Rmult_le_reg_r with (r:=(-amin)%R);
              [ solve_linear | ].
            repeat rewrite Ropp_mult_distr_r_reverse.
            field_simplify; auto. simpl.
            unfold Rdiv. repeat rewrite RMicromega.Rinv_1.
            clear - H8 r H5 n1 H. solve_nonlinear. }
          { intros. eapply Rle_trans; eauto.
            assert (pre "v"+eval_term a pre post*x > 0)%R
              by solve_linear.
            field_simplify; auto. simpl.
            apply Rmult_le_reg_r with (r:=2%R);
              [ solve_linear | ].
            apply Rmult_le_reg_r
            with (r:=(-(eval_term a pre post))%R);
              [ solve_nonlinear | ].
            apply Rmult_le_reg_r with (r:=(-amin)%R);
              [ solve_linear | ].
            repeat rewrite Ropp_mult_distr_r_reverse.
            field_simplify; auto. simpl.
            unfold Rdiv. repeat rewrite RMicromega.Rinv_1.
            clear - H8 n2 H5 n1 H. solve_nonlinear. } }
  Qed.

  Definition SafeAccZeroOrderSolved (a : Term) (d : Term)
    : Formula :=
      (--"v"/d < a //\\
       a <=
       (--(amin*d*d-2%R*"v"*d) -
        SqrtT ((amin*d*d-2%R*"v"*d)*(amin*d*d-2%R*"v"*d) -
               4%R*(--d*d)*(2%R*amin*"y"-2%R*amin*ub +
                            2%R*amin*"v"*d-"v"*"v")))
        * /2%R * /(--d*d)) \\//
      (a <= --"v"/d //\\ 0 < "v" //\\
       a <= "v"*"v"/(2*("y"-ub))) \\//
      (a <= --"v"/d //\\ "v" <= 0).

  Lemma SafeAccZeroOrderSolved_refines :
    forall a,
      SafeAccZeroOrderSolved a d //\\ SafeAcc amin d
      |-- SafeAccZeroOrder a d.
  Proof.
    intros. reason_action_tac.
    pose proof d_gt_0.
    pose proof amin_lt_0.
    split.
    - intuition.
      + rewrite Rminus_0_l. repeat rewrite Rmult_1_r.
        repeat rewrite <- Rmult_assoc.
        apply SafeAcc_quadratic.
        * exact amin_lt_0.
        * solve_linear.
        * match goal with
            |- (?a*_*_ + ?b*_ + ?c >= _)%R
            => pose (a2:=a); pose (a1:=b); pose (a0:=c)
          end.
          assert (0 <= a1*a1 - 4*a2*a0)%R as Hsqrt_ge_0.
          { rewrite_real_zeros. intros.
            pose proof amin_lt_0. unfold a1, a2, a0.
            specialize (H4 0%R). specialize_arith_hyp H4.
            revert H4. unfold Rbasic_fun.Rmax.
            repeat destruct_ite; rewrite_real_zeros.
            { revert r. rewrite_real_zeros. intros.
              pose proof amin_lt_0. unfold a1, a2, a0.
              clear - r H4 H0 H.
              z3_solve; admit. }
            { revert n. rewrite_real_zeros. intros.
              pose proof amin_lt_0. unfold a1, a2, a0.
              clear - n H4 H0 H.
              z3_solve; admit. } }
          apply concave_quadratic_ineq.
          { split.
            { pose proof (quadratic_axis_of_symmetry a2 a1 a0)
                as Hsym.
              assert (- d * d < 0)%R by (z3_solve; admit).
              specialize_arith_hyp Hsym.
              destruct Hsym as [Hsym1 Hsym2]. 
              eapply Rle_trans; eauto.
              unfold a0, a1, a2.
              apply Rmult_le_reg_l with (r:=2%R);
                [ solve_linear | ].
              apply Rmult_le_reg_l with (r:=(d*d)%R);
                [ solve_linear | ].
              repeat rewrite Ropp_mult_distr_l_reverse.
              rewrite <- Ropp_inv_permute; [ | solve_linear].
              field_simplify; [ | solve_linear ].
              simpl. unfold Rdiv. rewrite Rinv_1.
              pose proof amin_lt_0. solve_nonlinear. }
            { eapply Rle_trans; eauto.
              repeat rewrite Rminus_0_l.
              apply RIneq.Rle_refl. } }
          { z3_solve; admit. }
          { exact Hsqrt_ge_0. }
      + specialize (H4 0%R). specialize_arith_hyp H4.
        revert H4. unfold Rbasic_fun.Rmax.
        repeat destruct_ite; rewrite_real_zeros.
        * z3_solve; admit.
        * z3_solve; admit.
      + specialize (H4 0%R). specialize_arith_hyp H4.
        revert H4. unfold Rbasic_fun.Rmax.
        repeat destruct_ite; rewrite_real_zeros.
        { z3_solve; admit. }
        { z3_solve; admit. }
    - intuition.
      + z3_solve; admit.
      + specialize (H4 0%R). specialize_arith_hyp H4.
        revert H4. unfold Rbasic_fun.Rmax.
        repeat destruct_ite; rewrite_real_zeros.
        * z3_solve; admit.
        * z3_solve; admit.
      + solve_linear.
  Qed.

(*
    Forall t : R,
      (0 <= t //\\ t <= d) -->>
      (0 <= "v" + a*t -->>
       a <= (SqrtT (amin*(amin*t^^2+4*t*"v"-8*ub+8*"y")) +
             amin*t-2*"v")*(/2)%R*(/t)%R) //\\
      ("v" + a*t <= 0 -->>
       a <= 2*(ub - "y" - "v"*t)*(/t)*(/t)).*)

(*
  Lemma lower_bound_irrelevant :
    forall v a t,
      0 <= v + a*t ->
  *)

  Lemma axis_symmetry_SafeAcc :
    forall a b v t,
      (t > 0 ->
       a*t >= -v ->
       b <= 0 ->
       2*t*a >= b*t-v*2)%R.
  Proof. solve_nonlinear. Qed.

  Require Import TLA.ArithFacts.
  Lemma SafeAccEquiv_refines :
    forall a d,
      SafeAccEquiv a d //\\ SafeAcc amin d |-- SafeAcc a d.
  Proof.
    intros. reason_action_tac.
    destruct (RIneq.Req_dec x R0).
    { subst. intuition. specialize (H2 R0).
      specialize_arith_hyp H2. revert H2.
      unfold Rbasic_fun.Rmax.
      repeat destruct_ite; rewrite_real_zeros;
      solve_linear. }
    unfold Rbasic_fun.Rmax.
    destruct_ite.
    - rewrite_real_zeros. intuition.
      specialize (H2 x). intuition.
      assert (eq (x*/x) 1)%R by solve_linear.
      generalize dependent (/x)%R. intros.
      z3_solve; admit.
    - intuition. specialize (H2 x).
      intuition. specialize_arith_hyp H2.
      rewrite Rminus_0_l. repeat rewrite Rmult_1_r.
      repeat rewrite <- Rmult_assoc.
      apply SafeAcc_quadratic.
      + exact amin_lt_0.
      + solve_linear.
      + match goal with
        |- (?a*_*_ + ?b*_ + ?c >= _)%R
        => pose (a2:=a); pose (a1:=b); pose (a0:=c)
        end.
        assert (0 <= a1*a1 - 4*a2*a0)%R as Hsqrt_ge_0.
        { specialize (H3 R0). specialize_arith_hyp H3.
          revert H3. unfold Rbasic_fun.Rmax.
          repeat destruct_ite; rewrite_real_zeros.
          { revert r. rewrite_real_zeros. intros.
            pose proof amin_lt_0. unfold a1, a2, a0.
            clear - r H3 H0 H.
            z3_solve; admit. }
          { revert n0. rewrite_real_zeros. intros.
            pose proof amin_lt_0. unfold a1, a2, a0.
            clear - n0 H3 H0 H.
            z3_solve; admit. } }
        apply concave_quadratic_ineq.
        * split.
          { pose proof (quadratic_axis_of_symmetry a2 a1 a0)
              as Hsym.
            assert (0 < x)%R by solve_linear.
            assert (- x * x < 0)%R by (z3_solve; admit).
            specialize_arith_hyp Hsym.
            destruct Hsym as [Hsym1 Hsym2]. 
            eapply Rle_trans; eauto.
            unfold a0, a1, a2.
            assert (pre "v"+eval_term a pre post*x > 0)%R
              by solve_linear.
            apply Rmult_le_reg_l with (r:=2%R);
              [ solve_linear | ].
            apply Rmult_le_reg_l with (r:=(x*x)%R);
              [ solve_linear | ].
            repeat rewrite Ropp_mult_distr_l_reverse.
            rewrite <- Ropp_inv_permute; [ | solve_linear].
            field_simplify; [ | solve_linear ].
            simpl. unfold Rdiv. rewrite Rinv_1.
            pose proof amin_lt_0. solve_nonlinear. }
          { eapply Rle_trans; eauto.
            repeat rewrite Rminus_0_l.
            reflexivity. }
        * assert (0 < x)%R by solve_linear.
          z3_solve; admit.
        * exact Hsqrt_ge_0.
  Qed.

  Definition AbstractPD (a : Term) : Formula :=
    Exists kP : R, kP < 0 //\\
    Exists kD : R, kD < 0 //\\
      a = kP*MAX("y" - ub, 0) + kD*"v".

  Definition Ctrl (a : Term) : Formula :=
    (SafeAcc a d //\\ a >= amin) \\//
    ((SafeAcc amin d -->> FALSE) //\\
      AbstractPD a).

  Definition Next : Formula :=
    (Continuous World //\\ "t"! - "T"! <= d) \\//
    (Ctrl "a"! //\\ "T"! = "t" //\\
     Unchanged ("t"::"y"::"v"::nil)).

  Definition Init : Formula :=
    Ctrl "a".

  Definition Spec : Formula :=
    Init //\\ []Next.

  Definition IndInv : Formula :=
    SafeAcc "a" (d - ("t" - "T")) //\\ ("t" - "T" <= d).

Definition evolution_entails :=
  Morphisms.pointwise_relation state lentails.

Definition evolution_equiv :=
  Morphisms.pointwise_relation state lequiv.

Ltac zero_deriv_tac v :=
  eapply ContinuousProofRules.zero_deriv
  with (x:=v); [ charge_tauto | solve_linear | ].

Ltac always_imp_tac :=
  match goal with
  | [ |- ?H |-- _ ]
    => match H with
       | context[ []?HH ] =>
         tlaAssert ([]HH);
           [ charge_tauto |
             apply Lemmas.forget_prem; apply always_imp ]
       end
  end.

Ltac exp_pos_tac :=
  match goal with
    |- context [ Rtrigo_def.exp ?x ]
    => pose proof (Exp_prop.exp_pos x)
  end.

Lemma SafeAcc_zero_error :
  forall a t,
    t >= 0 //\\ SafeAcc a t |-- error "y" "v" = 0.
Proof.
  intros. reason_action_tac. intuition.
  unfold Rbasic_fun.Rmax. repeat destruct_ite.
  - reflexivity.
  - specialize (H1 R0). solve_linear.
  - specialize (H1 R0). solve_linear.
Qed.

Lemma error_pos :
  forall y v, |-- error y v >= 0.
Proof.
  breakAbstraction. intros. unfold Rbasic_fun.Rmax.
  repeat destruct_ite; solve_linear.
Qed.

  Theorem exp_stability :
    |-- Spec -->> ExponentiallyStable.
  Proof.
    charge_intros.
    tlaAssert ([]IndInv).
    { eapply discr_indX.
      - tlaIntuition.
      - charge_tauto.
      - unfold Spec, Init, IndInv, Ctrl.
        admit.
      - unfold Next. rewrite Lemmas.land_lor_distr_R.
        apply lorL.
        + zero_deriv_tac "a".
          zero_deriv_tac "T".
          assert (evolution_entails World dbl_int)
              by (red; red; solve_linear).
          rewrite H. clear H. rewrite solve_dbl_int.
          unfold IndInv, SafeAcc. simpl next.
          restoreAbstraction.
          charge_split.
          * apply lforallR. intro.
            charge_intros; reason_action_tac; intuition;
            match goal with
            | [ H : forall _ : R, _ |- _ ]
              => specialize (H (x + post "t" - pre "t")%R)
            end; intuition;
            repeat match goal with
                   | [ H : eq _ _ |- _ ]
                     => rewrite H in *
                   end; solve_linear.
          * solve_linear.
        + unfold Ctrl.
          rewrite Lemmas.land_lor_distr_R.
          rewrite Lemmas.land_lor_distr_L.
          apply lorL.
          * charge_split.
            { unfold IndInv. reason_action_tac.
              intuition;
                repeat match goal with
                       | [ H : eq _ _ |- _ ]
                         => rewrite H in *
                       end;
                match goal with
                | [ H : forall _ : R, _ |- _ ]
                  => solve [specialize (H x); solve_linear]
                end. }
            { pose proof d_gt_0. solve_linear. }
          * admit. }
    { charge_intros. unfold IndInv, ExponentiallyStable.
      apply lexistsR with (x:=1%R).
      charge_split; [ solve_linear | ].
      apply lexistsR with (x:=1%R).
      charge_split; [ solve_linear | ].
      apply Exists_with_st with (t:="y").
      intro y0. charge_intros.
      charge_split; [ solve_linear | ].
      apply Exists_with_st with (t:="v").
      intro v0. charge_intros.
      charge_split; [ solve_linear | ].
      always_imp_tac. charge_intros.
      tlaAssert (error "y" "v" = 0).
      { rewrite <- (SafeAcc_zero_error "a" (d - ("t" - "T"))).
        charge_split; [ solve_linear | charge_tauto ]. }
      { tlaAssert (error y0 v0 >= 0);
        [ apply Lemmas.forget_prem; apply error_pos |
          apply Lemmas.forget_prem; charge_intros ].
        reason_action_tac. exp_pos_tac.
        solve_nonlinear. } }
  Qed.

 reason_action_tac.
      unfold Rbasic_fun.Rmax. repeat destruct_ite.
      - solve_linear.
      - exp_pos_tac. solve_nonlinear.
      - exp_pos_tac. solve_nonlinear.
      - exp_pos_tac. solve_nonlinear.


    tlaAssert ("y" - ub < 0 \\// "y" - ub >= 0);
    [ solve_linear | charge_intros ].
    rewrite Lemmas.land_lor_distr_R.
    apply lorL.
    - tlaAssert ([]("a" <= 0 //\\ "y" - ub < 0)).
      + eapply discr_indX.
        * tlaIntuition.
        * charge_tauto.
        * charge_split; [ | charge_tauto ].
          unfold Spec, Init.
          breakAbstraction. intros.
          repeat destruct H.
          destruct H2. solve_linear.
      + charge_intros.
        apply lexistsR with (x:=1%R).
        charge_split; [ solve_linear | ].
        apply lexistsR with (x:=1%R).
        charge_split; [ solve_linear | ].
        apply Exists_with_st with (t:="t").
        intros. charge_intros.
        charge_split; [ solve_linear | ].
        charge_split; [ solve_linear | ].
        charge_intros.
        tlaAssert ([]("a" = 0 //\\ "y" - ub < 0));
          [ charge_tauto | ].
        apply Lemmas.forget_prem. apply always_imp.
        solve_linear.
        