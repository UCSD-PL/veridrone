Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rtrigo_def.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import Examples.DiffEqSolutions.
Require Import Coq.Lists.List.

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
      0 <= t <= d -->>
      "y" + tdist "v" a t + sdist MAX("v" + a*t, 0) <= ub.

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
        