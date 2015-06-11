Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Import TLA.TLA.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import TLA.BasicProofRules.
Require Import Examples.System.
Require Import Examples.SecondDerivUtil.

Open Scope HP_scope.
Open Scope string_scope.

Module Type SensorWithDelayRangeSndOrderParams <: SdistParams.

  Parameter d : R.

  Parameter amin : R.
  Parameter amin_lt_0 : (amin < 0)%R.

  Parameter WC : Formula.

End SensorWithDelayRangeSndOrderParams.

Module SensorWithDelayRangeSndOrder
       (Import Params : SensorWithDelayRangeSndOrderParams).

  Module SdistUtil := SdistUtil(Params).
  Import SdistUtil.

  Definition Sense : Formula :=
         ("a"! >= 0 //\\
          Max (tdist "Vmax" "a"! d) 0
          (fun mx => "Xmax_post"! = "Xmax" + mx))
    \\// ("a"! < 0 //\\ 
          Max (tdist "Vmax" 0 d) 0
          (fun mx => "Xmax_post"! = "Xmax" + mx)).

  Definition History : Formula :=
    "X"! = "x" //\\ "V"! = "v" //\\ "T"! = "t"!.

  Definition tdiff : Term :=
    "T" - "t".

  Definition SenseSafeInd : Formula :=
    "x" <= "X" + tdist "V" "a" tdiff //\\
    "v" <= "V" + "a"*tdiff //\\
    Syntax.Forall R
           (fun t =>
              (0 <= t <= d -->>
                           ("a" >= 0 -->>
                            Max (tdist "V" "a" t) 0
                            (fun mx => "X" + mx <= "Xmax_post"))
                     //\\ ("a" < 0 -->>
                           Max (tdist "V" 0 t) 0
                           (fun mx => "X" + mx <= "Xmax_post")))) //\\
   "t" <= "T" <= d.

  Definition I := SenseSafeInd.

  Definition SenseSafe : Formula :=
    "x" <= "Xmax_post".

  Definition w :=
    fun st' : state =>
      st' "x" = "v" //\\ st' "v" = "a" //\\
      AllConstant ("Xmax_post"::"a"::"X"::"V"::"T"::nil)%list st'.

  Definition SpecR : SysRec :=
    {| Init := I;
       Prog := Sense //\\ History //\\ Unchanged ("x"::"v"::nil)%list;
       world := w;
       unch := (("Xmax_post":Term)::("a":Term)::("X":Term)::
                ("V":Term)::("T":Term)::("x":Term)::("v":Term)::nil)%list;
       maxTime := d |}.

  Definition Spec := SysD SpecR.

  Lemma SysSafe_sense : forall P, P |-- SysSafe SpecR.
  Proof.
    intros.
    apply SysSafe_rule; apply always_tauto.
    enable_ex_st. simpl.
    exists d. exists (st "v"). exists (st "x").
    exists d. exists (st "v"). exists (st "x").
    exists (st "Xmax" + Rbasic_fun.Rmax (st "Vmax" * d) 0)%R.
    exists R0. solve_linear. left.
    rewrite_real_zeros. solve_linear.
    { unfold Rbasic_fun.Rmax.
      match goal with
      |- context[ Rle_dec ?e1 ?e2 ] =>
      destruct (Rle_dec e1 e2)
      end; solve_linear. }
    { unfold Rbasic_fun.Rmax.
      match goal with
      |- context[ Rle_dec ?e1 ?e2 ] =>
      destruct (Rle_dec e1 e2)
      end; solve_linear. }
  Qed.

(*
  Ltac rewrite_deriv_terms :=
    repeat match goal with
           | [ H : context [ get_deriv ] |- _ ] =>
             rewrite H
           end.*)

  Ltac solve_diff_ind_goals :=
    solve [ tlaIntuition |
            unfold World; tlaAssume |
            breakAbstraction;
              solve_linear ].
  
  Theorem sense_safe :
    []("v" <= "Vmax" //\\ "x" <= "Xmax") //\\ Spec |-- []SenseSafe.
  Proof.
    intro.
    eapply Sys_by_induction
    with (IndInv := SenseSafeInd)
           (A:="v" <= "Vmax" //\\ "x" <= "Xmax").
    - tlaIntuition.
    - unfold Spec, SpecR. tlaAssume.
    - tlaIntuition.
    - apply SysSafe_sense.
    - tlaAssume.
    - charge_tauto.
    - reason_action_tac. intuition.
      specialize (H4 (pre "T" - pre "t")%R).
      intuition.
      repeat match type of H7 with
             | ?H -> _ =>
               let HH := fresh "H" in
               assert H as HH by solve_linear;
                 specialize (H7 HH); clear HH
             end.
      destruct (Rge_dec (pre "a") R0); intuition; solve_linear.
      assert (pre "a" < 0)%R; solve_linear.
      destruct (Rle_dec
                  (pre "V" * (pre "T" - pre "t") +
                   / 2 * 0 * ((pre "T" - pre "t") *
                              ((pre "T" - pre "t") * 1))) R0);
        intuition.
      + eapply Rle_trans; eauto.
        eapply Rle_trans; eauto.
        apply Rplus_le_compat; solve_linear.
        eapply Rle_trans; eauto.
        clear - H7. solve_nonlinear.
      + assert (pre "V" * (pre "T" - pre "t") +
                / 2 * 0 * ((pre "T" - pre "t") *
                           ((pre "T" - pre "t") * 1)) >= 0)%R;
        solve_linear.
        eapply Rle_trans; eauto.
        eapply Rle_trans; eauto.
        apply Rplus_le_compat; solve_linear.
        clear - H7. solve_nonlinear.
    - red. solve_linear; rewrite_next_st; solve_linear;
      specialize (H3 x); intuition; solve_linear.
    - unfold World. repeat charge_split.
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:="v" <= "V" + "a"*tdiff)
                                 (G:=unnext GG)
        end; try solve_diff_ind_goals.
        eapply diff_ind with (Hyps:=TRUE);
          try solve_diff_ind_goals; solve_nonlinear.
        solve_nonlinear. }
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=TRUE) (G:=unnext GG)
        end;
        try solve_diff_ind_goals.
        solve_nonlinear. }
      { tlaIntro. eapply diff_ind with (Hyps:=ltrue);
                  try solve_diff_ind_goals.
        - unfold SenseSafeInd;
          simpl; restoreAbstraction; unfold tdist, sdist;
          solve_linear; rewrite_next_st; solve_linear;
          specialize (H7 x); solve_linear.
        - simpl deriv_formula. restoreAbstraction.
          simpl. restoreAbstraction.
          charge_intros; repeat charge_split;
          charge_intros.
          + solve_linear.
          + repeat charge_split.
            * charge_intros. eapply zero_deriv with (x:="a").
              { charge_tauto. }
              { tlaIntuition. }
              { solve_linear. }
            * charge_intros; repeat charge_split;
              charge_intros.
              { eapply zero_deriv with (x:="a");
                [ charge_tauto | tlaIntuition | ].
                eapply zero_deriv with (x:="X");
                [ charge_tauto | tlaIntuition | ].
                eapply zero_deriv with (x:="V");
                [ charge_tauto | tlaIntuition | ].
                eapply zero_deriv with (x:="T");
                [ charge_tauto | tlaIntuition | ].
                solve_linear; rewrite_next_st;
                solve_linear. }
              { solve_nonlinear. }
              { eapply zero_deriv with (x:="a");
                [ charge_tauto | tlaIntuition | ].
                eapply zero_deriv with (x:="X");
                [ charge_tauto | tlaIntuition | ].
                eapply zero_deriv with (x:="V");
                [ charge_tauto | tlaIntuition | ].
                eapply zero_deriv with (x:="T");
                [ charge_tauto | tlaIntuition | ].
                solve_linear; rewrite_next_st;
                solve_linear. }
              { solve_nonlinear. }
            * charge_intros; repeat charge_split;
              charge_intros.
              { eapply zero_deriv with (x:="a");
                [ charge_tauto | tlaIntuition | ].
                solve_linear. }
              { eapply zero_deriv with (x:="a");
                [ charge_tauto | tlaIntuition | ].
                solve_linear. }
            * charge_intros; repeat charge_split;
              charge_intros.
              { eapply zero_deriv with (x:="a");
                [ charge_tauto | tlaIntuition | ].
                eapply zero_deriv with (x:="X");
                [ charge_tauto | tlaIntuition | ].
                eapply zero_deriv with (x:="V");
                [ charge_tauto | tlaIntuition | ].
                eapply zero_deriv with (x:="T");
                [ charge_tauto | tlaIntuition | ].
                solve_linear; rewrite_next_st;
                solve_linear. }
              { solve_nonlinear. }
              { eapply zero_deriv with (x:="a");
                [ charge_tauto | tlaIntuition | ].
                eapply zero_deriv with (x:="X");
                [ charge_tauto | tlaIntuition | ].
                eapply zero_deriv with (x:="V");
                [ charge_tauto | tlaIntuition | ].
                eapply zero_deriv with (x:="T");
                [ charge_tauto | tlaIntuition | ].
                solve_linear; rewrite_next_st;
                solve_linear. }
              { solve_nonlinear. } }
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=TRUE)
                                 (G:=unnext GG)
        end; try solve_diff_ind_goals. }
      { eapply zero_deriv with (x:="T");
        [ charge_tauto | tlaIntuition | ].
        solve_linear. }
    - repeat charge_split.
      { solve_linear; rewrite_next_st; R_simplify; solve_linear. }
      { solve_linear; rewrite_next_st; R_simplify; solve_linear. }
      { unfold Discr, Sense, History, Max.
        decompose_hyps; repeat tlaIntro;
        charge_split; fold BasicProofRules.next;
        try solve [solve_linear].
        - reason_action_tac. simpl in *.
          intuition; try solve [solve_linear].
          repeat match goal with
                 | [ H : eq (post _) _ |- _ ]
                   => try rewrite H in *; clear H
                 end.
          destruct (Rle_dec (pre "Vmax" * d + / 2 * post "a"
                                              * (d * (d * 1)))
                            R0); intuition.
          * repeat match goal with
                   | [ H : eq (post _) _ |- _ ]
                     => try rewrite H in *; clear H
                   end.
            apply Rplus_le_compat; solve_linear.
            clear - r H0 H1 H4 H2. 
            destruct H1.
            { repeat rewrite <- Rmult_assoc in *.
              rewrite Rmult_1_r in *.
              rewrite <- Rmult_plus_distr_r in *.
              assert (0 < d)%R by solve_linear.
              solve_nonlinear. }
            { rewrite <- H. solve_linear. }
          * assert (pre "Vmax" * d +
                    / 2 * post "a" * (d * (d * 1)) >= 0)%R
              by solve_linear. intuition.
            rewrite H16. apply Rplus_le_compat; solve_linear.
            clear - H H0 H14 H1 H4 H2.
            destruct H1.
            { repeat rewrite <- Rmult_assoc in *.
              rewrite Rmult_1_r in *.
              rewrite <- Rmult_plus_distr_r in *.
              assert (0 < d)%R by solve_linear.
              solve_nonlinear. }
            { rewrite <- H1. solve_linear. }
        - reason_action_tac. simpl in *.
          intuition; try solve [solve_linear].
          repeat match goal with
                 | [ H : eq (post _) _ |- _ ]
                   => try rewrite H in *; clear H
                 end.
          destruct (Rle_dec (pre "Vmax" * d +
                             / 2 * 0 * (d * (d * 1))) R0);
            intuition.
          * repeat match goal with
                   | [ H : eq (post _) _ |- _ ]
                     => try rewrite H in *; clear H
                   end.
            apply Rplus_le_compat; solve_linear.
            clear - r H H1 H4 H2. 
            destruct H1.
            { repeat rewrite <- Rmult_assoc in *.
              rewrite Rmult_1_r in *.
              rewrite <- Rmult_plus_distr_r in *.
              assert (0 < d)%R by solve_linear.
              solve_nonlinear. }
            { rewrite <- H0. solve_linear. }
          * assert (pre "Vmax" * d +
                    / 2 * 0 * (d * (d * 1)) >= 0)%R
              by solve_linear. intuition.
            rewrite H16. apply Rplus_le_compat; solve_linear.
            clear - H H14 H1 H4 H2.
            destruct H1.
            { repeat rewrite <- Rmult_assoc in *.
              rewrite Rmult_1_r in *.
              rewrite <- Rmult_plus_distr_r in *.
              assert (0 < d)%R by solve_linear.
              solve_nonlinear. }
            { rewrite <- H0. solve_linear. } }
      { solve_linear. }
      { solve_linear. }
  Qed.

End SensorWithDelayRangeSndOrder.

Close Scope HP_scope.
Close Scope string_scope.