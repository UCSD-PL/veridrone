Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Import TLA.TLA.
Import LibNotations.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import TLA.BasicProofRules.
Require Import Examples.System.
Require Import Examples.SecondDerivUtil.

Open Scope HP_scope.
Open Scope string_scope.

Module Type SensorWithDelayRangeSndOrderParams <: SdistParams.

  Parameter x : Var.
  Parameter Xmax : Var.
  Parameter Xmax_post : Var.
  Parameter xd1 : Var.
  Parameter xd2 : Var.
  Parameter xd1max : Var.
  Parameter X : Var.
  Parameter Xd1 : Var.
  Parameter T : Var.
  Parameter d : R.
  (** Clean this up? Maybe **)
  Let w_all := ["t" '  ::= -- (1), x '  ::= xd1,
                xd1 ' ::= xd2, Xmax_post '  ::= 0,
                xd2 '  ::= 0, X ' ::= 0, Xd1 ' ::= 0,
                T ' ::= 0].
  Parameter get_deriv_Xmax_post :
    get_deriv Xmax_post w_all = Some (NatT 0).
  Parameter get_deriv_xd2 :
    get_deriv xd2 w_all = Some (NatT 0).
  Parameter get_deriv_x :
    get_deriv x w_all = Some (VarNowT xd1).
  Parameter get_deriv_xd1 :
    get_deriv xd1 w_all = Some (VarNowT xd2).
  Parameter get_deriv_Xd1 :
    get_deriv Xd1 w_all = Some (NatT 0).
  Parameter get_deriv_X :
    get_deriv X w_all = Some (NatT 0).
  Parameter get_deriv_T :
    get_deriv T w_all = Some (NatT 0).

  Parameter amin : R.
  Parameter amin_lt_0 : (amin < 0)%R.

  Parameter WC : Formula.

End SensorWithDelayRangeSndOrderParams.

Module SensorWithDelayRangeSndOrder
       (Import Params : SensorWithDelayRangeSndOrderParams).

  Module SdistUtil := SdistUtil(Params).
  Import SdistUtil.

  Definition Sense : Formula :=
         (xd2! >= 0 //\\
          Max (tdist xd1max xd2! d) 0
          (fun mx => Xmax_post! = Xmax + mx))
    \\// (xd2! < 0 //\\ 
          Max (tdist xd1max 0 d) 0
          (fun mx => Xmax_post! = Xmax + mx)).

  Definition History : Formula :=
    X ! = x //\\ Xd1 ! = xd1 //\\ T ! = "t"!.

  Definition tdiff : Term :=
    T - "t".

  Definition SenseSafeInd : Formula :=
    x <= X + tdist Xd1 xd2 tdiff //\\
    xd1 <= Xd1 + xd2*tdiff //\\
    Syntax.Forall R
           (fun t =>
              (0 <= t <= d -->>
                           (xd2 >= 0 -->>
                            Max (tdist Xd1 xd2 t) 0
                            (fun mx => X + mx <= Xmax_post))
                     //\\ (xd2 < 0 -->>
                           Max (tdist Xd1 0 t) 0
                           (fun mx => X + mx <= Xmax_post)))) //\\
   "t" <= T <= d.

  Definition I := SenseSafeInd.

  Definition SenseSafe : Formula :=
    x <= Xmax_post.

  Definition w :=
    [x '  ::= xd1, xd1 ' ::= xd2 ].

  Definition SpecR : SysRec :=
    {| dvars := (Xmax_post::xd2::X::Xd1::T::nil)%list;
       cvars := (x::xd1::nil)%list;
       Init := I;
       Prog := Sense //\\ History;
       world := w;
       WConstraint := WC;
       maxTime := d |}.

  Definition Spec := SysD SpecR.

  Ltac rewrite_deriv_terms :=
    repeat match goal with
           | [ H : context [ get_deriv ] |- _ ] =>
             rewrite H
           end.

  Ltac solve_diff_ind_goals :=
    solve [ tlaIntuition |
            unfold World; tlaAssume |
            breakAbstraction;
              rewrite_deriv_terms; solve_linear ].
  
  Theorem sense_safe :
    [](xd1 <= xd1max //\\ x <= Xmax) //\\ Spec |-- []SenseSafe.
  Proof.
    intro.
    eapply Sys_by_induction
    with (IndInv := SenseSafeInd)
           (A:=xd1 <= xd1max //\\ x <= Xmax).
    - tlaIntuition.
    - unfold Spec, SpecR. tlaAssume.
    - tlaAssume.
    - charge_tauto.
    - reason_action_tac. intuition.
      specialize (H4 (pre T - pre "t")%R).
      intuition.
      repeat match type of H7 with
             | ?H -> _ =>
               let HH := fresh "H" in
               assert H as HH by solve_linear;
                 specialize (H7 HH); clear HH
             end.
      destruct (Rge_dec (pre xd2) R0); intuition; solve_linear.
      assert (pre xd2 < 0)%R; solve_linear.
      destruct (Rle_dec
                  (pre Xd1 * (pre T - pre "t") +
                   / 2 * 0 * ((pre T - pre "t") *
                              ((pre T - pre "t") * 1))) R0);
        intuition.
      + eapply Rle_trans; eauto.
        eapply Rle_trans; eauto.
        apply Rplus_le_compat; solve_linear.
        eapply Rle_trans; eauto.
        clear - H7. solve_nonlinear.
      + assert (pre Xd1 * (pre T - pre "t") +
                / 2 * 0 * ((pre T - pre "t") *
                           ((pre T - pre "t") * 1)) >= 0)%R;
        solve_linear.
        eapply Rle_trans; eauto.
        eapply Rle_trans; eauto.
        apply Rplus_le_compat; solve_linear.
        clear - H7. solve_nonlinear.
    - red. solve_linear; rewrite_next_st; solve_linear;
      specialize (H3 x0); intuition; solve_linear.
    - pose proof get_deriv_Xmax_post as get_deriv_Xmax_post.
      pose proof get_deriv_xd2 as get_deriv_xd2.
      pose proof get_deriv_xd1 as get_deriv_xd1.
      pose proof get_deriv_x as get_deriv_x.
      pose proof get_deriv_Xd1 as get_deriv_Xd1.
      pose proof get_deriv_X as get_deriv_X.
      pose proof get_deriv_T as get_deriv_T.
      unfold w_all in *.
      unfold World. repeat charge_split.
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=xd1 <= Xd1 + xd2*tdiff)
                                 (G:=unnext GG)
        end; try solve_diff_ind_goals.
        eapply diff_ind with (Hyps:=TRUE);
          try solve_diff_ind_goals. }
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=TRUE) (G:=unnext GG)
        end;
        try solve_diff_ind_goals. }
      { tlaIntro. eapply diff_ind with (Hyps:=ltrue);
                  try solve_diff_ind_goals.
        - unfold SenseSafeInd;
          simpl; restoreAbstraction; unfold tdist, sdist;
          solve_linear; rewrite_next_st; solve_linear;
          specialize (H7 x0); solve_linear.
        - simpl deriv_formula. restoreAbstraction.
          rewrite_deriv_terms. simpl. restoreAbstraction.
          repeat charge_split.
          + tlaIntro; eapply unchanged_continuous;
            [ tlaAssume | 
            solve_linear; rewrite_next_st; solve_linear ].
          + charge_intros. repeat charge_split.
            * charge_intros; eapply unchanged_continuous;
              [ tlaAssume |
                solve_linear; rewrite_next_st; solve_linear ].
            * charge_intros.
              repeat charge_split;
                try solve [ charge_intros;
                            eapply unchanged_continuous;
                            [ tlaAssume |
                              solve_linear; rewrite_next_st;
                              solve_linear ] |
                            solve_linear ].
            * charge_intros;
              eapply unchanged_continuous;
              [ tlaAssume |
                solve_linear; rewrite_next_st;
                solve_linear ].
            * charge_intros.
              repeat charge_split;
                try solve [ charge_intros;
                            eapply unchanged_continuous;
                            [ tlaAssume |
                              solve_linear; rewrite_next_st;
                              solve_linear ] |
                            solve_linear ]. }
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=TRUE)
                                 (G:=unnext GG)
        end; try solve_diff_ind_goals. }
      { eapply unchanged_continuous;
        [ unfold World; charge_assumption | ].
        solve_linear. }
    - repeat charge_split.
      { solve_linear; rewrite_next_st; R_simplify; solve_linear. }
      { solve_linear; rewrite_next_st; R_simplify; solve_linear. }
      { unfold Discr, Sense, History, Max.
        decompose_hyps; repeat tlaIntro;
        charge_split; fold BasicProofRules.next;
        try solve [solve_linear].
        - reason_action_tac. intuition; try solve [solve_linear].
          repeat match goal with
                 | [ H : eq (post _) _ |- _ ]
                   => try rewrite H in *; clear H
                 end.
          destruct (Rle_dec (pre xd1max * d + / 2 * post xd2
                                              * (d * (d * 1)))
                            R0); intuition.
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
          * assert (pre xd1max * d +
                    / 2 * post xd2 * (d * (d * 1)) >= 0)%R
              by solve_linear. intuition.
            rewrite H16. apply Rplus_le_compat; solve_linear.
            clear - H H14 H1 H4 H2.
            destruct H1.
            { repeat rewrite <- Rmult_assoc in *.
              rewrite Rmult_1_r in *.
              rewrite <- Rmult_plus_distr_r in *.
              assert (0 < d)%R by solve_linear.
              solve_nonlinear. }
            { rewrite <- H0. solve_linear. }
        - reason_action_tac. intuition; try solve [solve_linear].
          repeat match goal with
                 | [ H : eq (post _) _ |- _ ]
                   => try rewrite H in *; clear H
                 end.
          destruct (Rle_dec (pre xd1max * d +
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
          * assert (pre xd1max * d +
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