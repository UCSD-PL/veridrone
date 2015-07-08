  Lemma same_next :
    forall x y,
      (x! = R0 //\\ y! = R0 |-- x! = y!).
  Proof. solve_linear. Qed.

  Lemma UpperLower_X_Proposed_refine :
    forall t,
      (UpperLower_X.Monitor.SafeAcc t //\\ "a"! = t
       |-- UpperLower_X.Monitor.SafeAcc "a"!).
  Proof.
    breakAbstraction. solve_linear. rewrite H1 in *.
    solve_linear.
  Qed.

(*
  Definition refined_UpperLower_X_SpecR :
    { ins : list Var &
       { outs : list Var &
           { p : Parallel ins outs &
                 tlaParD p |--
                 Prog (projT1 UpperLower_X_SpecR)} } }.
  Proof.
    Opaque UpperLower_X.Monitor.SafeAcc
           UpperLower_X.Monitor.Default.
    eexists. eexists. eexists. simpl. restoreAbstraction.
    match goal with
    | [ |- context [ rename_formula ?m _ ] ]
      => remember m as rx
    end.
    match goal with
    | [ |- context
             [ rename_formula _ (rename_formula ?m _) ] ]
      => remember m as rm
    end.
    repeat rewrite minus_eq.
    rewrite land_distr.
    apply par_disjoint_refine.
    { repeat rewrite land_lor_distr_R.
      pose proof UpperLower_X_Proposed_refine
        as Hrefine. specialize (Hrefine "A").
      apply (Proper_Rename rx rx) in Hrefine;
        [ | reflexivity].
      rewrite <- Rename_ok in Hrefine.
      rewrite <- Rename_ok in Hrefine.
      rewrite <- Hrefine at 1. clear Hrefine.
      pose proof UpperLower_X_Proposed_refine as Hrefine.
      specialize (Hrefine "A").
      apply (Proper_Rename rm rm) in Hrefine;
        [ | reflexivity].
      apply (Proper_Rename rx rx) in Hrefine;
        [ | reflexivity].
      rewrite <- Rename_ok with (m:=rm) in Hrefine.
      rewrite <- Rename_ok with (m:=rm) in Hrefine.
      rewrite <- Rename_ok with (m:=rx) in Hrefine.
      rewrite <- Rename_ok with (m:=rx) in Hrefine.
      rewrite <- Hrefine at 1. clear Hrefine.
      repeat rewrite lorA.
      Transparent UpperLower_X.Monitor.SafeAcc
                  UpperLower_X.Monitor.Default.
      subst. simpl. restoreAbstraction.
      repeat rewrite minus_eq. rewrite land_distr.
      apply ite_refine.
      { reflexivity. }
      { apply Assign_refine; reflexivity. }
      { rewrite <- lor_intro2. rewrite <- lor_intro2.
        apply ite_refine_and_impl.
        { reflexivity. }
        { solve_linear. }
        { apply ite_refine_and_impl.
          { reflexivity. }
          { solve_linear. }
          { rewrite <- leq_eq_refine.
            apply Assign_refine; reflexivity. }
          { rewrite <- leq_eq_refine.
            apply Assign_refine; reflexivity. } }
        { apply ite_refine_and_impl.
          { reflexivity. }
          { solve_linear. }
          { rewrite <- leq_eq_refine.
            rewrite minus_0_l_equiv.
            rewrite <- neg_eq.
            apply Assign_refine; reflexivity. }
          { rewrite <- leq_eq_refine.
            rewrite minus_0_l_equiv.
            rewrite <- neg_eq.
            apply Assign_refine; reflexivity. } } }
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit. }
    { rewrite landtrueR.
      rewrite <- same_next.
      repeat apply par_disjoint_refine;
      try (apply Assign_refine; reflexivity). }
    Grab Existential Variables.
    { decide_disjoint_var_sets. }
    { decide_disjoint_var_sets. }
    { decide_disjoint_var_sets. }
    { decide_disjoint_var_sets. }
    { decide_disjoint_var_sets. }
    { decide_disjoint_var_sets. }
  Defined.
*)