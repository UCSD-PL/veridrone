Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import Examples.System.

Open Scope HP_scope.
Open Scope string_scope.

Module Type FirstDerivShimParams.
  (* Upper bound on velocity. *)
  Parameter ub : R.
  (* Max time between executions of the
     controller. *)
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
End FirstDerivShimParams.

Module FirstDerivShim (P : FirstDerivShimParams).

  Import P.

  (* The continuous dynamics of the system *)
  Definition w : Evolution :=
    fun st' => st' "v" = "a" //\\ st' "a" = 0.

  Definition Ctrl : Formula :=
    "a"!*d + "v" <= ub \\// "a"! <= 0.

  Definition I : Formula :=
    "v" <= ub //\\ "v" + "a"*d <= ub.

  Definition SpecR : SysRec :=
    {| Init := I;
       Prog := Ctrl //\\ Unchanged ("v"::nil)%list;
       world := w;
       unch := (("a":Term)::("v":Term)::nil)%list;
       maxTime := d |}.

  Definition Spec := PartialSysD SpecR.

  Definition IndInv : Formula :=
         ("a" <  0 -->> "v" <= ub)
    //\\ ("a" >= 0 -->> "a"*"t" + "v" <= ub).

  Lemma SysSafe_ctrl : forall P, P |-- SysSafe SpecR.
  Proof.
    intros.
    apply SysSafe_rule; apply always_tauto.
    enable_ex_st; repeat eexists; solve_linear.
  Qed.

  Theorem ctrl_safe :
    |-- Spec -->> []"v" <= ub.
  Proof.
    charge_intros.
    eapply PartialSys_by_induction
    with (IndInv:=IndInv) (A:=ltrue).
    - tlaIntuition.
    - unfold Spec, SpecR. charge_assumption.
    - tlaIntuition.
    - solve_nonlinear.
    - apply Lemmas.forget_prem. apply always_tauto.
      charge_tauto.
    - solve_nonlinear.
    - unfold InvariantUnder. solve_linear.
      rewrite_next_st. solve_linear.
    - eapply diff_ind with (Hyps:=TRUE).
      + tlaIntuition.
      + tlaIntuition.
      + unfold World. tlaAssume.
      + tlaIntuition.
      + tlaAssume.
      + tlaIntuition.
      + charge_tauto.
      + simpl deriv_formula. restoreAbstraction.
        charge_intros.
        repeat charge_split; charge_intros;
          try solve [solve_linear |
                     eapply zero_deriv with (x:="a");
                       [ charge_tauto | tlaIntuition |
                         solve_linear ] ].
        solve_nonlinear.
    - solve_nonlinear.
  Qed.

End FirstDerivShim.

Close Scope HP_scope.
Close Scope string_scope.
