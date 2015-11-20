Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import TLA.BasicProofRules.
Require Import Examples.System.

Open Scope HP_scope.
Open Scope string_scope.

Section SensorWithDelay.

  Variable d : R.

  Definition Sense : Formula :=
         ("v"! >= 0 //\\ "Xmax_post"! = "Xmax" + "v"!*d
          //\\ "Xmin_post"! = "Xmin")
    \\// ("v"! < 0 //\\ "Xmax_post"! = "Xmax"
         //\\ "Xmin_post"! = "Xmin" + "v"!*d).

  Definition SenseSafeInd : Formula :=
         ("v" >= 0 -->> ("Xmax_post" >= "x" + "v"*"t"
                            //\\ "Xmin_post" <= "x"))
    //\\ ("v" < 0 -->> ("Xmax_post" >= "x"
                           //\\ "Xmin_post" <= "x" + "v"*"t")).

  Definition I := SenseSafeInd.

  Definition SenseSafe : Formula :=
    "Xmin_post" <= "x" <= "Xmax_post".

  Variable WC : Formula.

  Definition w : state->Formula :=
    fun st' => st' "x" = "v" //\\
               AllConstant ("v"::"Xmin_post"::"Xmax_post"::nil)%list st'.

  Definition SpecR : SysRec :=
    {| Init := I;
       Prog := Sense //\\ Unchanged ("x"::nil)%list;
       world := w;
       unch := (("Xmax_post":Term)::("Xmin_post":Term)::
                ("v":Term)::("x":Term)::
                ("Xmin":Term)::("Xmax":Term)::nil)%list;
       maxTime := d |}.

  Definition Spec := SysD SpecR.

  Lemma SysSafe_sense : forall P, P |-- SysSafe SpecR.
  Proof.
    intros.
    apply SysSafe_rule; apply always_tauto.
    enable_ex_st; repeat eexists; solve_linear.
  Qed.

  Theorem sense_safe :
    []("Xmin" <= "x" <= "Xmax") //\\ Spec |-- []SenseSafe.
  Proof.
    intro.
    eapply Sys_by_induction with (IndInv := SenseSafeInd).
    - tlaIntuition.
    - unfold Spec, SpecR. tlaAssume.
    - tlaIntuition.
    - apply SysSafe_sense.
    - tlaAssume.
    - charge_assumption.
    - solve_nonlinear.
    - red. solve_nonlinear.
    - unfold World. eapply diff_ind with (Hyps:=ltrue);
        try solve [tlaIntuition | tlaAssume ].
      simpl deriv_formula. restoreAbstraction.
      charge_intros; repeat charge_split;
      charge_intros.
      { eapply zero_deriv with (x:="v").
        - charge_tauto.
        - tlaIntuition.
        - solve_linear. }
      { solve_nonlinear. }
      { eapply zero_deriv with (x:="v").
        - charge_tauto.
        - tlaIntuition.
        - solve_linear. }
      { solve_nonlinear. }
    - solve_linear; solve_nonlinear.
  Qed.

End SensorWithDelay.

Close Scope HP_scope.
Close Scope string_scope.