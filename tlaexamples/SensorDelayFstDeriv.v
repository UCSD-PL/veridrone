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
         ("v"! >= 0 //\\ "Xmax_post"! = "Xmax" + "v"!*d)
    \\// ("v"! < 0 //\\ "Xmax_post"! = "Xmax").

  Definition SenseSafeInd : Formula :=
         ("v" >= 0 -->> ("Xmax_post" >= "x" + "v"*"t"))
    //\\ ("v" < 0 -->> ("Xmax_post" >= "x")).

  Definition I := SenseSafeInd.

  Definition SenseSafe : Formula :=
    "x" <= "Xmax_post".

  Variable WC : Formula.

  Definition w : state->Formula :=
    fun st' => st' "x" <= "v" //\\
               AllConstant ("v"::"Xmax_post"::nil)%list st'.

  Definition SpecR : SysRec :=
    {| Init := I;
       Prog := Sense //\\ Unchanged ("x"::nil)%list;
       world := w;
       unch := (("Xmax_post":Term)::("v":Term)::("x":Term)::
                ("Xmax":Term)::nil)%list;
       maxTime := d |}.

  Definition Spec := SysD SpecR.

  Theorem sense_safe :
    []"x" <= "Xmax" //\\ Spec |-- []SenseSafe.
  Proof.
    intro.
    eapply Sys_by_induction with (IndInv := SenseSafeInd).
    - tlaIntuition.
    - unfold Spec, SpecR. tlaAssume.
    - tlaIntuition.
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