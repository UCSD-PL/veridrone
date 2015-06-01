Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import Examples.System.

Open Scope HP_scope.

Section SensorWithError.

  Variable err : R.

  Definition Sense : Formula :=
    "Xmax" <= "Xmin" + err //\\ "Xmin" <= "x" <= "Xmax".

  Definition SenseSafe : Formula :=
    "Xmin" <= "x" <= "Xmax".

  Definition I : Formula := SenseSafe.

  Variable d : R.

  Definition SpecR : SysRec :=
    {| Init := I;
       Prog := Unchanged ("x"::"Xmax"::"Xmin"::nil)%list;
       world := fun _ => Sense;
       unch := (("x":Term)::("Xmax":Term)::("Xmin":Term)::nil)%list;
       maxTime := d |}.

  Definition Spec := SysD SpecR.

  Lemma SysSafe_sense : forall P, P |-- SysSafe SpecR.
  Proof.
    intros.
    apply SysSafe_rule; apply always_tauto.
    enable_ex_st. repeat eexists. solve_linear.
  Qed.

  Theorem sense_safe :
    Spec |-- []SenseSafe.
  Proof.
    eapply Sys_by_induction
      with (IndInv := SenseSafe) (A := ltrue).
    + tlaIntuition.
    + unfold Spec, SpecR. tlaAssume.
    + tlaIntuition.
    + apply SysSafe_sense.
    + tlaAssume.
    + eapply BasicProofRules.always_tauto. charge_tauto.
    + tlaAssume.
    + red. solve_linear.
    + unfold World. rewrite Continuous_st_formula with (F:=Sense).
      * solve_linear.
      * tlaIntuition.
      * tlaIntuition.
      * charge_tauto.
    + solve_linear.
  Qed.

End SensorWithError.

Close Scope HP_scope.