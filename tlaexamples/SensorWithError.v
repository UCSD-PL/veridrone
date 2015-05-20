Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import Examples.System.

Open Scope HP_scope.

Section SensorWithError.

  Variable err : R.

  Definition Sense : Formula :=
    "Xmax"! <= "Xmin"! + err //\\ "Xmin"! <= "x"! <= "Xmax"!.

  Definition SenseSafe : Formula :=
    "Xmin" <= "x" <= "Xmax".

  Definition I : Formula := SenseSafe.

  Variable w : list DiffEq.
  Variable d : R.

  Definition SpecR : SysRec :=
    {| dvars := nil;
       cvars := ("x"::"Xmax"::"Xmin"::nil)%list;
       Init := I;
       Prog := ltrue;
       world := w;
       WConstraint := Sense;
       maxTime := d |}.

  Definition Spec := SysD SpecR.

  Lemma SysSafe_sense : forall P, P |-- SysSafe SpecR.
  Proof.
    intros.
    apply SysSafe_rule; apply always_tauto.
    enable_ex; repeat eexists; solve_linear.
  Qed.

  Theorem sense_safe :
    Spec |-- []SenseSafe.
  Proof.
    eapply Sys_by_induction
      with (IndInv := SenseSafe) (A := ltrue).
    + tlaIntuition.
    + unfold Spec, SpecR. tlaAssume.
    + apply SysSafe_sense.
    + tlaAssume.
    + eapply BasicProofRules.always_tauto. charge_tauto.
    + tlaAssume.
    + red. solve_linear.
    + solve_linear.
    + solve_linear.
  Qed.

End SensorWithError.

Close Scope HP_scope.