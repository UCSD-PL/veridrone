Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Import LibNotations.
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

  Definition w : list DiffEq := ["x"' ::= "v"].

  Definition SpecR : SysRec :=
    {| dvars := ("Xmax_post"::"Xmin_post"::"v"::nil)%list;
       cvars := ("x"::nil)%list;
       Init := I;
       Prog := Sense;
       world := w;
       WConstraint := WC;
       maxTime := d |}.

  Definition Spec := SysD SpecR.

  Lemma SysSafe_sense : forall P, P |-- SysSafe SpecR.
  Proof.
    intros.
    apply SysSafe_rule; apply always_tauto.
    enable_ex; repeat eexists; solve_linear.
  Qed.

  Theorem sense_safe :
    []("Xmin" <= "x" <= "Xmax") //\\ Spec |-- []SenseSafe.
  Proof.
    intro.
    eapply Sys_by_induction with (IndInv := SenseSafeInd).
    - tlaIntuition.
    - unfold Spec, SpecR. tlaAssume.
    - apply SysSafe_sense.
    - tlaAssume.
    - charge_assumption.
    - solve_nonlinear.
    - red. solve_nonlinear.
    - unfold World. eapply diff_ind with (Hyps:=ltrue);
        try solve [tlaIntuition | tlaAssume ];
        repeat tlaSplit;
        try solve [ solve_linear |
                    tlaIntro; eapply unchanged_continuous;
                      [ tlaAssume | solve_linear ] ].
    - solve_linear; solve_nonlinear.
  Qed.

End SensorWithDelay.

Close Scope HP_scope.
Close Scope string_scope.