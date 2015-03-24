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

  Variable x : Var.
  Variables Xmax Xmin : Var.
  Variables Xmax_post Xmin_post : Var.
  Variable xderiv : Var.
  Variable d : R.
  (** Clean this up? Maybe **)
  Let w := ["t" '  ::= -- (1), x '  ::= xderiv, Xmax_post '  ::= 0,
            Xmin_post '  ::= 0, xderiv '  ::= 0].
  Hypothesis get_deriv_Xmax_post :
    get_deriv Xmax_post w = Some (NatT 0).
  Hypothesis get_deriv_Xmin_post :
    get_deriv Xmin_post w = Some (NatT 0).
  Hypothesis get_deriv_xderiv :
    get_deriv xderiv w = Some (NatT 0).
  Hypothesis get_deriv_x :
    get_deriv x w = Some (VarNowT xderiv).

  Ltac rewrite_deriv_hyps :=
    breakAbstraction; unfold w in *;
    repeat first [ rewrite get_deriv_Xmax_post |
                   rewrite get_deriv_Xmin_post |
                   rewrite get_deriv_xderiv |
                   rewrite get_deriv_x ].

  Definition Sense : Formula :=
         (xderiv! >= 0 //\\ Xmax_post! = Xmax + xderiv!*d
          //\\ Xmin_post! = Xmin)
    \\// (xderiv! < 0 //\\ Xmax_post! = Xmax
         //\\ Xmin_post! = Xmin + xderiv!*d).

  Definition SenseSafeInd : Formula :=
         (xderiv >= 0 -->> (Xmax_post >= x + xderiv*"t"
                            //\\ Xmin_post <= x))
    //\\ (xderiv < 0 -->> (Xmax_post >= x
                           //\\ Xmin_post <= x + xderiv*"t")).

  Definition I := SenseSafeInd.

  Definition SenseSafe : Formula :=
    Xmin_post <= x <= Xmax_post.

  Variable WC : Formula.

  Definition world := (DiffEqC x xderiv::nil)%list.

  Definition SpecR : SysRec (x::nil)%list world d :=
    {| dvars := (Xmax_post::Xmin_post::xderiv::nil)%list;
       Init := I;
       Prog := Sense;
       WConstraint := WC |}.

  Definition Spec := SysD SpecR.

  Theorem sense_safe :
    [](Xmin <= x <= Xmax) //\\ Spec |-- []SenseSafe.
  Proof.
    intro.
    eapply Sys_by_induction with (IndInv := SenseSafeInd).
    - tlaIntuition.
    - unfold Spec, SpecR. tlaAssume.
    - tlaAssume.
    - charge_assumption.
    - solve_nonlinear.
    - red. solve_nonlinear.
    - unfold World. eapply diff_ind with (Hyps:=ltrue);
        try solve [tlaIntuition | tlaAssume ];
        repeat tlaSplit;
        try solve [ rewrite_deriv_hyps; solve_linear |
                    tlaIntro; eapply unchanged_continuous;
                      [ tlaAssume | solve_linear ] ].
    - solve_linear; solve_nonlinear.
  Qed.

End SensorWithDelay.

Close Scope HP_scope.
Close Scope string_scope.