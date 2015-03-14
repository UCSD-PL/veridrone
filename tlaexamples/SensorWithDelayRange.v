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
    breakAbstraction; unfold w in * ;
    repeat first [ rewrite get_deriv_Xmax_post |
                   rewrite get_deriv_Xmin_post |
                   rewrite get_deriv_xderiv |
                   rewrite get_deriv_x ].

  Definition Sense : Formula :=
         (xderiv! >= 0 //\\ Xmax_post! = Xmax + xderiv!*d //\\ Xmin_post! = Xmin)
    \\// (xderiv! < 0 //\\ Xmax_post! = Xmax //\\ Xmin_post! = Xmin + xderiv!*d).

  Definition SenseSafeInd : Formula :=
         (xderiv >= 0 -->> (Xmax_post >= x + xderiv*"t" //\\ Xmin_post <= x))
    //\\ (xderiv < 0 -->> (Xmax_post >= x //\\ Xmin_post <= x + xderiv*"t")).

  Definition Init := SenseSafeInd.

  Definition SenseSafe : Formula :=
    Xmin_post <= x <= Xmax_post.

  Theorem sense_safe : forall WC,
    [](Xmin <= x <= Xmax) //\\
    Sys (Xmax_post::Xmin_post::xderiv::nil)%list (x::nil)%list
        Init Sense (DiffEqC x xderiv::nil)%list WC d
        |-- []SenseSafe.
  Proof.
    intro.
    eapply Sys_by_induction with (IndInv := SenseSafeInd).
    - tlaIntuition.
    - tlaAssume.
    - tlaAssume.
    - charge_assumption.
    - solve_nonlinear.
    - red. solve_nonlinear.
    - unfold World. eapply diff_ind with (Hyps:=ltrue);
        try solve [tlaIntuition | tlaAssume ];
        repeat tlaSplit;
        try solve [ rewrite_deriv_hyps; solve_linear |
                    eapply unchanged_continuous;
                      [ tlaIntro; tlaAssume |
                        solve_linear ] ].
    - solve_linear; solve_nonlinear.
  Qed.

End SensorWithDelay.

Close Scope HP_scope.
Close Scope string_scope.