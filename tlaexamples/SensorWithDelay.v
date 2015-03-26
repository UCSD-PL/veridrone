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
  Variable Xmax : Var.
  Variable Xmin : Var.
  Variable xderiv : Var.
  Variable d : R.
  Hypothesis get_deriv_Xmax :
    get_deriv Xmax
              (["t" '  ::= -- (1), x '  ::= xderiv, Xmax '  ::= 0,
                Xmin '  ::= 0, xderiv '  ::= 0]) = Some (NatT 0).
  Hypothesis get_deriv_Xmin :
    get_deriv Xmin
              (["t" '  ::= -- (1), x '  ::= xderiv, Xmax '  ::= 0,
                Xmin '  ::= 0, xderiv '  ::= 0]) = Some (NatT 0).
  Hypothesis get_deriv_xderiv :
    get_deriv xderiv
              (["t" '  ::= -- (1), x '  ::= xderiv, Xmax '  ::= 0,
                Xmin '  ::= 0, xderiv '  ::= 0]) = Some (NatT 0).
  Hypothesis get_deriv_x :
    get_deriv x
              (["t" '  ::= -- (1), x '  ::= xderiv, Xmax '  ::= 0,
                Xmin '  ::= 0, xderiv '  ::= 0]) =
    Some (VarNowT xderiv).

  Ltac rewrite_deriv_hyps :=
    breakAbstraction;
    repeat first [ rewrite get_deriv_Xmax |
                   rewrite get_deriv_Xmin |
                   rewrite get_deriv_xderiv |
                   rewrite get_deriv_x ].

  Definition Sense : Formula :=
         (xderiv! >= 0 //\\ Xmax! = x + xderiv!*d //\\ Xmin! = x)
    \\// (xderiv! < 0 //\\ Xmax! = x //\\ Xmin! = x + xderiv!*d).

  Definition SenseSafeInd : Formula :=
         (xderiv >= 0 -->> (Xmax >= x + xderiv*"t" //\\ Xmin <= x))
    //\\ (xderiv < 0 -->> (Xmax >= x //\\ Xmin <= x + xderiv*"t")).

  Definition Init := SenseSafeInd.

  Definition SenseSafe : Formula :=
    Xmin <= x <= Xmax.

  Theorem sense_safe_ind : forall WC,
    Sys (Xmax::Xmin::xderiv::nil)%list (x::nil)%list
        Init Sense (DiffEqC x xderiv::nil)%list WC d
        |-- []SenseSafeInd.
  Proof.
    intro.
    eapply discr_indX.
    - tlaIntuition.
    - tlaAssume.
    - tlaAssume.
    - unfold Next. decompose_hyps.
      + unfold World. eapply diff_ind with (Hyps:=TRUE);
        try solve [tlaIntuition | tlaAssume ];
        repeat tlaSplit;
        try solve [ rewrite_deriv_hyps; solve_linear |
                    eapply unchanged_continuous;
                      [ tlaIntro; tlaAssume |
                        solve_linear ] ].
      + solve_linear; solve_nonlinear.
      + solve_linear; solve_nonlinear.
  Qed.

  Theorem sense_safe : forall WC,
    |-- Sys (Xmax::Xmin::xderiv::nil)%list (x::nil)%list
            Init Sense (DiffEqC x xderiv::nil)%list WC d -->>
            []SenseSafe.
  Proof.
    intros. charge_intros.
    tlaAssert ([]TimeBound d).
    + eapply Sys_bound_t. tlaAssume.
    + charge_intros. tlaAssert ([]SenseSafeInd).
      * rewrite sense_safe_ind. tlaAssume.
      * tlaRevert. apply forget_prem.
        rewrite <- uncurry. rewrite Always_and.
        apply always_imp. solve_nonlinear.
  Qed.

End SensorWithDelay.

Close Scope HP_scope.
Close Scope string_scope.