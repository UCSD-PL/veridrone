Require Import Coq.micromega.Psatz.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.MVT.
Require Import ChargeCore.Tactics.Tactics.
Require Import Logic.Syntax.
Require Import Logic.Semantics.
Require Import Logic.Lib.
Require Import Logic.BasicProofRules.
Require Import Logic.DifferentialInduction.
Require Import Logic.Automation.

Local Open Scope HP_scope.

(* Contains more proof rules about continuous
   transitions (basic differential induction
   is located in DifferentialInduction.v).
   Includes:
     1) a lemma zero_deriv stating
        that if a continuous transition
        contains a variable with derivative
        zero, then one can add x! = x to
        the hypothesis
     2) a corollary of differential
        induction called diff_ind_imp
     3) a lemma zero_deriv_formula_ok which
        allows one to substitute x for x! in a
        goal Formula for all variables x which
        have derivative 0
     4) a lemma unchanged_continuous which
        generalizes zero_deriv and makes it
        easier to apply by automatically adding
        x! = x to the hypothesis for all variables
        with derivative 0 *)

Lemma zero_deriv : forall G cp F x,
  (F |-- Continuous cp) ->
  |-- Forall st : state, cp st -->> st x = R0 ->
  (F //\\ x! = x |-- G) ->
  (F |-- G).
Proof.
  breakAbstraction.
  intros G cp F x Hcont Hin Hsuf tr HF.
  apply Hsuf; split; auto.
  specialize (Hcont tr HF).
  destruct Hcont as [r [f [Hr [Hsol [Hstart Hend]]]]].
  rewrite <- Hend. rewrite <- Hstart.
  unfold is_solution, solves_diffeqs in Hsol.
  destruct Hsol as [pf Hsol].
  assert (forall x0 : R,
          (0 < x0 < r)%R -> derivable_pt (fun t : R => f t x) x0)
    as pf2.
  { intros. apply (pf x). }
  { rewrite (null_derivative_loc (fun t => f t x) R0 r);
    auto.
  - intros. unfold derivable in pf.
    apply derivable_continuous_pt.
    apply pf.
  - unfold derive in Hsol. intros.
    assert (0 <= x0 <= r)%R as Hx0 by psatzl R.
    specialize (Hsol _ Hx0).
    specialize (Hin (Stream.forever (f x0)) I
               (fun x1 : Var =>
                  derive_pt (fun t : R => f t x1) x0 (pf x1 x0))).
    rewrite <- Hin; auto.
    instantiate (1:=pf2).
    apply Ranalysis4.pr_nu_var. auto.
  - intuition. }
Qed.

Lemma Continuous_st_formula : forall w F,
  (forall st', is_st_formula (w st')) ->
  is_st_formula F ->
  |-- Forall st', w st' -->> F ->
  Continuous w |-- next F.
Proof.
  breakAbstraction. intros.
  destruct H2 as [r [f ?]].
  intuition.
  unfold is_solution, solves_diffeqs in *.
  apply next_formula_tl; auto.
  destruct H2. specialize (H2 r).
  assert (0 <= r <= r)%R by psatzl R.
  intuition.
  eapply H1; eauto.
  eapply st_formula_hd; eauto.
Qed.

Lemma Continuous_and
: forall P Q, Continuous (P //\\ Q) |-- Continuous P //\\ Continuous Q.
Proof.
  unfold Continuous; intros.
  repeat (eapply lexistsL; intros).
  charge_split; do 2 eapply lexistsR;
  instantiate (1:= x); instantiate (1:=x0);
  repeat charge_split; try charge_tauto.
  - charge_assert (PropF (is_solution x0 (P //\\ Q) x)).
    + charge_assumption.
    + charge_clear.
      breakAbstraction. intros.
      eapply Proper_is_solution_lentails. 4: eassumption.
      reflexivity. charge_tauto.
      eapply RIneq.Req_ge. reflexivity.
  - charge_assert (PropF (is_solution x0 (P //\\ Q) x)).
    + charge_assumption.
    + charge_clear.
      breakAbstraction. intros.
      eapply Proper_is_solution_lentails. 4: eassumption.
      reflexivity. charge_tauto.
      eapply RIneq.Req_ge. reflexivity.
Qed.
