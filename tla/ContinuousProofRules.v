Require Import Coq.micromega.Psatz.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.MVT.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.BasicProofRules.
Require Import TLA.DifferentialInduction.
Require Import TLA.Automation.

Open Scope HP_scope.

(* Contains more proof rules about continuous
   transitions (basic differential induction
   is located in DifferentialInduction.v).
   Includes:
     1) a lemma zero_deriv stating
        that if a continuous transition
        contains a variable with derivative
        zero, then one can add x! = x to
        the hypothesis
     2) a lemma stating that continuous transitions
        guarantee state formulas in the next state
        if the evolution implies that state formula *)

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

Close Scope HP_scope.