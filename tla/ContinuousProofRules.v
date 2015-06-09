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

(* The shallow embedding of differential equations breaks
   the rest of this file. *)
(*
Definition var_eqb (s1 s2:Var) : bool :=
  proj1_sig (Sumbool.bool_of_sumbool
               (String.string_dec s1 s2)).

Lemma var_eqb_ok : forall s1 s2,
  var_eqb s1 s2 = true ->
  s1 = s2.
Proof.
  unfold var_eqb; simpl; intros.
  destruct (String.string_dec s1 s2);
    try discriminate; auto.
Qed.

Definition diffeq_eqb (x:Var) (n:nat) (d:DiffEq) : bool :=
  andb (var_eqb (get_var d) x)
       (match get_term d with
          | NatT n' => beq_nat n n'
          | _ => false
        end).

Fixpoint term_unchanged (t:Term) (eqs:state->Formula) : bool :=
  match t with
    | VarNowT x =>
      List.existsb (diffeq_eqb x 0) eqs
    | VarNextT _ => false
    | RealT _ => true
    | NatT _ => true
    | PlusT t1 t2 =>
      andb (term_unchanged t1 eqs) (term_unchanged t2 eqs)
    | MinusT t1 t2 =>
      andb (term_unchanged t1 eqs) (term_unchanged t2 eqs)
    | MultT t1 t2 =>
      andb (term_unchanged t1 eqs) (term_unchanged t2 eqs)
    | InvT t => term_unchanged t eqs
    | CosT t => term_unchanged t eqs
    | SinT t => term_unchanged t eqs
    | SqrtT t => term_unchanged t eqs
    | ArctanT t => term_unchanged t eqs
  end.

Fixpoint formula_unchanged (F:Formula) (eqs:list DiffEq)
  : bool :=
  match F with
    | Comp t1 t2 _ =>
      andb (term_unchanged t1 eqs) (term_unchanged t2 eqs)
    | And F1 F2 =>
      andb (formula_unchanged F1 eqs)
           (formula_unchanged F2 eqs)
    | Or F1 F2 =>
      andb (formula_unchanged F1 eqs)
           (formula_unchanged F2 eqs)
    | Imp F1 F2 =>
      andb (formula_unchanged F1 eqs)
           (formula_unchanged F2 eqs)
    | _ => false
  end.

Lemma diffeq_eqb_ok : forall v e d,
  diffeq_eqb v e d = true ->
  d = DiffEqC v e.
Proof.
  intros v e d Heq.
  unfold diffeq_eqb in *. simpl in *.
  apply andb_prop in Heq; destruct Heq.
  apply var_eqb_ok in H.
  destruct d as [v' t]; simpl in *.
  destruct t; try discriminate.
  apply beq_nat_true in H0.
  subst e; subst v; auto.
Qed.

Lemma extract_vars_term_0 : forall t eqs tr,
  term_unchanged t eqs = true ->
  eval_formula (Continuous eqs) tr ->
  eval_term (next_term t) (Stream.hd tr) (Stream.hd (Stream.tl tr)) =
  eval_term t (Stream.hd tr) (Stream.hd (Stream.tl tr)).
Proof.
  Admitted.
(*
  induction t; simpl;
  intros eqs tr Hst Hunch; auto;
  try solve [
        simpl in *; simpl;
    apply andb_prop in Hst; destruct Hst;
    erewrite IHt1; eauto; try (erewrite IHt2; eauto);
    intros; apply Hin; apply List.in_or_app; auto;
    intros; apply Hin; apply List.in_or_app; auto].
  - pose proof (zero_deriv (v!=v) eqs (Continuous eqs) v).
    apply H; auto; simpl; intros; intuition.
    destruct (List.existsb_exists (diffeq_eqb v 0) eqs)
             as [Hin1 Hin2].
    specialize (Hin1 Hst).
    destruct Hin1 as [d [Hin Heq] ].
    apply diffeq_eqb_ok in Heq.
    subst d; auto.
    clear; breakAbstraction; tauto.
  - erewrite IHt; eauto;
    intros; apply Hin; apply List.in_or_app; auto;
    intros; apply Hin; apply List.in_or_app; auto.
  - erewrite IHt; eauto;
    intros; apply Hin; apply List.in_or_app; auto;
    intros; apply Hin; apply List.in_or_app; auto.
  - erewrite IHt; eauto;
    intros; apply Hin; apply List.in_or_app; auto;
    intros; apply Hin; apply List.in_or_app; auto.
Qed.
*)
Lemma extract_vars_0 : forall F H eqs,
  formula_unchanged H eqs = true ->
  (F |-- Continuous eqs) ->
  (|-- (F //\\ next H) -->> H) //\\ (|-- (F //\\ H) -->> next H).
Proof.
  induction H; intros eqs Hunch Hcont;
   simpl in *; unfold tlaEntails in *;
  simpl in *; intros; intuition; try discriminate;
  try apply andb_prop in Hunch;
  try destruct Hunch as [Hunch1 Hunch2];
  try solve [ eapply IHFormula1; eauto |
              eapply IHFormula2; eauto |
              left; eapply IHFormula1; eauto |
              right; eapply IHFormula2; eauto ].
  - unfold tlaEntails in *; simpl in *;
    unfold eval_comp in *; simpl in *; intros.
    rewrite <- extract_vars_term_0 with (eqs:=eqs) (t:=t);
      auto;
    try rewrite <- extract_vars_term_0
    with (eqs:=eqs) (t:=t0); auto; try tauto;
    apply Hcont; auto; tauto.
  - simpl in *; unfold eval_comp in *; simpl; intros.
    rewrite extract_vars_term_0
    with (eqs:=eqs) (t:=t); auto;
    try rewrite extract_vars_term_0
    with (eqs:=eqs) (t:=t0); auto; try tauto;
    apply Hcont; auto; tauto.
  - eapply IHFormula2; eauto; intuition.
    apply H5. eapply IHFormula1; eauto.
  - eapply IHFormula2; eauto; intuition.
    apply H5. eapply IHFormula1; eauto.
Qed.

Lemma diff_ind_imp : forall F H G eqs,
  is_st_formula G ->
  is_st_formula H ->
  formula_unchanged H eqs = true ->
  (F //\\ H |-- G) ->
  (F |-- Continuous eqs) ->
  (H |-- deriv_formula G eqs) ->
  (F |-- (next H -->> next G)).
Proof.
  intros F H G eqs HstG HstH Hin Hinit Hcont Hind.
  tlaRevert. apply imp_right.
  assert (|-- (Continuous eqs //\\ next H) -->> H) by
    (eapply extract_vars_0; eauto; charge_assumption).
  assert (|-- (Continuous eqs //\\ H) -->> next H) by
      (eapply extract_vars_0; eauto; charge_assumption).
  charge_intros.
  apply diff_ind with (Hyps:=H) (cp:=eqs); auto;
  charge_tauto.
Qed.

Fixpoint zero_deriv_term (t:Term) (eqs:list DiffEq) :=
  match t with
    | VarNextT x =>
      if List.existsb (diffeq_eqb x 0) eqs
      then VarNowT x
      else t
    | PlusT t1 t2 =>
      PlusT (zero_deriv_term t1 eqs)
            (zero_deriv_term t2 eqs)
    | MinusT t1 t2 =>
      MinusT (zero_deriv_term t1 eqs)
             (zero_deriv_term t2 eqs)
    | MultT t1 t2 =>
      MultT (zero_deriv_term t1 eqs)
            (zero_deriv_term t2 eqs)
    | _ => t
  end.

Fixpoint zero_deriv_formula (F:Formula) (eqs:list DiffEq) :=
  match F with
    | Comp t1 t2 op => Comp (zero_deriv_term t1 eqs)
                            (zero_deriv_term t2 eqs) op
    | And F1 F2 => And (zero_deriv_formula F1 eqs)
                       (zero_deriv_formula F2 eqs)
    | Or F1 F2 => Or (zero_deriv_formula F1 eqs)
                       (zero_deriv_formula F2 eqs)
    | _ => F
  end.

Lemma zero_deriv_term_ok : forall t eqs F,
  (|-- F -->> Continuous eqs) ->
  (|-- F -->> (zero_deriv_term t eqs) = t).
Proof.
  intros t eqs.
  induction t; intros F Hcont;
  try solve [breakAbstraction; unfold eval_comp; simpl; intuition |
             breakAbstraction; unfold eval_comp in *; simpl;
            simpl; intros ? tr HF;
            erewrite IHt1; eauto; erewrite IHt2; eauto].
  - unfold zero_deriv_term.
    destruct (List.existsb (diffeq_eqb v 0) eqs) eqn:?.
    + apply List.existsb_exists in Heqb.
      destruct Heqb as [d [Hd1 Hd2] ].
      apply diffeq_eqb_ok in Hd2. subst d.
      apply limplAdj.
      apply zero_deriv with (x:=v) (cp:=eqs); auto.
      apply landAdj. assumption.
      simpl; unfold eval_comp; simpl;
      intuition.
      clear. breakAbstraction. unfold eval_comp. simpl.
      intuition.
    + breakAbstraction; unfold eval_comp; simpl; intuition.
Qed.

Lemma zero_deriv_formula_ok : forall F G eqs,
  (|-- F -->> Continuous eqs) ->
  (|-- F -->> zero_deriv_formula G eqs) ->
  (|-- F -->> G).
Proof.
  simpl; intros F G eqs Hcont Hzero tr HF.
  specialize (Hzero tr HF).
  induction G; try solve [ simpl; auto ].
  - pose proof (zero_deriv_term_ok t eqs _ Hcont).
    pose proof (zero_deriv_term_ok t0 eqs _ Hcont).
    simpl in *. unfold eval_comp in *. simpl in *.
    intro.
    rewrite <- H; auto. rewrite <- H0; auto.
    eapply Hzero; eauto.
  - simpl in Hzero. split; try apply IHG1;
    try apply IHG2; intuition.
    simpl. eauto. simpl; eauto.
  - simpl. intros. destruct Hzero; eauto.
    + left; apply IHG1; auto. simpl; eauto.
    + right; apply IHG2; auto; simpl; eauto.
Qed.

Definition get_unchanged (eqs:list DiffEq) : list Var :=
  List.map get_var
           (List.filter (fun d =>
                           match get_term d with
                             | NatT O => true
                             | _ => false
                           end) eqs).

Lemma get_unchanged_ok : forall eqs x,
  List.In x (get_unchanged eqs) ->
  List.In (DiffEqC x 0) eqs.
Proof.
  induction eqs; auto.
  intros x Hin. destruct a.
  unfold get_unchanged in *. simpl in *.
  destruct t; simpl in *;
  try solve [right; apply IHeqs; auto].
  destruct n; simpl in *.
  - destruct Hin.
    + subst v; left; auto.
    + right; apply IHeqs; auto.
  - right; apply IHeqs; auto.
Qed.

Lemma unchanged_continuous_aux : forall eqs,
  |-- Continuous eqs -->> Unchanged (get_unchanged eqs).
Proof.
  intro eqs. pose proof (get_unchanged_ok eqs) as Hunch.
  revert Hunch.  generalize (get_unchanged eqs).
  intros l Hin. induction l.
  - simpl; intros; auto.
    breakAbstraction; tauto.
  - apply limplAdj.
    apply zero_deriv with (x:=a) (cp:=eqs).
    + apply Hin; intuition.
    + apply landL2. reflexivity.
    + Opaque land. simpl (Unchanged (a :: l)).
      apply landR.
      * apply landL2. reflexivity.
      * eapply landL1. apply landAdj.
        eapply IHl.
        intros. eapply Hin. right. assumption.
Qed.

Lemma unchanged_continuous : forall eqs F G,
  (F |-- Continuous eqs) ->
  (F //\\ Unchanged (get_unchanged eqs) |-- G) ->
  (F |-- G).
Proof.
  intros eqs F G Hcont Hunch.
  pose proof (unchanged_continuous_aux eqs).
  charge_tauto.
Qed.
*)

Close Scope HP_scope.