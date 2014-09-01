Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Syntax.
Require Import Semantics.
Require Import List.
Require Import Sumbool.
Require Import Coq.Reals.MVT.
Require Import String.

(************************************************)
(* Some proof rules.                            *)
(************************************************)
Open Scope HP_scope.

(* Implication introduction *)
Lemma imp_intro : forall f f' st,
  (eval_formula f st ->
   eval_formula f' st) ->
  eval_formula (f --> f') st.
Proof. auto. Qed.

(* The following three functions will be used to state
   the differential induction rule (diff_ind) below.
   Essentially, an invariant inv is a differential
   invariant of a system of differential equations
   diffeqs at some state st if
     1) inv holds at st
     2) if one takes the "derivative" of inv
        and substitutes the right hand sides of diffeqs
        into this derivative to form inv', then inv'
        holds on any state st'
   The derivative of a formula and substitution of
   differential equations right hand sides is implemented
   in the following three functions. *)
(* Takes a var x and list of differential equations
   and returns Some t if (x' := t) is in the list of
   differential equations. Returns None otherwise. *)
Definition get_deriv (x:Var) (eqs:list (Var * Term))
  : option Term :=
  option_map (@snd Var Term)
    (find (fun p : Var * Term => let (y, t) := p in
          proj1_sig (bool_of_sumbool (string_dec x y))) eqs).

(* Takes the derivative of a term and substitutes in
   the right hand side of differential equations. If
   a variable has no corresponding differential equation
   then 0 is substituted. This is because variables
   without specified derivatives have a derivative of 0. *)
Fixpoint deriv_term (t:Term) (eqs:list (Var * Term))
  : Term :=
  match t with
  | VarT x =>
    match get_deriv x eqs with
      | Some t => t
      | None   => RealT R0
    end
  | RealT r => RealT R0
  | PlusT t1 t2 =>
     (deriv_term t1 eqs) + (deriv_term t2 eqs)
  | MinusT t1 t2 =>
     (deriv_term t1 eqs) - (deriv_term t2 eqs)
  | MultT t1 t2 =>
     ((deriv_term t1 eqs) * t2) + (t1 * (deriv_term t2 eqs))
  end.

(* For some formulas, differential induction does not work,
   so we use the following unprovable formula in those
   cases. *)
Definition FalseFormula : Formula := 0 > 1.

Lemma FalseFormulaFalse : forall st,
  ~eval_formula FalseFormula st.
Proof.
  intros. simpl. apply RIneq.Rle_not_gt.
  apply RIneq.Rle_0_1.
Qed.

(* The derivative of a formula is essentially the derivative
   of each of its terms (with some exceptions not shown
   here). *)
Fixpoint deriv_formula (f:Formula) (eqs:list (Var * Term))
  : Formula :=
  match f with
  | GtF t1 t2 => (deriv_term t1 eqs) >= (deriv_term t2 eqs)
  | EqF t1 t2 => EqF (deriv_term t1 eqs) (deriv_term t2 eqs)
  | AndF f1 f2 => AndF (deriv_formula f1 eqs)
                      (deriv_formula f2 eqs)
  | OrF f1 f2 => AndF (deriv_formula f1 eqs)
                      (deriv_formula f2 eqs)
  | Imp f1 f2 => FalseFormula
     (*I'm not sure what the condition is in this case
       but I think the following is wrong. *)
     (*Imp (deriv_formula f1 eqs)
           (deriv_formula f2 eqs)*)
  | ForallState p f => FalseFormula
     (*I don't think differential induction works here.*)
     (*ForallState p (deriv_formula f eqs)*)
  end.

(* Now we have a bunch of messy lemmas that we'll use
   to prove the differential induction (diff_ind) rule. *)
Lemma term_is_derivable : forall (f : R -> state) (e : Term),
  (forall x, derivable (fun t => f t x)) ->
  derivable (fun t => eval_term e (f t)).
Proof.
  intros f e.
  induction e; simpl; intro is_derivable.
    - auto.
    - apply derivable_const.
    - apply derivable_plus; auto.
    - apply derivable_minus; auto.
    - apply derivable_mult; auto.
(*    - apply derivable_div; auto.*)
Qed.

Lemma get_deriv_in : forall x eqs t,
  get_deriv x eqs = Some t ->
  List.In (x, t) eqs.
Proof.
  intros x eqs t Hderiv.
  induction eqs.
    - unfold get_deriv in *. simpl in *. discriminate.
    - unfold get_deriv in *. simpl in *. destruct a.
      destruct (string_dec x v) eqn:?; simpl in *;
        intuition congruence.
Qed.

Lemma get_deriv_not_in : forall x eqs,
  get_deriv x eqs = None ->
  ~exists t, List.In (x, t) eqs.
Proof.
  intros x eqs Hderiv.
  induction eqs.
    - intro H. destruct H. auto.
    - intro H. destruct H. simpl in *.
      destruct H.
      + subst a. unfold get_deriv in *. simpl in *.
        destruct (string_dec x x); simpl in *;
        intuition discriminate.
      + unfold get_deriv in *. simpl in *. destruct a.
        destruct (string_dec x v); simpl in *.
        * discriminate.
        * intuition. eauto.
Qed.

Lemma term_deriv : forall (f : R -> state) (e : Term)
  (r : R) (diffeqs : list (Var * Term)) is_derivable s,
  solves_diffeqs f diffeqs r is_derivable ->
  vars_unchanged f diffeqs r s ->
  forall z, 
    (R0 <= z <= r)%R ->
    derive (fun t => eval_term e (f t))
           (term_is_derivable f e is_derivable) z =
    eval_term (deriv_term e diffeqs) (f z).
Proof.
  intros. unfold derive.
  apply (derive_pt_D_in
           (fun t : R => eval_term e (f t))
           (fun t : R => eval_term (deriv_term e diffeqs)
                                   (f t))).
  induction e; intros; simpl in *.
    - destruct (get_deriv v diffeqs) eqn:?.
      + unfold solves_diffeqs in *.
        unfold derive in *.
        specialize (H v t (get_deriv_in _ _ _ Heqo) z H1).
        apply (derive_pt_D_in
                 (fun t0 : R => f t0 v)
                 (fun t0 : R => eval_term t (f t0))) in H.
        auto.
      + apply (derive_pt_D_in _ _ _
         (term_is_derivable _ (VarT v) is_derivable z)).
        simpl. unfold vars_unchanged, derive in *.
        specialize (H0 v (get_deriv_not_in v diffeqs Heqo)
                       z H1).
        transitivity (derive_pt (fun t : R => f t v) z
                                (s v z)).
        apply pr_nu.
        apply H0.
    - apply Dconst.
    - apply Dadd; auto.
    - apply Dminus; auto.
    - apply Dmult; auto.
Qed.

(* Differential induction *)
Lemma diff_ind : forall diffeqs b inv st,
  eval_formula inv st ->
  (forall st, eval_formula (deriv_formula inv diffeqs) st) ->
  eval_formula ([DiffEq diffeqs b]inv) st.
Proof.
  intros diffeqs b inv st Hbase Hind.
  simpl; intros st' Htrans; inversion_clear Htrans.
  generalize dependent st.
  generalize dependent st'.
  induction inv; simpl in *; intros.
    - apply RIneq.Rminus_gt. apply RIneq.Rgt_minus in Hbase.
      cut (eval_term t st - eval_term t0 st <=
           eval_term t st' - eval_term t0 st')%R.
      + intros. apply RIneq.Rlt_gt.
        apply RIneq.Rgt_lt in Hbase.
        apply RIneq.Rlt_le_trans with
          (r2 := (eval_term t st - eval_term t0 st)%R); auto.
      + subst st. subst st'.
        eapply (derive_increasing_interv_var
                 0 r (fun z =>
                        eval_term t (f z) -
                        eval_term t0 (f z))%R); eauto.
        * intros. specialize (Hind (f t1)).
          apply RIneq.Rge_minus in Hind.
          apply RIneq.Rge_le in Hind.
          erewrite <- term_deriv in Hind; eauto.
          erewrite <- term_deriv in Hind; eauto.
          unfold derive in Hind.
          rewrite <- derive_pt_minus in Hind.
          apply Hind.
          destruct H0.
          split; try apply RIneq.Rlt_le; auto.
          destruct H0.
          split; try apply RIneq.Rlt_le; auto.
        * split; try apply RIneq.Rle_refl;
          apply RIneq.Rlt_le; auto.
        * split; try apply RIneq.Rle_refl;
          apply RIneq.Rlt_le; auto.
    - apply RIneq.Rminus_diag_uniq.
      apply RIneq.Rminus_diag_eq in Hbase.
      transitivity (eval_term t st - eval_term t0 st)%R.
      * subst st. subst st'.
        eapply (null_derivative_loc
                 (fun z => (eval_term t (f z) -
                            eval_term t0 (f z))%R)).
        intros. specialize (Hind (f x)).
        apply RIneq.Rminus_diag_eq in Hind.
        erewrite <- term_deriv in Hind; eauto.
        erewrite <- term_deriv in Hind; eauto.
        unfold derive in Hind.
        apply continuity_pt_minus.
        apply derivable_continuous_pt.
        apply term_is_derivable; auto.
        apply derivable_continuous_pt.
        apply term_is_derivable; auto.
        intros. specialize (Hind (f x)).
        apply RIneq.Rminus_diag_eq in Hind.
        erewrite <- term_deriv in Hind; eauto.
        erewrite <- term_deriv in Hind; eauto.
        unfold derive in *.
        rewrite <- derive_pt_minus in Hind.
        apply Hind.
        destruct P.
        split; try apply RIneq.Rlt_le; auto.
        destruct P.
        split; try apply RIneq.Rlt_le; auto.
        split; try apply RIneq.Rle_refl;
        apply RIneq.Rlt_le; auto.
      * auto.
    - split.
      + eapply IHinv1; eauto. apply Hind. apply Hbase.
      + eapply IHinv2; eauto. apply Hind. apply Hbase.
    - destruct Hbase.
      + left. eapply IHinv1; eauto. apply Hind.
      + right. eapply IHinv2; eauto. apply Hind.
    - specialize (Hind (fun _ => R0)). 
      destruct (FalseFormulaFalse st' Hind).
    - specialize (Hind (fun _ => R0)). 
      destruct (FalseFormulaFalse st' Hind).
Qed.

(* A tactic for applying all of our proof rules. *)
Ltac apply_proof_rules :=
  repeat (intros; match goal with
                    | [ |- _ ] => apply imp_intro
                    | [ |- _ ] => apply diff_ind
                  end).

Close Scope HP_scope.