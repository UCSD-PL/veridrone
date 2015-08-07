Require Import Coq.micromega.Psatz.
Require Import Rdefinitions.
Require Import Ranalysis1.
Require Import Rtrigo Rtrigo_reg.
Require Import MVT.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.BasicProofRules.
Require Import TLA.Automation.
Require Import Coq.Reals.R_sqrt.
Require Import Coq.Lists.List.
Open Scope HP_scope.

(* This file contains the statement and soundness
   proof of differential induction.
   Essentially, an invariant inv is a differential
   invariant of a system of differential equations
   diffeqs at some state st if
     1) inv holds at st
     2) if one takes the "syntactic derivative" of inv
        and substitutes the right hand sides of diffeqs
        into this derivative to form inv', then inv'
        holds on any state st'
   There are two important parts to this file:
     1) deriv_formula - takes syntatic derivative and
        performs the substitutions
     2) diff_ind - states the proof rules for
        differential induction and has accompanying
        soundness proof *)

(* The function deriv_formula (below) produces the
   the syntactic derivative of a Formula and substitutes
   the right hand side of the differential equations.
   The following functions are used to implement
   deriv_formula. *)

(* option map on two inputs *)
Definition option_map2 {A B C} (f:A->B->C)
  (a:option A) (b:option B) : option C :=
  match a, b with
    | Some a, Some b => Some (f a b)
    | _, _ => None
  end.

Definition lift2 {A B C D} (f:A->B->C)
  : (D->A)->(D->B)->(D->C) :=
  fun a b c => f (a c) (b c).

(* Tries to take the derivative of a term and substitute
   in the right hand side of differential equations. If
   a variable has no corresponding differential equation
   then this procedure fails and returns None. Otherwise,
   it returns (Some d), where d is the syntatic derivative
   with RHSs of diffeqs substituted in. None can occur
   because in our specification of continuous transitions
   the evolution of variables with no differential equations
   is unspecified. *)
Fixpoint deriv_term (t:Term)
: option (state -> Term) :=
  match t with
  | VarNowT x =>
    Some (fun st => RealT (st x))
  | VarNextT _ => None
  | NatT _ => Some (fun _ => RealT R0)
  | RealT _ => Some (fun _ => RealT R0)
  | PlusT t1 t2 =>
     option_map2 (lift2 PlusT) (deriv_term t1) (deriv_term t2)
  | MinusT t1 t2 =>
     option_map2 (lift2 MinusT) (deriv_term t1) (deriv_term t2)
  | MultT t1 t2 =>
     option_map2 (lift2 PlusT)
                 (option_map (fun t st => MultT (t st) t2)
                             (deriv_term t1))
                 (option_map (fun t st => MultT t1 (t st)) (deriv_term t2))
  | InvT _ => None
  | CosT t =>
    option_map2 (lift2 MultT)
                (Some (fun _ => --sin(t)))
                (deriv_term t)
  | SinT t =>
    option_map2 (lift2 MultT)
                (Some (fun _ => cos(t)))
                (deriv_term t)
  | SqrtT t => None (*
    option_map2 (lift2 MultT)
                (Some (fun _ => MultT (InvT (RealT 2)) (InvT (SqrtT t))))
                (deriv_term t) *)
  | ArctanT t => None (*
    option_map (fun f x => InvT (f x))
               (Some (fun _ => PlusT (RealT R1) (MultT t t)))
*)
  | ExpT t =>
    option_map2 (lift2 MultT)
                (Some (fun _ => exp(t)))
                (deriv_term t)
  | MaxT _ _ => None
  end.

(* Takes the "derivative" of a comparison operator.
   When you take the synthetic derivative of a formula
   with a comparison operator, the operator does not
   necessarily stay the same. For example x < y becomes
   x' <= y' *)
Fixpoint deriv_comp_op (op:CompOp) : CompOp :=
  match op with
    | Gt => Ge
    | Ge => Ge
    | Lt => Le
    | Le => Le
    | Eq => Eq
  end.

(* Tries to take the syntactic derivative of a formula
   and substitute in correspond RHSs of diffeqs. This
   procedure can fail (produce FALSE) for reasons
   described in deriv_term or because I couldn't figure
   out what the derivative should be. It is always
   sound to return FALSE because this is unprovable. *)
Fixpoint deriv_formula (P:state->Formula) (F:Formula) (st:state)
  : Formula :=
  match F with
    | TRUE => TRUE
    | FALSE => FALSE
    | Comp t1 t2 op =>
      match deriv_term t1, deriv_term t2 with
        | Some t1, Some t2 =>
          Comp (t1 st) (t2 st) (deriv_comp_op op)
        | _, _ => FALSE
      end
    | And F1 F2 =>
      (deriv_formula P F1 st) //\\ (deriv_formula P F2 st)
    | Imp F1 F2 =>
      (Continuous P -->> ((F1 -->> next F1) //\\ (next F1 -->> F1)))
      //\\ (F1 -->> (deriv_formula P F2 st))
    | _ => FALSE
  end.

(* Now we have a bunch of messy lemmas that we'll use
   to prove the differential induction (diff_ind) rule.
   Perhaps some day someone will clean these up. *)

(* This lemma says that our notion of syntatic
   derivatives for terms agrees with the actual
   definition of a derivative. *)

Lemma term_deriv : forall (f : R -> state) e e'
  (r : R) is_derivable s,
  deriv_term e = Some e' ->
  { pf : _ |
    forall z,
      (R0 <= z <= r)%R ->
      let f' := (fun t x => derive (fun t => f t x) (is_derivable x) t) in
      eq (derive (fun t => eval_term e (f t) s) pf z)
         (eval_term (e' (f' z)) (f z) s) }.
Proof.
  intros.
  generalize dependent e'.
  induction e; intros; simpl in *.
    - inversion H; clear H; subst.
      simpl. exists (is_derivable v).
      auto.
    - inversion H.
    - inversion H; subst e'.
      unfold eval_term, derive.
      exists (derivable_pt_const (Raxioms.INR n)). intros.
      eapply derive_pt_const.
    - inversion H; subst e'.
      unfold eval_term, derive.
      exists (derivable_pt_const r0). intros.
      eapply derive_pt_const.
    - destruct (deriv_term e1);
      destruct (deriv_term e2);
      simpl in *; try discriminate. inversion H; subst e'.
      specialize (IHe1 t (Logic.eq_refl _)).
      specialize (IHe2 t0 (Logic.eq_refl _)).
      destruct IHe1 as [pf1 IHe1].
      destruct IHe2 as [pf2 IHe2].
      exists (fun r => derivable_pt_plus _ _ _
                                         (pf1 r) (pf2 r)).
      intros.
      pose proof (derive_pt_plus _ _ _ (pf1 z) (pf2 z))
        as Hderiv.
      unfold derive, plus_fct in *. rewrite Hderiv.
      simpl. rewrite IHe1; auto; rewrite IHe2; auto.
    - destruct (deriv_term e1);
      destruct (deriv_term e2);
      simpl in *; try discriminate. inversion H; subst e'.
      specialize (IHe1 t (Logic.eq_refl _)).
      specialize (IHe2 t0 (Logic.eq_refl _)).
      destruct IHe1 as [pf1 IHe1].
      destruct IHe2 as [pf2 IHe2].
      exists (fun r => derivable_pt_minus _ _ _
                                         (pf1 r) (pf2 r)).
      intros.
      pose proof (derive_pt_minus _ _ _ (pf1 z) (pf2 z))
        as Hderiv.
      unfold derive, minus_fct in *. rewrite Hderiv.
      simpl. rewrite IHe1; auto; rewrite IHe2; auto.
    - destruct (deriv_term e1);
      destruct (deriv_term e2);
      simpl in *; try discriminate. inversion H; subst e'.
      specialize (IHe1 t (Logic.eq_refl _)).
      specialize (IHe2 t0 (Logic.eq_refl _)).
      destruct IHe1 as [pf1 IHe1].
      destruct IHe2 as [pf2 IHe2].
      exists (fun r => derivable_pt_mult _ _ _
                                         (pf1 r) (pf2 r)).
      intros.
      pose proof (derive_pt_mult _ _ _ (pf1 z) (pf2 z))
        as Hderiv.
      unfold derive, mult_fct in *. rewrite Hderiv.
      simpl. rewrite IHe1; auto; rewrite IHe2; auto.
    - discriminate.
    - destruct (deriv_term e);
      simpl in *; try discriminate. inversion H; subst e'.
      specialize (IHe t (Logic.eq_refl _)).
      destruct IHe as [pf IHe].
      exists (fun r => derivable_pt_comp
                         _ _ _ (pf r)
                         (derivable_pt_cos
                            (eval_term e (f r) s))).
      intros.
      pose proof (derive_pt_comp _ cos _ (pf z)
                                 (derivable_pt_cos
                                    (eval_term e (f z) s)))
        as Hderiv.
      unfold derive, comp in *. rewrite Hderiv.
      simpl. rewrite IHe; auto; rewrite derive_pt_cos;
      rewrite RIneq.Rminus_0_l; auto.
    - destruct (deriv_term e);
      simpl in *; try discriminate. inversion H; subst e'.
      specialize (IHe t (Logic.eq_refl _)).
      destruct IHe as [pf IHe].
      exists (fun r => derivable_pt_comp
                         _ _ _ (pf r)
                         (derivable_pt_sin
                            (eval_term e (f r) s))).
      intros.
      pose proof (derive_pt_comp _ sin _ (pf z)
                                 (derivable_pt_sin
                                    (eval_term e (f z) s)))
        as Hderiv.
      unfold derive, comp in *. rewrite Hderiv.
      simpl. rewrite IHe; auto. rewrite derive_pt_sin. auto.
    - (** TODO: derivative of sqrt **) inversion H.
    - (** TODO: derivative of arctan **) inversion H.
    - destruct (deriv_term e);
      simpl in *; try discriminate. inversion H; subst e'.
      specialize (IHe t (Logic.eq_refl _)).
      destruct IHe as [pf IHe].
      exists (fun r => derivable_pt_comp
                         _ _ _ (pf r)
                         (Ranalysis4.derivable_pt_exp
                            (eval_term e (f r) s))).
      intros.
      pose proof (derive_pt_comp _ exp _ (pf z)
                                 (Ranalysis4.derivable_pt_exp
                                    (eval_term e (f z) s)))
        as Hderiv.
      unfold derive, comp in *. rewrite Hderiv.
      simpl. rewrite IHe; auto.
      rewrite Ranalysis4.derive_pt_exp. auto.
    - inversion H.
Qed.

Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Option.

Lemma deriv_st_term : forall t t',
  deriv_term t = Some t' ->
  is_st_term t = true /\ (forall x, is_st_term (t' x) = true).
Proof.
  induction t; simpl; auto;
  intros;
  try solve [ discriminate
            | unfold option_map2, option_map in *;
              simpl in *; forward; inv_all; subst;
              repeat match goal with
                     | H : _ |- _ => specialize (H _ eq_refl); destruct H
                     end; simpl; intuition ].
Qed.

Hint Extern 0 (forall x, is_st_term _ = true) =>
  (intros; eapply deriv_st_term; eauto) : rw_rename.

Theorem Rename_Continuous_deriv_term :
  forall (r : RenameMap) (r' : state->Var->Term)
         (c:Evolution),
    (forall x,
        deriv_term (r x) = Some (fun st' => r' st' x)) ->
    Continuous (fun st' => (Forall x : Var, st' x = r' st' x) //\\ Rename r (c st'))
    |-- Rename r (Continuous c).
Proof.
  intros.
  assert ((forall x, is_st_term (r x) = true) /\ (forall x st', is_st_term (r' st' x) = true)).
  { generalize (fun x => @deriv_st_term _ _ (H x)); clear. firstorder. }
  destruct H0 as [ Hst1 Hst2 ].
  eapply Rename_Continuous; eauto. intros. simpl.
  assert (forall v : Var,
             derivable (fun t : R => eval_term (r v) (f t) (f t))).
  { intros. specialize (H v).
    eapply term_deriv in H; eauto.
    destruct H. clear e. revert x.
    instantiate (2 := f).
    instantiate (1 := fun _ => R0).
    intros.
    match goal with
    | _ : derivable ?X |- derivable ?Y =>
      cutrewrite (eq Y X); eauto
    end.
    eapply FunctionalExtensionality.functional_extensionality.
    intros.
    eapply st_term_hd; eauto. }
  { exists H0. intros.
    specialize (H v).
    unfold deriv_stateF.
    eapply term_deriv in H.
    revert H. instantiate (2 := f).
    instantiate (1 := fun _ => R0).
    instantiate (1 := pf2).
    instantiate (1:=z).
    destruct 1.
    simpl in e. specialize (e z).
    rewrite st_term_hd with (s3:=fun _ : Var => 0%R).
    rewrite <- e.
    apply Ranalysis4.pr_nu_var.
    eapply FunctionalExtensionality.functional_extensionality.
    intros. apply st_term_hd.
    apply Hst1.
    psatzl R.
    apply Hst2.
    Grab Existential Variables.
    exact R0.
    auto. }
Qed.

Definition deriv_term_succeed (t : Term) :=
  match deriv_term t with
  | Some t => t
  | None => fun _ => R0
  end.

Fixpoint deriv_term_RenameList (l : list (Var*Term))
         (st' : state) : RenameMap :=
  match l with
  | nil => st'
  | (v, t) :: l =>
    fun x => if String.string_dec x v
             then deriv_term_succeed t st'
             else deriv_term_RenameList l st' x
  end.

Lemma deriv_term_list : forall l,
  List.forallb (fun p => match deriv_term (snd p) with
                         | None => false
                         | Some _ => true
                         end) l = true ->
  forall x,
    deriv_term (to_RenameMap l x) =
    Some (fun st' => deriv_term_RenameList l st' x).
Proof.
  induction l.
  - reflexivity.
  - simpl. destruct a. simpl.
    destruct (deriv_term t) eqn:?.
    + intros. destruct (String.string_dec x v).
      * subst. unfold deriv_term_succeed. rewrite Heqo.
        reflexivity.
      * rewrite IHl; auto.
    + inversion 1.
Qed.

(* Here are a few tactics for proving our main
   helper lemma: eval_comp_ind. It's probably
   best not to try to understand these tactics. *)

Ltac normalize_ineq_goal :=
  match goal with
    | [ |- Rgt _ _ ]
      => apply RIneq.Rminus_gt; apply RIneq.Rlt_gt
    | [ |- Rge _ _ ]
      => apply RIneq.Rminus_ge; apply RIneq.Rle_ge
    | [ |- Rlt _ _ ]
      => apply RIneq.Rminus_lt; apply RIneq.Ropp_lt_cancel;
         rewrite RIneq.Ropp_minus_distr; rewrite RIneq.Ropp_0
    | [ |- Rle _ _ ]
      => apply RIneq.Rminus_le; apply RIneq.Ropp_le_cancel;
         rewrite RIneq.Ropp_minus_distr; rewrite RIneq.Ropp_0
    | [ |- eq _ _ ]
      => apply RIneq.Rminus_diag_uniq
  end.

Ltac normalize_ineq_hyp H :=
  match type of H with
    | context [Rgt _ _] => eapply RIneq.Rgt_minus in H;
                          eapply RIneq.Rgt_lt in H
    | context [Rge _ _] => eapply RIneq.Rge_minus in H;
                          eapply RIneq.Rge_le in H
    | context [Rlt _ _] => eapply RIneq.Rlt_minus in H;
       eapply RIneq.Ropp_lt_contravar in H;
       rewrite RIneq.Ropp_minus_distr in H;
       rewrite RIneq.Ropp_0 in H
    | context [Rle _ _] => eapply RIneq.Rle_minus in H;
       eapply RIneq.Ropp_le_contravar in H;
       rewrite RIneq.Ropp_minus_distr in H;
       rewrite RIneq.Ropp_0 in H
    | context [ eq _ _ ] => apply RIneq.Rminus_diag_eq in H
  end.

Ltac ineq_trans :=
  match goal with
    | [ H : Rlt ?r1 ?r2 |- Rlt ?r1 ?r3 ]
        => apply (RIneq.Rlt_le_trans r1 r2 r3)
    | [ H : Rle ?r1 ?r2 |- Rle ?r1 ?r3 ]
        => apply (RIneq.Rle_trans r1 r2 r3)
    | [ H : Rlt ?r2 ?r3 |- Rlt ?r1 ?r3 ]
        => apply (RIneq.Rlt_le_trans r1 r2 r3)
    | [ H : Rle ?r2 ?r3 |- Rle ?r1 ?r3 ]
        => apply (RIneq.Rle_trans r1 r2 r3)
    | [ H : eq (Rminus (eval_term ?t1 _ _)
                       (eval_term ?t2 _ _)) ?r3
        |- Rle ?r3 (Rminus (eval_term ?t1 _ _)
                           (eval_term ?t2 _ _)) ]
        => rewrite <- H
    | [ H : eq (Rminus (eval_term ?t2 _ _)
                       (eval_term ?t1 _ _)) ?r3
        |- Rle ?r3 (Rminus (eval_term ?t1 _ _)
                           (eval_term ?t2 _ _)) ]
        => apply RIneq.Rminus_diag_uniq in H;
           symmetry in H; apply RIneq.Rminus_diag_eq in H;
           rewrite <- H
  end.

Ltac deriv_ineq :=
  match goal with
    | [ |- Rle (eval_term ?t1 (?f ?r1) ?s -
                eval_term ?t2 (?f _) ?s)
            (eval_term ?t1 (?f ?r2) ?s -
             eval_term ?t2 (?f _) ?s) ]
        => eapply (derive_increasing_interv_var r1 r2
                     (fun z => eval_term t1 (f z) s -
                               eval_term t2 (f z) s)%R); eauto
    | [ |- @eq R
               (Rminus (eval_term ?t1 (?f _) ?s)
                       (eval_term ?t2 (?f _) ?s))
               (Rminus (eval_term ?t1 (?f _) ?s)
                       (eval_term ?t2 (?f _) ?s))]
        => eapply (null_derivative_loc
                 (fun z => (eval_term t1 (f z) s -
                            eval_term t2 (f z) s)%R)); eauto
  end.

Ltac solve_ineq := psatzl R.

Lemma eval_next_term : forall t s1 s2 s3,
  is_st_term t = true ->
  eval_term (next_term t) s1 s2 =
  eval_term t s2 s3.
Proof.
  induction t; simpl; auto; intros;
  try discriminate;
  try (try apply andb_prop in H; intuition;
       erewrite IHt1; eauto;
       erewrite IHt2; eauto).
Qed.

Lemma is_solution_sub : forall f eqs r1 r2,
  (r1 <= r2)%R ->
  is_solution f eqs r2 ->
  is_solution f eqs r1.
Proof.
  intros f eqs r1 r2 Hr Hsol.
  unfold is_solution in *.
  destruct Hsol as [pf Hsol].
  exists pf. unfold solves_diffeqs in *.
  intros x d.
  apply Hsol; auto.
  psatzl R.
Qed.

Definition derive_stateF (f : R -> state) (is_derivable : forall x, derivable (fun t => f t x))
: R -> state :=
  fun t v => derive (fun t => f t v) (is_derivable v) t.

Lemma deriv_neg : forall f t1 t2 t1' t2' r eqs is_derivable s,
  solves_diffeqs f eqs r is_derivable ->
  deriv_term t1 = Some t1' ->
  deriv_term t2 = Some t2' ->
  forall t,
    (R0 <= t <= r)%R ->
    exists pf,
      let f' := derive_stateF f is_derivable in
      (forall st,
          (0 <= eval_term (t1' (f' t)) st s - eval_term (t2' (f' t)) st s)%R) ->
      (R0 <=
    derive_pt
      (fun z : R => eval_term t1 (f z) s -
                    eval_term t2 (f z) s)
      t pf)%R.
Proof.
  intros f t1 t2 t1' t2' r diffeqs is_derivable s Hsol
         Ht1 Ht2 t Ht.
  pose proof (term_deriv f (t1-t2) (fun st' => t1' st' - t2' st') r
                         is_derivable s) as Hderiv.
  simpl in *. rewrite Ht1 in *. rewrite Ht2 in *. simpl in *.
  specialize (Hderiv (Logic.eq_refl _)).
  destruct Hderiv as [pf Hderiv]. exists (pf t).
  unfold derive in *. rewrite Hderiv; auto.
Qed.

(* Main helper lemma for diff_ind. Basically
   establishes the base case for diff_ind. The
   proof of this lemma is a complete mess. *)
Lemma eval_comp_ind : forall Hyps Pdiff
                             t1 t2 t1' t2' op
  (Hpdiff:forall st, is_st_formula (Pdiff st)),
  deriv_term t1 = Some t1' ->
  deriv_term t2 = Some t2' ->
  is_st_formula Hyps ->
  (|-- (Hyps //\\ Continuous Pdiff) -->> next Hyps) ->
  (|-- Hyps -->> (Forall x, Pdiff x -->> Comp (t1' x) (t2' x) (deriv_comp_op op))) ->
  (|-- (Comp t1 t2 op //\\ Hyps //\\
             Continuous Pdiff) -->>
       Comp (next_term t1) (next_term t2) op).
Proof.
  intros Hyps eqs t1 t2 t1' t2' op Hpdiff Ht1 Ht2 Hst Hhyps Hind.
  breakAbstraction; unfold eval_comp in *; simpl in *.
  intros tr XX H; clear XX; destruct H as [Hbase [HhypsI Hcont] ].

  destruct Hcont as [r [f Hcont] ];
    destruct Hcont as [Hr [Hsol [? ?] ] ].
  pose proof (proj1 (deriv_st_term _ _ Ht1)).
  pose proof (proj1 (deriv_st_term _ _ Ht2)).
  repeat rewrite eval_next_term with (s3:=Stream.hd (Stream.tl tr)); auto.
  unfold is_solution in *. destruct Hsol as [pf Hsol].
  pose proof (term_deriv f (t1 - t2) (fun st' => t1' st' - t2' st')
                         r pf (Stream.hd (Stream.tl tr)))
    as Hterm1.
  pose proof (term_deriv f (t2 - t1) (fun st' => t2' st' - t1' st')
                         r pf (Stream.hd (Stream.tl tr)))
    as Hterm2.
  rewrite <- H in *.
  rewrite <- H0 in *.
  simpl in *; rewrite Ht1 in Hterm1;
  rewrite Ht1 in Hterm2; rewrite Ht2 in Hterm1;
  rewrite Ht2 in Hterm2; simpl in *.
  specialize (Hterm1 (eq_refl _)).
  specialize (Hterm2 (eq_refl _)).
  unfold derive in Hterm1. unfold derive in Hterm2.
  destruct Hterm1 as [pf1 Hterm1].
  destruct Hterm2 as [pf2 Hterm2].
  destruct op; simpl in *; try (apply RIneq.Rle_le_eq; split);
  normalize_ineq_goal; normalize_ineq_hyp Hbase;
  ineq_trans; auto;
  deriv_ineq; intros; try solve_ineq;
  (instantiate (1:=pf1) || instantiate (1:=pf2));
  (rewrite Hterm1 || rewrite Hterm2); try solve_ineq;
  try specialize (Hhyps (Stream.Cons (Stream.hd tr)
                              (Stream.Cons (f t) (Stream.tl tr))) I);
  simpl in *; try apply next_formula_tl in Hhyps; auto;
  try specialize (Hind (Stream.Cons (f t) (Stream.tl tr)) I); simpl in *;
  try specialize (Hind Hhyps); try solve_ineq;
  try (split;
        [ eapply st_formula_hd; eauto |
          exists t; exists f; repeat split; try solve_ineq; auto;
          solve [apply is_solution_sub with (r2:=r);
                  try solve_ineq; unfold is_solution; eauto]
      ]);
  specialize (Hind (fun x : Var => derive_pt (fun t0 : R => f t0 x) t (pf x t)));
  unfold solves_diffeqs in *; rewrite H0;
  assert (0 <= t <= r)%R as Ht by solve_ineq;
  specialize (Hsol t Ht);
  eapply st_formula_hd in Hsol; try apply Hind in Hsol;
  try solve_ineq; auto.
Qed.

Lemma Continuous_deriv_exists :
  forall Pdiff tr,
    (forall st, is_st_formula (Pdiff st)) ->
    eval_formula (Continuous Pdiff) tr ->
    exists st, eval_formula (Pdiff st) tr.
Proof.
  breakAbstraction. intros. destruct H0 as [r [f H0]].
  unfold is_solution, solves_diffeqs in *.
  destruct H0 as [? [ [? ?] [? ?] ] ]. eexists.
  eapply st_formula_hd with (tr1:=Stream.forever (f R0)); eauto.
  apply H1; solve_ineq.
Qed.

(* Differential induction proof rule plus soundness
   proof. *)
Lemma diff_ind : forall Hyps G cp F,
  is_st_formula G ->
  is_st_formula Hyps ->
  (F |-- Continuous cp) ->
  (forall st, is_st_formula (cp st)) ->
  ((Hyps //\\ Continuous cp) |-- next Hyps) ->
  (F |-- G) ->
  (F |-- Hyps) ->
  (Hyps |-- Forall st, cp st -->> deriv_formula cp G st) ->
  (F |-- next G).
Proof.
  Opaque Continuous.
  intros Hyps G; generalize dependent Hyps;
  induction G;
    intros Hyps cp F HstG HstH Hcont Hcp Hhyps Hbase HhypsF Hind;
    simpl in *; unfold tlaEntails in *; simpl in *; intros; trivial;
    try solve [ pose proof (Hcont tr) as Hcont2;
                eapply Continuous_deriv_exists in Hcont2; auto;
                destruct Hcont2 as [st Hcont2]; exfalso;
                eapply Hind; eauto ].
  - destruct HstG as [HstG1 HstG2].
    pose proof (HhypsF _ H) as HhypsF2. pose proof Hcont as Hcont2.
    pose proof (Hind _ HhypsF2). eapply Continuous_deriv_exists in Hcont2; eauto.
    destruct (deriv_term t) eqn:?;
             destruct (deriv_term t0) eqn:?;
    try solve [destruct Hcont2; exfalso; eapply Hind; eauto].
    pose proof (eval_comp_ind Hyps cp t t0
                              t1 t2 c Hcp Heqo Heqo0 HstH) as Hcomp.
    apply Hcomp.
    { breakAbstraction. intros. eauto. }
    { breakAbstraction. intros. eauto. }
    { breakAbstraction. auto. }
    { fold eval_formula. repeat split; eauto.
      try eapply Hbase; eauto. }
  - split.
    + eapply IHG1; eauto.
      * intuition.
      * apply Hbase; auto.
      * apply Hind; auto.
    + eapply IHG2; eauto.
      * intuition.
      * apply Hbase; auto.
      * apply Hind; auto.
  - eapply IHG2 with (Hyps:=Hyps //\\ G1) (F:=F //\\ G1); eauto;
    simpl; intuition.
    + pose proof H5 as Hcont2;
      eapply Continuous_deriv_exists in Hcont2; destruct Hcont2;
      auto; specialize (Hind tr0 H3 _ H4); apply Hind; auto.
    + specialize (Hind tr0 H4); apply Hind; auto.
    + specialize (HhypsF _ H). pose proof (Hcont _ H) as Hcont2.
      eapply Continuous_deriv_exists in Hcont2; destruct Hcont2 as [st Hcont2].
      specialize (Hind _ HhypsF _ Hcont2). apply Hind; auto. auto.
Qed.

Close Scope HP_scope.
