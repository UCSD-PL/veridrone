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

(* Takes a var x and list of differential equations
   and returns Some t if (x' := t) is in the list of
   differential equations. Returns None otherwise. *)
Definition get_deriv (x:Var) (eqs:list DiffEq)
  : option Term :=
  option_map get_term
    (List.find (fun p : DiffEq => let (y, t) := p in
          proj1_sig (Sumbool.bool_of_sumbool
                       (String.string_dec x y))) eqs).

(* option map on two inputs *)
Definition option_map2 {A B C} (f:A->B->C) 
  (a:option A) (b:option B) : option C :=
  match a, b with
    | Some a, Some b => Some (f a b)
    | _, _ => None
  end.

(* Tries to take the derivative of a term and substitute
   in the right hand side of differential equations. If
   a variable has no corresponding differential equation
   then this procedure fails and returns None. Otherwise,
   it returns (Some d), where d is the syntatic derivative
   with RHSs of diffeqs substituted in. None can occur
   because in our specification of continuous transitions
   the evolution of variables with no differential equations
   is unspecified. *)
Fixpoint deriv_term (t:Term) (eqs:list DiffEq)
  : option Term :=
  match t with
  | VarNowT x =>
    get_deriv x eqs
  | VarNextT _ => None
  | NatT _ => Some (RealT R0)
  | RealT _ => Some (RealT R0)
  | PlusT t1 t2 =>
     option_map2 PlusT (deriv_term t1 eqs) (deriv_term t2 eqs)
  | MinusT t1 t2 =>
     option_map2 MinusT (deriv_term t1 eqs) (deriv_term t2 eqs)
  | MultT t1 t2 =>
     option_map2 PlusT
                 (option_map (fun t => MultT t t2)
                             (deriv_term t1 eqs))
                 (option_map (MultT t1) (deriv_term t2 eqs))
  | InvT _ => None
  | CosT t =>
    option_map2 MultT
                (Some --sin(t))
                (deriv_term t eqs)
  | SinT t =>
    option_map2 MultT
                (Some cos(t))
                (deriv_term t eqs)
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
Fixpoint deriv_formula (F:Formula) (eqs:list DiffEq) :=
  match F with
    | TRUE => TRUE
    | FALSE => FALSE
    | Comp t1 t2 op =>
      match deriv_term t1 eqs, deriv_term t2 eqs with
        | Some t1, Some t2 =>
          Comp t1 t2 (deriv_comp_op op)
        | _, _ => FALSE
      end
    | And F1 F2 =>
      (deriv_formula F1 eqs) //\\ (deriv_formula F2 eqs)
    | Imp F1 F2 =>
      (Continuous eqs -->> ((F1 -->> next F1) //\\ (next F1 -->> F1)))
      //\\ (F1 -->> (deriv_formula F2 eqs))
    | _ => FALSE
  end.

(* Now we have a bunch of messy lemmas that we'll use
   to prove the differential induction (diff_ind) rule.
   Perhaps some day someone will clean these up. *)

Lemma get_deriv_in : forall x eqs t,
  get_deriv x eqs = Some t ->
  List.In (DiffEqC x t) eqs.
Proof.
  intros x eqs t Hderiv.
  induction eqs.
    - unfold get_deriv in *. simpl in *. discriminate.
    - unfold get_deriv in *. simpl in *. destruct a.
      destruct (String.string_dec x v) eqn:?; simpl in *;
        intuition congruence.
Qed.

Lemma get_deriv_not_in : forall x eqs,
  get_deriv x eqs = None ->
  ~exists t, List.In (DiffEqC x t) eqs.
Proof.
  intros x eqs Hderiv.
  induction eqs.
    - intro H. destruct H. auto.
    - intro H. destruct H. simpl in *.
      destruct H.
      + subst a. unfold get_deriv in *. simpl in *.
        destruct (String.string_dec x x); simpl in *;
        intuition discriminate.
      + unfold get_deriv in *. simpl in *. destruct a.
        destruct (String.string_dec x v); simpl in *.
        * discriminate.
        * intuition. eauto.
Qed.

(* This lemma says that our notation of syntatic
   derivatives for terms agrees with the actual
   definition of a derivative. *)
Lemma term_deriv : forall (f : R -> state) (e e' : Term)
  (r : R) (eqs : list DiffEq) is_derivable s,
  solves_diffeqs f eqs r is_derivable ->
  deriv_term e eqs = Some e' ->
  exists pf,
  forall z,
    (R0 <= z <= r)%R ->
      eq (derive (fun t => eval_term e (f t) s)
             (*(term_is_derivable f e s is_derivable)*) pf z)
         (eval_term e' (f z) s).
Proof.
  intros.
(*  apply (derive_pt_D_in
           (fun t : R => eval_term e (f t) s)
           (fun t : R => eval_term e' (f t) s)).*)
  generalize dependent e'.
  induction e; intros; simpl in *.
    - destruct (get_deriv v eqs) eqn:?.
      + unfold solves_diffeqs in *.
        unfold derive in *.
        exists (is_derivable v). intros.
        specialize (H v t s (get_deriv_in _ _ _ Heqo) z H1).
(*        apply (derive_pt_D_in
                 (fun t0 : R => f t0 v)
                 (fun t0 : R => eval_term t (f t0) s)) in H.*)
        inversion H0; subst e'; eauto.
      + discriminate.
    - inversion H0.
    - inversion H0; subst e'.
      unfold eval_term, derive.
      exists (derivable_pt_const (Raxioms.INR n)). intros.
      eapply derive_pt_const.
    - inversion H0; subst e'.
      unfold eval_term, derive.
      exists (derivable_pt_const r0). intros.
      eapply derive_pt_const.
    - destruct (deriv_term e1 eqs);
      destruct (deriv_term e2 eqs);
      simpl in *; try discriminate. inversion H0; subst e'.
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
    - destruct (deriv_term e1 eqs);
      destruct (deriv_term e2 eqs);
      simpl in *; try discriminate. inversion H0; subst e'.
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
    - destruct (deriv_term e1 eqs);
      destruct (deriv_term e2 eqs);
      simpl in *; try discriminate. inversion H0; subst e'.
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
    - destruct (deriv_term e eqs);
      simpl in *; try discriminate. inversion H0; subst e'.
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
    - destruct (deriv_term e eqs);
      simpl in *; try discriminate. inversion H0; subst e'.
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

(* States correctness of VarsAgree *)
Lemma deriv_trace_now : forall f eqs t t' tr s,
  eval_formula (VarsAgree (List.map get_var eqs) (f R0)) tr ->
  deriv_term t eqs = Some t' ->
  eval_term t (Stream.hd tr) s = eval_term t (f R0) s.
Proof.
  induction t; simpl; intros; auto.
  - induction eqs.
    + unfold get_deriv in *.
      simpl in *. discriminate.
    + unfold get_deriv in *. simpl in *.
      destruct H. destruct a.
      destruct (String.string_dec v v0); simpl in *.
      * subst v0; unfold eval_comp in *; simpl in *; auto.
      * apply IHeqs; auto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    unfold eval_term in *; simpl in *;
      erewrite IHt1; eauto;
      erewrite IHt2; eauto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    unfold eval_term in *; simpl in *;
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    unfold eval_term in *; simpl in *;
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
  - discriminate.
  - destruct (deriv_term t eqs) eqn:?;
             try discriminate.
    unfold eval_term in *; simpl in *;
    erewrite IHt; eauto.
  - destruct (deriv_term t eqs) eqn:?;
             try discriminate.
    unfold eval_term in *; simpl in *;
    erewrite IHt; eauto.
Qed.

(* States correctness of AVarsAgree *)
Lemma deriv_trace_next : forall f eqs (r:R) t t' tr s,
  eval_formula (AVarsAgree (List.map get_var eqs) (f r)) tr ->
  deriv_term t eqs = Some t' ->
  eval_term t (Stream.hd (Stream.tl tr)) s = eval_term t (f r) s.
Proof.
  induction t; simpl; intros; auto.
  - induction eqs.
    + unfold get_deriv in *.
      simpl in *. discriminate.
    + unfold get_deriv in *. simpl in *.
      destruct H. destruct a.
      destruct (String.string_dec v v0); simpl in *.
      * subst v0; unfold eval_comp in *; simpl in *; auto.
      * apply IHeqs; auto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    unfold eval_term in *; simpl in *;
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    unfold eval_term in *; simpl in *;
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    unfold eval_term in *; simpl in *;
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
  - discriminate.
  - destruct (deriv_term t eqs) eqn:?;
             try discriminate.
    unfold eval_term in *; simpl in *;
    erewrite IHt; eauto.
  - destruct (deriv_term t eqs) eqn:?;
             try discriminate.
    unfold eval_term in *; simpl in *;
    erewrite IHt; eauto.
Qed.

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

Lemma deriv_st_term : forall t t' eqs,
  deriv_term t eqs = Some t' ->
  is_st_term t = true.
Proof.
  induction t; simpl; auto;
  intros; try discriminate;
  try (unfold option_map2 in *;
        simpl in *;
        destruct (deriv_term t1 eqs) eqn:?;
                 destruct (deriv_term t2 eqs) eqn:?;
                 try discriminate;
       apply andb_true_intro;
       split; try eapply IHt1;
       try eapply IHt2; eauto).
  - destruct (deriv_term t eqs) eqn:?;
             try discriminate;
    eapply IHt; eauto.
  - destruct (deriv_term t eqs) eqn:?;
             try discriminate;
    eapply IHt; eauto.
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
  intros x d s Hin z Hz.
  apply Hsol; auto.
  psatzl R.
Qed.

Lemma deriv_neg : forall f t1 t2 t1' t2' r eqs is_derivable s,
  solves_diffeqs f eqs r is_derivable ->
  deriv_term t1 eqs = Some t1' ->
  deriv_term t2 eqs = Some t2' ->
  (forall st,
     (R0 <= eval_term t1' st s -
      eval_term t2' st s)%R) ->
  forall t,
    (R0 <= t <= r)%R ->
    exists pf,
    (R0 <=
    derive_pt
      (fun z : R => eval_term t1 (f z) s -
                    eval_term t2 (f z) s)
      t pf)%R.
Proof.
  intros f t1 t2 t1' t2' r diffeqs is_derivable s Hsol
         Ht1 Ht2 Hineq t Ht.
  specialize (Hineq (f t)).
  pose proof (term_deriv f (t1-t2) (t1'-t2') r diffeqs
                         is_derivable s Hsol) as Hderiv.
  simpl in *. rewrite Ht1 in *. rewrite Ht2 in *. simpl in *.
  specialize (Hderiv (Logic.eq_refl _)).
  destruct Hderiv as [pf Hderiv]. exists (pf t).
  unfold derive in *. rewrite Hderiv; auto.
Qed.

Lemma st_term_hd : forall t s1 s2 s3,
  is_st_term t = true ->
  eval_term t s1 s2 =
  eval_term t s1 s3.
Proof.
  induction t; intros s1 s2 s3 Hst;
  simpl in *; auto; try discriminate;
  try (try apply andb_prop in Hst; simpl;
       try erewrite IHt1; intuition).
Qed.

Lemma st_formula_hd : forall F tr1 tr2,
  is_st_formula F ->
  eval_formula F tr1 ->
  Stream.hd tr1 = Stream.hd tr2 ->
  eval_formula F tr2.
Proof.
  induction F; intros; simpl in *; auto;
  try tauto; try discriminate.
  - unfold eval_comp in *. simpl in *.
    rewrite st_term_hd with (t:=t) (s3:=Stream.hd (Stream.tl tr1));
      intuition.
    rewrite st_term_hd with (t:=t0) (s3:=Stream.hd (Stream.tl tr1));
      intuition.
    rewrite <- H1; auto.
  - split; try eapply IHF1; try eapply IHF2;
    intuition; eauto.
  - destruct H0;
    [ left; eapply IHF1 |
      right; eapply IHF2 ];
    intuition; eauto.
  - intros. eapply IHF2; eauto; intuition.
    apply H0. eapply IHF1; eauto.
  - destruct H1. exists x. eapply H; eauto.
  - intros. eapply H; eauto.
Qed.

Lemma st_formula_varsagree : forall xs s,
  is_st_formula (VarsAgree xs s).
Proof.
  induction xs; simpl; auto.
Qed.

Lemma avarsagree_next : forall xs s1 s2 tr,
  eval_formula (AVarsAgree xs s2)
               (Stream.Cons _ s1 (Stream.Cons _ s2 tr)).
Proof.
  induction xs; intros; simpl in *; auto;
  unfold eval_comp; auto.
Qed.

(* Main helper lemma for diff_ind. Basically
   establishes the base case for diff_ind. The
   proof of this lemma is a complete mess. *)
Lemma eval_comp_ind : forall Hyps eqs
                             t1 t2 t1' t2' op,
  deriv_term t1 eqs = Some t1' ->
  deriv_term t2 eqs = Some t2' ->
  is_st_formula Hyps ->
  (|-- (Hyps //\\ Continuous eqs) -->> next Hyps) ->
  (|-- Hyps -->> (Comp t1' t2' (deriv_comp_op op))) ->
  (|-- (Comp t1 t2 op //\\ Hyps //\\
       Continuous eqs) -->>
                       Comp (next_term t1)
                       (next_term t2) op).
Proof.
  intros Hyps eqs t1 t2 t1' t2' op Ht1 Ht2 Hst Hhyps Hind.
  breakAbstraction; unfold eval_comp in *; simpl in *.
  intros tr XX H; clear XX; destruct H as [Hbase [HhypsI Hcont] ].

  destruct Hcont as [r [f Hcont] ];
    destruct Hcont as [Hr [Hsol [? ?] ] ].
  do 2 erewrite deriv_trace_now with (tr:=tr) in Hbase; eauto.
  pose proof (deriv_st_term _ _ _ Ht1).
  pose proof (deriv_st_term _ _ _ Ht2).
  repeat rewrite eval_next_term with (s3:=Stream.hd (Stream.tl tr)); auto.
  repeat erewrite deriv_trace_next with (tr:=tr) by eauto.
  unfold is_solution in *. destruct Hsol as [pf Hsol].
  simpl in *.
  pose proof (term_deriv f (t1 - t2) (t1' - t2')
                         r eqs pf (Stream.hd (Stream.tl tr)) Hsol)
    as Hterm1.
  pose proof (term_deriv f (t2 - t1) (t2' - t1')
                         r eqs pf (Stream.hd (Stream.tl tr)) Hsol)
    as Hterm2.
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
  try specialize (Hhyps (Stream.Cons _ (Stream.hd tr)
                              (Stream.Cons _ (f t) (Stream.tl tr))) I);
  simpl in *; try apply next_formula_tl in Hhyps; auto;
  try specialize (Hind (Stream.Cons _ (f t) (Stream.tl tr)) I); simpl in *;
  try specialize (Hind Hhyps); try solve_ineq;
  try (split;
        [ eapply st_formula_hd; eauto |
          exists t; exists f; repeat split; try solve_ineq;
          solve [apply is_solution_sub with (r2:=r);
                  try solve_ineq; unfold is_solution; eauto |
                 apply st_formula_hd with (tr1:=tr); auto;
                 apply st_formula_varsagree |
                 apply avarsagree_next]
      ]).
Qed.

(* Differential induction proof rule plus soundness
   proof. *)
Lemma diff_ind : forall Hyps G cp F,
  is_st_formula G ->
  is_st_formula Hyps ->
  (F |-- Continuous cp) ->
  ((Hyps //\\ Continuous cp) |-- next Hyps) ->
  (F |-- G) ->
  (F |-- Hyps) ->
  (Hyps |-- deriv_formula G cp) ->
  (F |-- next G).
Proof.
  Opaque Continuous.
  intros Hyps G; generalize dependent Hyps;
  induction G;
    intros Hyps cp F HstG HstH Hcont Hhyps Hbase HhypsF Hind;
  simpl in *; unfold tlaEntails in *; simpl in *; intros; eauto;
  try discriminate; try solve [exfalso; eapply Hind; eauto].
  - destruct HstG as [HstG1 HstG2].
    destruct (deriv_term t cp) eqn:?;
             destruct (deriv_term t0 cp) eqn:?;
    try solve [simpl in *; exfalso; eapply Hind; eauto].
    simpl in *. pose proof (Hcont tr H).
    destruct H0 as [r [f Hf] ]. simpl in *.
    decompose [and] Hf.
    pose proof (eval_comp_ind Hyps cp t t0
                              t1 t2 c Heqo Heqo0 HstH) as Hcomp.
    apply Hcomp; simpl in *; unfold tlaEntails; simpl in *; auto.
    repeat split; intuition.
    + apply HhypsF; auto.
    + apply Hcont; auto.
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
    + apply Hind; auto.
    + apply Hind; auto.
    + apply Hind; auto.
Qed.

Close Scope HP_scope.
