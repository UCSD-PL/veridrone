Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Syntax.
Require Import Semantics.
Require Import List.
Require Import Sumbool.
Require Import Coq.Reals.MVT.
Require Import String.
Require Import FunctionalExtensionality.
Require Import Equality.
Require Import Coq.Bool.Bool.

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

(* Substitutes t2 for x in t1 *)
Fixpoint subst_var_term (t1 t2:Term) (x:Var) : Term :=
  match t1 with
  | VarT y => if string_dec x y then t2 else t1
  | RealT r => t1
  | PlusT t3 t4 =>
     (subst_var_term t3 t2 x) + (subst_var_term t4 t2 x)
  | MinusT t3 t4 =>
     (subst_var_term t3 t2 x) - (subst_var_term t4 t2 x)
  | MultT t3 t4 =>
     (subst_var_term t3 t2 x) * (subst_var_term t4 t2 x)
  end.

(* Substitutes t for x in c *)
Fixpoint subst_var_cond (c:Cond) (x:Var) (t:Term) : Cond :=
  match c with
    | CompC t1 t2 op => CompC (subst_var_term t1 t x)
                              (subst_var_term t2 t x) op
    | AndC c1 c2 => AndC (subst_var_cond c1 x t)
                         (subst_var_cond c2 x t)
    | OrC c1 c2 => OrC (subst_var_cond c1 x t)
                       (subst_var_cond c2 x t)
  end.

Fixpoint get_vars (t:Term) : list Var :=
  match t with
    | VarT x => x::nil
    | RealT _ => nil
    | PlusT t1 t2 => get_vars t1 ++ get_vars t2
    | MinusT t1 t2 => get_vars t1 ++ get_vars t2
    | MultT t1 t2 => get_vars t1 ++ get_vars t2
  end.

Fixpoint admissible_subst_prog (p:HybridProg) (x:Var) (t:Term)
  : bool :=
  match p with
    | Skip => true
    | Assign y t' => 
      proj1_sig (bool_of_sumbool
                   (in_dec string_dec y (x::get_vars t)))
    | DiffEq eqs b =>
      existsb (fun p =>
                 proj1_sig
                   (bool_of_sumbool
                      (in_dec string_dec (fst p)
                              (x::get_vars t))))
              eqs
    | Seq p1 p2 =>
      andb (admissible_subst_prog p1 x t)
           (admissible_subst_prog p2 x t)
    | Branch c p1 p2 =>
      andb (admissible_subst_prog p1 x t)
           (admissible_subst_prog p2 x t)
    | While c p =>
      admissible_subst_prog p x t
  end.

Fixpoint admissible_subst (f:Formula) (x:Var) (t:Term)
  : bool :=
  match f with
    | CompF t1 t2 op => true
    | AndF f1 f2 => andb (admissible_subst f1 x t)
                         (admissible_subst f2 x t)
    | OrF f1 f2 => andb (admissible_subst f1 x t)
                        (admissible_subst f2 x t)
    | Imp f1 f2 => andb (admissible_subst f1 x t)
                        (admissible_subst f2 x t)
    | ForallState p f' => andb (admissible_subst_prog p x t)
                               (admissible_subst f' x t)
  end.

(* Substitutes t for x in p *)
Fixpoint subst_var_prog (p:HybridProg) (x:Var) (t:Term) :
  HybridProg :=
  match p with
    | Skip => Skip
    | Assign y t' => Assign y (subst_var_term t' t x)
    | DiffEq eqs b =>
      DiffEq
        (map (fun p => (fst p, subst_var_term (snd p) t x))
             eqs) b
    | Seq p1 p2 =>
      Seq (subst_var_prog p1 x t) (subst_var_prog p2 x t)
    | Branch c p1 p2 =>
      Branch (subst_var_cond c x t)
             (subst_var_prog p1 x t)
             (subst_var_prog p2 x t)
    | While c p =>
      While (subst_var_cond c x t) (subst_var_prog p x t)
  end.

(* Substitutes t for x in f *)
Fixpoint subst_var (f:Formula) (x:Var) (t:Term) : Formula :=
  match f with
    | CompF t1 t2 op =>
      CompF (subst_var_term t1 t x) (subst_var_term t2 t x) op
    | AndF f1 f2 => AndF (subst_var f1 x t) (subst_var f2 x t)
    | OrF f1 f2 => OrF (subst_var f1 x t) (subst_var f2 x t)
    | Imp f1 f2 => Imp (subst_var f1 x t) (subst_var f2 x t)
    | ForallState p f' =>
      ForallState (subst_var_prog p x t) (subst_var f' x t)
  end.

(* Assignment rule *)
Lemma assign_intro' : forall x t f st,
  admissible_subst f x t = true ->
  (eval_formula (subst_var f x t) st <->
   eval_formula f
                (fun y => if string_dec x y
                          then eval_term t st else st y)).
Proof.
  intros x t f.
  induction f; simpl in *; intros.
  - admit.
  - apply andb_true_iff in H. firstorder.
  - apply andb_true_iff in H. firstorder.
  - apply andb_true_iff in H. firstorder.
  - admit.
Qed.

Lemma assign_intro'' : forall x t f st,
  eval_formula f
    (fun y => if string_dec x y
              then eval_term t st else st y) ->
  eval_formula ([x ::= t]f) st.
Proof.
  intros x t f st H.
  simpl. intros st' Htrans.
  inversion Htrans.
 assert (st' = (fun y : Var =>
    if string_dec x y then eval_term t st else st y)).
    apply functional_extensionality.
    intro x1. destruct (string_dec x x1).
    subst x1; auto.
    symmetry. eapply H5.
    congruence.
  rewrite H6. auto.
Qed.

(* Assignment rule *)
Lemma assign_intro : forall x t f st
  (OK : admissible_subst f x t = true),
  eval_formula (subst_var f x t) st ->
   eval_formula ([x ::= t]f) st.
Proof.
  intros. apply assign_intro''. apply assign_intro'; auto.
Qed.

(*Sequencing introduction. *)
Lemma seq_intro : forall p1 p2 f st,
  eval_formula ([p1]([p2]f)) st ->
  eval_formula ([p1; p2]f) st.
Proof.
  intros p1 p2 f st H.
  simpl in *. intros st' Htrans.
  inversion Htrans.
  firstorder.
Qed.

(* Branching rule *)
Lemma ite_intro : forall c p1 p2 f st,
  (eval_cond c st ->
   eval_formula ([p1]f) st) ->
  (~eval_cond c st ->
    eval_formula ([p2]f) st) ->
  eval_formula ([Branch c p1 p2] f) st.
Proof.
  intros c p1 p2 f st HT HF.
  simpl. intros st' Htrans.
  inversion Htrans. subst. apply HT; auto.
  apply HF; auto.
Qed.

(* induction over while loops *)
(* This rule is weaker than it could be because
   it's annoying to put the false condition in the
   post condition. *)
Lemma while_ind : forall c p f st,
  eval_formula f st ->
  (forall st, eval_cond c st ->
              eval_formula (f --> [p] f) st) ->
  eval_formula ([While c p] f) st.
Proof.
  intros c p f st Hbase Hind.
  simpl in *. intros st' Htrans.
  dependent induction Htrans; firstorder.
Qed.

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
Definition FalseFormula : Formula := #0 > #1.

Lemma FalseFormulaFalse : forall st,
  ~eval_formula FalseFormula st.
Proof.
  intros. simpl. apply RIneq.Rle_not_gt.
  apply RIneq.Rle_0_1.
Qed.

(* When you take the synthetic derivative of a formula
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

(* The derivative of a formula is essentially the derivative
   of each of its terms (with some exceptions). *)
Fixpoint deriv_formula (f:Formula) (eqs:list (Var * Term))
  : Formula :=
  match f with
  | CompF t1 t2 op =>
     CompF (deriv_term t1 eqs) (deriv_term t2 eqs)
           (deriv_comp_op op)
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

Lemma deriv_neg : forall f t1 t2 r diffeqs is_derivable,
  solves_diffeqs f diffeqs r is_derivable ->
  vars_unchanged f diffeqs r is_derivable ->
  (forall st,
     (R0 <= eval_term (deriv_term t1 diffeqs) st -
      eval_term (deriv_term t2 diffeqs) st)%R) ->
  forall t,
    (R0 <= t <= r)%R ->
    (R0 <=
    derive_pt
      (fun z : R => eval_term t1 (f z) - eval_term t2 (f z))
      t (derivable_pt_minus _ _ t
           (term_is_derivable _ _ is_derivable t)
           (term_is_derivable _ _ is_derivable t)))%R.
Proof.
  intros f t1 t2 r diffeqs is_derivable Hdiff1 Hdiff2 Hineq
         t Ht.
  specialize (Hineq (f t)).
  erewrite <- term_deriv in Hineq; eauto.
  erewrite <- term_deriv in Hineq; eauto.
  unfold derive in Hineq.
  rewrite <- derive_pt_minus in Hineq.
  apply Hineq.
Qed.

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
    | [ _ : eq ?r1 ?r3 |- eq _ ?r3 ]
        => transitivity r1
  end.

Ltac deriv_ineq :=
  match goal with
    | [ |- Rle (eval_term ?t1 (?f ?r1) - eval_term ?t2 (?f _))
            (eval_term ?t1 (?f ?r2) - eval_term ?t2 (?f _)) ]
        => eapply (derive_increasing_interv_var r1 r2
                     (fun z => eval_term t1 (f z) -
                               eval_term t2 (f z))%R); eauto
    | [ |- @eq R
               (Rminus (eval_term ?t1 (?f _))
                       (eval_term ?t2 (?f _)))
               (Rminus (eval_term ?t1 (?f _))
                       (eval_term ?t2 (?f _)))]
        => eapply (null_derivative_loc
                 (fun z => (eval_term t1 (f z) -
                            eval_term t2 (f z))%R)); eauto
  end.

Ltac solve_ineq :=
  repeat match goal with
           | [ H : (_ < _ < _)%R |- _ ] => destruct H
           | [ |- (_ <= _ <= _)%R ] => split
           | [ |- _ ] => solve [eapply RIneq.Rlt_le; eauto]
           | [ |- _ ] => solve [apply RIneq.Rle_refl]
         end.

Lemma eval_comp_ind : forall f r diffeqs is_derivable
                             t1 t2 op,
  Rlt R0 r ->
  solves_diffeqs f diffeqs r is_derivable ->
  vars_unchanged f diffeqs r is_derivable ->
  eval_comp t1 t2 (f R0) op ->
  (forall st, eval_comp (deriv_term t1 diffeqs)
                        (deriv_term t2 diffeqs)
                        st
                        (deriv_comp_op op)) ->
  eval_comp t1 t2 (f r) op.
Proof.
  intros f r diffeqs is_derivable t1 t2 op Hr Hdiff1 Hdiff2
         Hbase Hind.
  destruct op; unfold eval_comp in *; simpl in *;
  try solve [normalize_ineq_goal; normalize_ineq_hyp Hbase;
       ineq_trans; auto; deriv_ineq; intros;
       match goal with
         | [ |- context [ derive_pt _ _ _ ] ]
           => eapply deriv_neg; eauto; intros;
         normalize_ineq_hyp Hind; try eapply Hind
         | [ |- _ ]
           => idtac
       end; solve_ineq].

normalize_ineq_goal; normalize_ineq_hyp Hbase;
ineq_trans; auto; deriv_ineq; intros.
apply continuity_pt_minus; apply derivable_continuous_pt;
apply term_is_derivable; auto.
eapply RIneq.Rminus_diag_eq in Hind.
erewrite <- term_deriv in Hind; eauto.
erewrite <- term_deriv in Hind; eauto.
unfold derive in *.
rewrite <- derive_pt_minus in Hind.
apply Hind.
solve_ineq.
solve_ineq.
solve_ineq.
Grab Existential Variables.
exact (f r).
exact (f r).
exact (f r).
exact (f r).
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
    - subst st. subst st'. eapply eval_comp_ind; eauto.
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
                    | [ |- _ ] => apply seq_intro
                    | [ |- _ ] => apply assign_intro;
                           [exact (Logic.eq_refl _) | ]
                    | [ |- _ ] => apply ite_intro
                    | [ |- _ ] => apply while_ind
                  end).

Close Scope HP_scope.