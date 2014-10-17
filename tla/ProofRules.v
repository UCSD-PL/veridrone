Require Import Coq.micromega.Psatz.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import Rdefinitions.
Require Import Ranalysis1.
Require Import MVT.

Open Scope HP_scope.

Fixpoint next_term (t:ActionTerm) :=
  match t with
    | TermNow t => TermNext t
    | _ => t
  end.

Fixpoint next (F:Formula) :=
  match F with
    | Comp t1 t2 op => Comp (next_term t1) (next_term t2) op
    | And F1 F2 => And (next F1) (next F2)
    | Or F1 F2 => Or (next F1) (next F2)
    | Imp F1 F2 => Imp (next F1) (next F2)
    | Exists _ f => Exists _ (fun x => next (f x))
    | Always F => Always (next F)
    | Eventually F => Eventually (next F)
    | _ => F
  end.

Fixpoint is_st_term (t:ActionTerm) : bool :=
  match t with
    | TermNow _ => true
    | _ => false
  end.

Fixpoint is_st_formula (F:Formula) : bool :=
  match F with
    | TRUE => true
    | FALSE => true
    | Comp t1 t2 _ => andb (is_st_term t1)
                           (is_st_term t2)
    | And F1 F2 => andb (is_st_formula F1)
                         (is_st_formula F2)
    | Or F1 F2 => andb (is_st_formula F1)
                        (is_st_formula F2)
    | Imp F1 F2 => andb (is_st_formula F1)
                        (is_st_formula F2)
    | _ => false
  end.

Lemma next_term_tl : forall t tr,
  is_st_term t = true ->
  eval_aterm (next_term t) tr =
  eval_aterm t (tl tr).
Proof.
  intros t tr Hst.
  induction t; auto;
  simpl in *; discriminate.
Qed.

Lemma next_formula_tl : forall F tr,
  is_st_formula F = true ->
  (eval_formula (next F) tr <->
   eval_formula F (tl tr)).
Proof.
  intros F tr Hst; induction F; simpl in *;
  try tauto; try discriminate.
  - unfold eval_comp in *. simpl in *.
    apply andb_prop in Hst.
    repeat rewrite <- next_term_tl;
      intuition.
   - apply andb_prop in Hst; intuition.
   - apply andb_prop in Hst; intuition.
   - apply andb_prop in Hst; intuition.
Qed.

Lemma st_formula_hd : forall F tr1 tr2,
  is_st_formula F = true ->
  eval_formula F tr1 ->
  hd tr1 = hd tr2 ->
  eval_formula F tr2.
Proof.
  induction F; intros; simpl in *; auto;
  try tauto; try discriminate.
  - unfold eval_comp in *. simpl in *.
    apply andb_prop in H.
    destruct a; destruct a0; simpl in *;
    intuition; try discriminate.
    rewrite H1 in *; auto.
   - apply andb_prop in H; intuition; firstorder.
   - apply andb_prop in H; intuition; firstorder.
   - apply andb_prop in H; intuition; firstorder.
Qed.

Lemma st_formula_varsagree : forall xs s,
  is_st_formula (VarsAgree xs s) = true.
Proof.
  induction xs; auto.
Qed.

Lemma avarsagree_next : forall xs s1 s2 tr,
  eval_formula (AVarsAgree xs s2)
               (Cons _ s1 (Cons _ s2 tr)).
Proof.
  induction xs; intros; simpl in *; auto;
  unfold eval_comp; auto.
Qed.

Lemma nth_suf_tl : forall A n (s:stream A),
  nth_suf n (tl s) =
  tl (nth_suf n s).
Proof.
  intros A n; induction n; intro s;
  firstorder.
Qed.

Lemma inv_discr_ind : forall I N,
  is_st_formula I = true ->
  (|- (I /\ N) --> (next I)) ->
  (|- (I /\ []N) --> []I).
Proof.
  intros I N Hst Hind. simpl in *.
  intros tr [HI HAN] n.
  induction n; auto.
  simpl. rewrite nth_suf_tl.
  apply next_formula_tl; intuition.
Qed.

Lemma imp_trans : forall F1 F2 F3,
  (|- F1 --> F2) ->
  (|- F2 --> F3) ->
  (|- F1 --> F3).
Proof. firstorder. Qed.

Lemma always_imp : forall F1 F2,
  (|- F1 --> F2) ->
  (|- []F1 --> []F2).
Proof. firstorder. Qed.

Lemma and_right : forall F1 F2 F3,
  (|- F1 --> F2) ->
  (|- F1 --> F3) ->
  (|- F1 --> (F2 /\ F3)).
Proof. firstorder. Qed.

Lemma and_left1 : forall F1 F2 F3,
  (|- F1 --> F3) ->
  (|- (F1 /\ F2) --> F3).
Proof. firstorder. Qed.

Lemma and_left2 : forall F1 F2 F3,
  (|- F2 --> F3) ->
  (|- (F1 /\ F2) --> F3).
Proof. firstorder. Qed.

Lemma imp_id : forall F,
  |- F --> F.
Proof. firstorder. Qed.

Lemma or_next : forall F1 F2 N1 N2,
  (|- (F1 /\ N1) --> F2) ->
  (|- (F1 /\ N2) --> F2) ->
  (|- (F1 /\ (N1 \/ N2)) --> F2).
Proof. firstorder. Qed.

Lemma imp_right : forall F1 F2 F3,
  (|- (F1 /\ F2) --> F3) ->
  (|- F1 --> (F2 --> F3)).
Proof. firstorder. Qed.

Lemma and_assoc_left : forall F1 F2 F3 F4,
  (|- (F1 /\ (F2 /\ F3)) --> F4) ->
  (|- ((F1 /\ F2) /\ F3) --> F4).
Proof. firstorder. Qed.

Lemma and_comm_left : forall F1 F2 F3,
  (|- (F2 /\ F1) --> F3) ->
  (|- (F1 /\ F2) --> F3).
Proof. firstorder. Qed.

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
Definition get_deriv (x:Var) (eqs:list DiffEq)
  : option Term :=
  option_map get_term
    (List.find (fun p : DiffEq => let (y, t) := p in
          proj1_sig (Sumbool.bool_of_sumbool
                       (String.string_dec x y))) eqs).

Definition option_map2 {A B C} (f:A->B->C) 
  (a:option A) (b:option B) : option C :=
  match a, b with
    | Some a, Some b => Some (f a b)
    | _, _ => None
  end.

(* Takes the derivative of a term and substitutes in
   the right hand side of differential equations. If
   a variable has no corresponding differential equation
   then 0 is substituted. This is because variables
   without specified derivatives have a derivative of 0. *)
Fixpoint deriv_term (t:Term) (eqs:list DiffEq)
  : option Term :=
  match t with
  | VarT x => get_deriv x eqs
  | RealT r => Some (RealT R0)
  | PlusT t1 t2 =>
     option_map2 PlusT (deriv_term t1 eqs) (deriv_term t2 eqs)
  | MinusT t1 t2 =>
     option_map2 MinusT (deriv_term t1 eqs) (deriv_term t2 eqs)
  | MultT t1 t2 =>
     option_map2 PlusT
                 (option_map (fun t => MultT t t2) (deriv_term t1 eqs))
                 (option_map (MultT t1) (deriv_term t2 eqs))
  end.

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

Fixpoint deriv_formula (F:Formula) (eqs:list DiffEq) :=
  match F with
    | TRUE => TRUE
    | FALSE => FALSE
    | Comp t1 t2 op =>
      match t1, t2 with
        | TermNext t1, TermNext t2 =>
          match deriv_term t1 eqs, deriv_term t2 eqs with
            | Some t1, Some t2 =>
              Comp t1 t2 (deriv_comp_op op)
            | _, _ => FALSE
          end
        | _, _ => FALSE
      end
    | _ => FALSE
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
Qed.

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

Lemma term_deriv : forall (f : R -> state) (e e' : Term)
  (r : R) (eqs : list DiffEq) is_derivable,
  solves_diffeqs f eqs r is_derivable ->
  deriv_term e eqs = Some e' ->
  forall z, 
    (R0 <= z <= r)%R ->
    derive (fun t => eval_term e (f t))
           (term_is_derivable f e is_derivable) z =
    eval_term e' (f z).
Proof.
  intros. unfold derive.
  apply (derive_pt_D_in
           (fun t : R => eval_term e (f t))
           (fun t : R => eval_term e' (f t))).
  generalize dependent e'.
  induction e; intros; simpl in *.
    - destruct (get_deriv v eqs) eqn:?.
      + unfold solves_diffeqs in *.
        unfold derive in *.
        specialize (H v t (get_deriv_in _ _ _ Heqo) z H1).
        apply (derive_pt_D_in
                 (fun t0 : R => f t0 v)
                 (fun t0 : R => eval_term t (f t0))) in H.
        inversion H0; subst e'; auto.
      + discriminate.
    - inversion H0; subst e'. apply Dconst.
    - destruct (deriv_term e1 eqs); destruct (deriv_term e2 eqs);
      simpl in *; try discriminate. inversion H0; subst e'.
      apply Dadd; auto.
    - destruct (deriv_term e1 eqs); destruct (deriv_term e2 eqs);
      simpl in *; try discriminate. inversion H0; subst e'.
      apply Dminus; auto.
    - destruct (deriv_term e1 eqs); destruct (deriv_term e2 eqs);
      simpl in *; try discriminate. inversion H0; subst e'.
      apply Dmult; auto.
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
    | [ H : eq (Rminus (eval_term ?t1 _) (eval_term ?t2 _)) ?r3
        |- Rle ?r3 (Rminus (eval_term ?t1 _) (eval_term ?t2 _)) ]
        => rewrite <- H
    | [ H : eq (Rminus (eval_term ?t2 _) (eval_term ?t1 _)) ?r3
        |- Rle ?r3 (Rminus (eval_term ?t1 _) (eval_term ?t2 _)) ]
        => apply RIneq.Rminus_diag_uniq in H;
           symmetry in H; apply RIneq.Rminus_diag_eq in H;
           rewrite <- H
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

Ltac solve_ineq := psatzl R.

Lemma deriv_trace_now : forall f eqs t t' tr,
  eval_formula (VarsAgree (List.map get_var eqs) (f R0)) tr ->
  deriv_term t eqs = Some t' ->
  eval_term t (hd tr) = eval_term t (f R0).
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
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
Qed.

Lemma deriv_trace_next : forall f eqs (r:R) t t' tr,
  eval_formula (AVarsAgree (List.map get_var eqs) (f r)) tr ->
  deriv_term t eqs = Some t' ->
  eval_term t (hd (tl tr)) = eval_term t (f r).
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
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
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
  intros x d Hin z Hz.
  apply Hsol; auto.
  psatzl R.
Qed.

Lemma deriv_neg : forall f t1 t2 t1' t2' r eqs is_derivable,
  solves_diffeqs f eqs r is_derivable ->
  deriv_term t1 eqs = Some t1' ->
  deriv_term t2 eqs = Some t2' ->
  (forall st,
     (R0 <= eval_term t1' st -
      eval_term t2' st)%R) ->
  forall t,
    (R0 <= t <= r)%R ->
    (R0 <=
    derive_pt
      (fun z : R => eval_term t1 (f z) - eval_term t2 (f z))
      t (derivable_pt_minus _ _ t
           (term_is_derivable _ _ is_derivable t)
           (term_is_derivable _ _ is_derivable t)))%R.
Proof.
  intros f t1 t2 t1' t2' r diffeqs is_derivable Hsol Ht1 Ht2 Hineq
         t Ht.
  specialize (Hineq (f t)).
  erewrite <- term_deriv in Hineq; eauto.
  erewrite <- term_deriv in Hineq; eauto.
  unfold derive in Hineq.
  rewrite <- derive_pt_minus in Hineq.
  apply Hineq.
Qed.

Lemma eval_comp_ind : forall Hyps eqs b tvar
                             t1 t2 t1' t2' op,
  deriv_term t1 eqs = Some t1' ->
  deriv_term t2 eqs = Some t2' ->
  is_st_formula Hyps = true ->
  (|- (Hyps /\ Continuous eqs b tvar) --> next Hyps) ->
  (|- Hyps --> (Comp t1' t2' (deriv_comp_op op))) ->
  (|- (Comp (TermNow t1) (TermNow t2) op /\ Hyps /\
       Continuous eqs b tvar) -->
                              Comp (TermNext t1) (TermNext t2) op).
Proof.
  intros Hyps eqs b tvar t1 t2 t1' t2' op Ht1 Ht2 Hst Hhyps Hind.
  simpl in *; unfold eval_comp in *; simpl in *.
  intros tr H; destruct H as [Hbase [HhypsI Hcont] ].

  destruct Hcont as [r [f Hcont] ];
    destruct Hcont as [Hr [Hsol [? [? ?] ] ] ].
  do 2 erewrite deriv_trace_now with (tr:=tr) in Hbase; eauto.
  erewrite deriv_trace_next with (tr:=tr); eauto.
  erewrite deriv_trace_next with (tr:=tr); eauto.
  unfold is_solution in *. destruct Hsol as [pf Hsol].
  simpl in *. simpl in *.
  destruct op; simpl in *; try (apply RIneq.Rle_le_eq; split);
  normalize_ineq_goal; normalize_ineq_hyp Hbase;
  ineq_trans; auto;
  deriv_ineq; intros; try solve_ineq;
  try (pose proof (term_deriv f (t1 - t2) (t1' - t2')
                              r eqs pf Hsol)
        as Hterm;
       instantiate (1:=term_is_derivable f (t1 - t2) pf));
  try (pose proof (term_deriv f (t2 - t1) (t2' - t1')
                              r eqs pf Hsol)
        as Hterm;
       instantiate (1:=term_is_derivable f (t2 - t1) pf));
  simpl in *; try rewrite Ht1 in Hterm; try rewrite Ht2 in Hterm;
  try specialize (Hterm (eq_refl _));
  try unfold derive in Hterm;
  try rewrite Hterm; try solve_ineq;
  try specialize (Hhyps (Cons _ (hd tr)
                              (Cons _ (f t) (tl (tl tr)))));
  simpl in *; try apply next_formula_tl in Hhyps; auto;
  try specialize (Hind (Cons _ (f t) tr)); simpl in *;
  try apply st_formula_hd
    with (tr2:=Cons _ (f t) tr) (F:=Hyps)
    in Hhyps; auto;
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

Lemma diff_ind : forall Hyps G cp b t F,
  is_st_formula G = true ->
  is_st_formula Hyps = true ->
  (|- (Hyps /\ Continuous cp b t) --> next Hyps) ->
  (|- F --> Continuous cp b t) ->
  (|- F --> G) ->
  (|- F --> Hyps) ->
  (|- Hyps --> deriv_formula (next G) cp) ->
  (|- F --> next G).
Proof.
  intros Hyps G; generalize dependent Hyps;
  induction G;
    intros Hyps cp b t F HstG HstH Hhyps Hcont Hbase HhypsF Hind;
  simpl in *; intros; eauto;
  try discriminate; try solve [exfalso; eapply Hind; eauto].
  destruct a; destruct a0; simpl in *;
  try discriminate.
  destruct (deriv_term t0 cp) eqn:?;
           destruct (deriv_term t1 cp) eqn:?;
  try solve [simpl in *; exfalso; eapply Hind; eauto].
  simpl in *. pose proof (Hcont tr H).
  destruct H0 as [r [f Hf] ].
  decompose [and] Hf.
  eapply eval_comp_ind with (t1:=t0) (t2:=t1) (op:=c)
  (Hyps:=Hyps) (eqs:=cp) (b:=b) (tvar:=t); eauto.
  repeat split; intuition.
  - apply HhypsF; auto.
  - apply Hcont; auto.
Qed.

Lemma zero_deriv : forall G cp b t F x,
  List.In (DiffEqC x 0) cp ->
  (|- F --> Continuous cp b t) ->
  (|- (F /\ x! = x) --> G) ->
  (|- F --> G).
Proof.
  induction cp; intros b t F x Hin Hcont Hsuf.
  - simpl in *; contradiction.
  - simpl in Hin. destruct Hin.
    + simpl in *; intros; apply Hsuf.
      split; auto. specialize (Hcont tr H0).
      destruct Hcont as [r [f Hf] ].
      decompose [and] Hf.
      unfold eval_comp in *. simpl in *.
      destruct a. simpl in *. inversion H.
      subst x. subst t0. unfold is_solution in *.
      unfold solves_diffeqs in *.
      destruct H3. specialize (H2 v 0).
      simpl in *. rewrite H5. rewrite H4.
      rewrite (null_derivative_loc (fun t => f t v) R0 r);
        auto.
      * intros.
Require Import String.
Open Scope string_scope.
Goal forall tr r, eval_aterm (next_term "pc") tr = r.
intros. simpl (next_term "pc").

Lemma time_diff : forall G cp b t F,
  (|- F --> Continuous cp b t) ->
  (|- (F /\ t! <= b!) --> G) ->
  (|- F --> G).
Admitted.

(*Lemma diff_ind : forall F1 F2 cp uc b t,
  let eqs := cons (DiffEqC t 1)
                  (List.app 
                     cp 
                     (List.map
                        (fun x => DiffEqC x (RealT R0)) uc)) in
  (|- (F1 /\ Unchanged uc )
        --> deriv_formula F2 eqs) ->
  (|- ((Continuous cp b t /\ Unchanged uc) /\ F1) --> F2).
Admitted.*)

Close Scope HP_scope.