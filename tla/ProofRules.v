Require Import Coq.micromega.Psatz.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import Rdefinitions.
Require Import Ranalysis1.
Require Import MVT.

Open Scope HP_scope.

Fixpoint next_term (t:Term) :=
  match t with
    | VarNowT x => VarNextT x
    | PlusT t1 t2 => PlusT (next_term t1)
                           (next_term t2)
    | MinusT t1 t2 => MinusT (next_term t1)
                             (next_term t2)
    | MultT t1 t2 => MultT (next_term t1)
                           (next_term t2)
    | _ => t
  end.

Fixpoint next (F:Formula) :=
  match F with
    | TRUE => TRUE
    | FALSE => FALSE
    | Comp t1 t2 op => Comp (next_term t1) (next_term t2) op
    | And F1 F2 => And (next F1) (next F2)
    | Or F1 F2 => Or (next F1) (next F2)
    | Imp F1 F2 => Imp (next F1) (next F2)
    | Exists _ f => Exists _ (fun x => next (f x))
    | Forall _ f => Forall _ (fun x => next (f x))
    | PropF P => PropF P
    | Always F => Always (next F)
    | Eventually F => Eventually (next F)
  end.

Fixpoint is_st_term (t:Term) : bool :=
  match t with
    | VarNextT x => false
    | PlusT t1 t2 => andb (is_st_term t1)
                          (is_st_term t2)
    | MinusT t1 t2 => andb (is_st_term t1)
                           (is_st_term t2)
    | MultT t1 t2 => andb (is_st_term t1)
                          (is_st_term t2)
    | _ => true
  end.

Fixpoint is_st_formula (F:Formula) : Prop :=
  match F with
    | TRUE => True
    | FALSE => False
    | Comp t1 t2 _ =>
      and (is_st_term t1 = true) (is_st_term t2 = true)
    | And F1 F2 =>
      and (is_st_formula F1) (is_st_formula F2)
    | Or F1 F2 =>
      and (is_st_formula F1) (is_st_formula F2)
    | Imp F1 F2 =>
      and (is_st_formula F1) (is_st_formula F2)
    | Exists _ f =>
      forall x, is_st_formula (f x)
    | Forall _ f =>
      forall x, is_st_formula (f x)
    | PropF _ => True
    | _ => False
  end.

Fixpoint is_st_formula_b (F:Formula) : bool :=
  match F with
    | TRUE => true
    | FALSE => true
    | Comp t1 t2 _ => andb (is_st_term t1)
                           (is_st_term t2)
    | And F1 F2 => andb (is_st_formula_b F1)
                         (is_st_formula_b F2)
    | Or F1 F2 => andb (is_st_formula_b F1)
                        (is_st_formula_b F2)
    | Imp F1 F2 => andb (is_st_formula_b F1)
                        (is_st_formula_b F2)
    | _ => false
  end.

Lemma next_term_tl : forall t s1 s2 s3,
  is_st_term t = true ->
  eval_term (next_term t) s1 s2 =
  eval_term t s2 s3.
Proof.
  intros t s1 s2 s3 Hst.
  induction t; auto; simpl in *;
  try discriminate;
  try (apply andb_prop in Hst; intuition;
       rewrite H1; rewrite H2; auto).
Qed.

Lemma next_formula_tl : forall F tr,
  is_st_formula F ->
  (eval_formula (next F) tr <->
   eval_formula F (tl tr)).
Proof.
  intros F tr Hst; induction F; simpl in *;
  try tauto; try solve [firstorder].
  - unfold eval_comp in *. simpl in *.
    rewrite <- next_term_tl with (s1:=hd tr) (t:=t).
    rewrite <- next_term_tl with (s1:=hd tr) (t:=t0).
    intuition. intuition. intuition.
Qed.

Lemma st_term_hd : forall t s1 s2 s3,
  is_st_term t = true ->
  eval_term t s1 s2 =
  eval_term t s1 s3.
Proof.
  induction t; intros s1 s2 s3 Hst;
  simpl in *; auto; try discriminate;
  try (apply andb_prop in Hst; simpl;
       erewrite IHt1; intuition).
Qed.

Lemma st_formula_hd : forall F tr1 tr2,
  is_st_formula F ->
  eval_formula F tr1 ->
  hd tr1 = hd tr2 ->
  eval_formula F tr2.
Proof.
  induction F; intros; simpl in *; auto;
  try tauto; try discriminate;
  try solve [intuition; firstorder].
  - unfold eval_comp in *. simpl in *.
    rewrite st_term_hd with (t:=t) (s3:=hd (tl tr1)); intuition.
    rewrite st_term_hd with (t:=t0) (s3:=hd (tl tr1)); intuition.
    rewrite <- H1; auto.
Qed.

Lemma st_formula_varsagree : forall xs s,
  is_st_formula (VarsAgree xs s).
Proof.
  induction xs; simpl; auto.
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
  is_st_formula I ->
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

Lemma or_left : forall F1 F2 F3,
  (|- F1 --> F3) ->
  (|- F2 --> F3) ->
  (|- (F1 \/ F2) --> F3).
Proof. firstorder. Qed.

Lemma or_right1 : forall F1 F2 F3,
  (|- F1 --> F2) ->
  (|- F1 --> (F2 \/ F3)).
Proof. firstorder. Qed.

Lemma or_right2 : forall F1 F2 F3,
  (|- F1 --> F3) ->
  (|- F1 --> (F2 \/ F3)).
Proof. firstorder. Qed.

Lemma imp_right : forall F1 F2 F3,
  (|- (F1 /\ F2) --> F3) ->
  (|- F1 --> (F2 --> F3)).
Proof. firstorder. Qed.

Lemma imp_strengthen : forall F1 F2 F3,
  (|- F1 --> F2) ->
  (|- (F1 /\ F2) --> F3) ->
  (|- F1 --> F3).
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

(*Fixpoint lift_termnow (t:TermNow) : TermNext :=
  match t with
    | VarT x => VarT _ (VarNow x)
    | NatT n => NatT _ n
    | RealT r => RealT _ r
    | PlusT t1 t2 => PlusT _ (lift_termnow t1)
                           (lift_termnow t2)
    | MinusT t1 t2 => MinusT _ (lift_termnow t1)
                             (lift_termnow t2)
    | MultT t1 t2 => MultT _ (lift_termnow t1)
                           (lift_termnow t2)
  end.

Fixpoint lower_termnext (t:TermNext) :
  option TermNow :=
  match t with
    | VarT (VarNow x) => Some (VarT _ x)
    | VarT (VarNext x) => None
    | NatT n => Some (NatT _ n)
    | RealT r => Some (RealT _ r)
    | PlusT t1 t2 =>
      option_map2 (PlusT _) (lower_termnext t1)
                  (lower_termnext t2)
    | MinusT t1 t2 =>
      option_map2 (MinusT _) (lower_termnext t1)
                  (lower_termnext t2)
    | MultT t1 t2 =>
      option_map2 (MultT _) (lower_termnext t1)
                  (lower_termnext t2)
  end.
*)
(* Takes the derivative of a term and substitutes in
   the right hand side of differential equations. If
   a variable has no corresponding differential equation
   then 0 is substituted. This is because variables
   without specified derivatives have a derivative of 0. *)
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
      match deriv_term t1 eqs, deriv_term t2 eqs with
        | Some t1, Some t2 =>
          Comp t1 t2 (deriv_comp_op op)
        | _, _ => FALSE
      end
    | And F1 F2 => And (deriv_formula F1 eqs)
                       (deriv_formula F2 eqs)
    | _ => FALSE
  end.

(* Now we have a bunch of messy lemmas that we'll use
   to prove the differential induction (diff_ind) rule. *)
Lemma term_is_derivable : forall (f : R -> state) (e : Term) s,
  (forall x, derivable (fun t => f t x)) ->
  derivable (fun t => eval_term e (f t) s).
Proof.
  intros f e s.
  induction e; unfold eval_term;
  simpl; intro is_derivable.
    - auto.
    - apply derivable_const.
    - apply derivable_const.
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
  (r : R) (eqs : list DiffEq) is_derivable s,
  solves_diffeqs f eqs r is_derivable ->
  deriv_term e eqs = Some e' ->
  forall z, 
    (R0 <= z <= r)%R ->
    derive (fun t => eval_term e (f t) s)
           (term_is_derivable f e s is_derivable) z =
    eval_term e' (f z) s.
Proof.
  intros. unfold derive.
  apply (derive_pt_D_in
           (fun t : R => eval_term e (f t) s)
           (fun t : R => eval_term e' (f t) s)).
  generalize dependent e'.
  induction e; intros; simpl in *.
    - destruct (get_deriv v eqs) eqn:?.
      + unfold solves_diffeqs in *.
        unfold derive in *.
        specialize (H v t s (get_deriv_in _ _ _ Heqo) z H1).
        apply (derive_pt_D_in
                 (fun t0 : R => f t0 v)
                 (fun t0 : R => eval_term t (f t0) s)) in H.
        inversion H0; subst e'; auto.
      + discriminate.
    - inversion H0.
    - inversion H0; subst e'.
      unfold eval_term. simpl. apply Dconst.
    - inversion H0; subst e'.
      unfold eval_term. simpl. apply Dconst.
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
    | [ H : eq (Rminus (eval_term ?t1 _ _) (eval_term ?t2 _ _)) ?r3
        |- Rle ?r3 (Rminus (eval_term ?t1 _ _) (eval_term ?t2 _ _)) ]
        => rewrite <- H
    | [ H : eq (Rminus (eval_term ?t2 _ _) (eval_term ?t1 _ _)) ?r3
        |- Rle ?r3 (Rminus (eval_term ?t1 _ _) (eval_term ?t2 _ _)) ]
        => apply RIneq.Rminus_diag_uniq in H;
           symmetry in H; apply RIneq.Rminus_diag_eq in H;
           rewrite <- H
  end.

Ltac deriv_ineq :=
  match goal with
    | [ |- Rle (eval_term ?t1 (?f ?r1) ?s - eval_term ?t2 (?f _) ?s)
            (eval_term ?t1 (?f ?r2) ?s - eval_term ?t2 (?f _) ?s) ]
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

Lemma deriv_trace_now : forall f eqs t t' tr s,
  eval_formula (VarsAgree (List.map get_var eqs) (f R0)) tr ->
  deriv_term t eqs = Some t' ->
  eval_term t (hd tr) s = eval_term t (f R0) s.
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
Qed.

Lemma deriv_trace_next : forall f eqs (r:R) t t' tr s,
  eval_formula (AVarsAgree (List.map get_var eqs) (f r)) tr ->
  deriv_term t eqs = Some t' ->
  eval_term t (hd (tl tr)) s = eval_term t (f r) s.
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
Qed.

Lemma eval_next_term : forall t s1 s2 s3,
  is_st_term t = true ->
  eval_term (next_term t) s1 s2 =
  eval_term t s2 s3.
Proof.
  induction t; simpl; auto; intros;
  try discriminate;
  try (apply andb_prop in H; intuition;
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
Qed.

(*Lemma eval_lift_termnow : forall t tr,
  eval_termnext (lift_termnow t) tr =
  eval_termnow t (hd tr).
Proof.
  induction t; intro tr; auto;
  unfold eval_termnow, eval_termnext;
  simpl; rewrite IHt1; rewrite IHt2;
  auto.
Qed.

Lemma eval_next_lift_termnow : forall t tr,
  eval_termnext (next_term (lift_termnow t)) tr =
  eval_termnow t (hd (tl tr)).
Proof.
  induction t; intro tr; auto;
  unfold eval_termnow, eval_termnext;
  simpl; rewrite IHt1; rewrite IHt2;
  auto.
Qed.
*)
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
    (R0 <=
    derive_pt
      (fun z : R => eval_term t1 (f z) s - eval_term t2 (f z) s)
      t (derivable_pt_minus _ _ t
           (term_is_derivable _ _ s is_derivable t)
           (term_is_derivable _ _ s is_derivable t)))%R.
Proof.
  intros f t1 t2 t1' t2' r diffeqs is_derivable s Hsol
         Ht1 Ht2 Hineq t Ht.
  specialize (Hineq (f t)).
  erewrite <- term_deriv in Hineq; eauto.
  erewrite <- term_deriv in Hineq; eauto.
  unfold derive in Hineq.
  rewrite <- derive_pt_minus in Hineq.
  apply Hineq.
Qed.

Lemma eval_comp_ind : forall Hyps eqs
                             t1 t2 t1' t2' op,
  deriv_term t1 eqs = Some t1' ->
  deriv_term t2 eqs = Some t2' ->
  is_st_formula Hyps ->
  (|- (Hyps /\ Continuous eqs) --> next Hyps) ->
  (|- Hyps --> (Comp t1' t2' (deriv_comp_op op))) ->
  (|- (Comp t1 t2 op /\ Hyps /\
       Continuous eqs) -->
                       Comp (next_term t1)
                       (next_term t2) op).
Proof.
  intros Hyps eqs t1 t2 t1' t2' op Ht1 Ht2 Hst Hhyps Hind.
  simpl in *; unfold eval_comp in *; simpl in *.
  intros tr H; destruct H as [Hbase [HhypsI Hcont] ].

  destruct Hcont as [r [f Hcont] ];
    destruct Hcont as [Hr [Hsol [? ?] ] ].
  do 2 erewrite deriv_trace_now with (tr:=tr) in Hbase; eauto.
  pose proof (deriv_st_term _ _ _ Ht1).
  pose proof (deriv_st_term _ _ _ Ht2).
  repeat rewrite eval_next_term with (s3:=hd (tl tr)); auto.
  erewrite deriv_trace_next with (tr:=tr); eauto.
  erewrite deriv_trace_next with (tr:=tr); eauto.
  unfold is_solution in *. destruct Hsol as [pf Hsol].
  simpl in *. simpl in *.
  destruct op; simpl in *; try (apply RIneq.Rle_le_eq; split);
  normalize_ineq_goal; normalize_ineq_hyp Hbase;
  ineq_trans; auto;
  deriv_ineq; intros; try solve_ineq;
  try (pose proof (term_deriv f (t1 - t2) (t1' - t2')
                              r eqs pf (hd (tl tr)) Hsol)
        as Hterm;
       instantiate (1:=term_is_derivable f (t1 - t2) (hd (tl tr)) pf));
  try (pose proof (term_deriv f (t2 - t1) (t2' - t1')
                              r eqs pf (hd (tl tr)) Hsol)
        as Hterm;
       instantiate (1:=term_is_derivable f (t2 - t1) (hd (tl tr)) pf));
  simpl in *; try rewrite Ht1 in Hterm; try rewrite Ht2 in Hterm;
  try specialize (Hterm (eq_refl _));
  try unfold derive in Hterm;
  try rewrite Hterm; try solve_ineq;
  try specialize (Hhyps (Cons _ (hd tr)
                              (Cons _ (f t) (tl tr))));
  simpl in *; try apply next_formula_tl in Hhyps; auto;
  try specialize (Hind (Cons _ (f t) (tl tr))); simpl in *;
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

(*Lemma lower_st_term : forall t,
  is_st_term t = true ->
  exists t',
    eq (lower_termnext t) (Some t').
Proof.
  induction t; intro Hst; simpl in *.
  - destruct v; try discriminate.
    exists (VarT _ v); auto.
  - exists (NatT _ n); auto.
  - exists (RealT _ r); auto.
  - apply andb_prop in Hst; intuition.
    destruct H1; destruct H2.
    exists (x + x0); rewrite H1;
    rewrite H2; auto.
  - apply andb_prop in Hst; intuition.
    destruct H1; destruct H2.
    exists (x - x0); rewrite H1;
    rewrite H2; auto.
  - apply andb_prop in Hst; intuition.
    destruct H1; destruct H2.
    exists (x * x0); rewrite H1;
    rewrite H2; auto.
Qed.

Lemma lift_lower_term : forall t t',
  lower_termnext t = Some t' ->
  lift_termnow t' = t.
Proof.
  induction t; intros t Hlower;
  simpl in *;
  try solve [inversion Hlower; auto |
             destruct (lower_termnext t1);
               destruct (lower_termnext t2);
               try discriminate;
               simpl in *; inversion Hlower;
               simpl; erewrite <- IHt1; eauto;
               erewrite <- IHt2; eauto |
             destruct v; try discriminate;
             inversion Hlower; auto].
Qed.*)

Lemma diff_ind : forall Hyps G cp F,
  is_st_formula G ->
  is_st_formula Hyps ->
  (|- (Hyps /\ Continuous cp) --> next Hyps) ->
  (|- F --> Continuous cp) ->
  (|- F --> G) ->
  (|- F --> Hyps) ->
  (|- Hyps --> deriv_formula G cp) ->
  (|- F --> next G).
Proof.
  intros Hyps G; generalize dependent Hyps;
  induction G;
    intros Hyps cp F HstG HstH Hhyps Hcont Hbase HhypsF Hind;
  simpl in *; intros; eauto;
  try discriminate; try solve [exfalso; eapply Hind; eauto].
  destruct HstG as [HstG1 HstG2].
  destruct (deriv_term t cp) eqn:?;
           destruct (deriv_term t0 cp) eqn:?;
  try solve [simpl in *; exfalso; eapply Hind; eauto].
  simpl in *. pose proof (Hcont tr H).
  destruct H0 as [r [f Hf] ].
  decompose [and] Hf.
  pose proof (eval_comp_ind Hyps cp t t0
                            t1 t2 c Heqo Heqo0 HstH) as Hcomp.
  apply Hcomp; auto.
  repeat split; intuition.
  - apply HhypsF; auto.
  - apply Hcont; auto.
  - split.
    + eapply IHG1; eauto.
      * intuition.
      * apply Hbase; auto.
      * apply Hind; auto.
    + eapply IHG2; eauto.
      * intuition.
      * apply Hbase; auto.
      * apply Hind; auto.
Qed.

Lemma zero_deriv : forall G cp F x,
  List.In (DiffEqC x 0) cp ->
  (|- F --> Continuous cp) ->
  (|- (F /\ x! = x) --> G) ->
  (|- F --> G).
Proof.
induction cp.  intros F x Hin Hcont Hsuf.
- simpl in *. contradiction.
-  intros F x Hin Hcont Hsuf. simpl in Hin. destruct Hin.
+ simpl in *. intros. apply Hsuf.
split. auto. specialize (Hcont tr H0).
destruct Hcont as [r [f Hf] ].
decompose [and] Hf.
unfold eval_comp in *. simpl in *.
destruct a. simpl in *. inversion H.
subst x. subst t. unfold is_solution in *.
unfold solves_diffeqs in *.
destruct H3 as [H10]. specialize (H3 v 0).
simpl in *. rewrite H2. rewrite H4.
rewrite (null_derivative_loc (fun t => f t v) R0 r).
auto.
* intros.  unfold derivable in H10. apply derivable_continuous_pt.
apply H10.
* unfold derive in H2. firstorder. apply H3. auto. left; auto. psatzl R.
* intuition. 
+ apply IHcp with (x:=x).
apply H. 
simpl in *. intros. specialize (Hcont tr H0).
destruct Hcont as [r [f Hf]]. decompose [and] Hf.
exists r. exists f. intuition.
unfold is_solution in *.
destruct H9.
unfold solves_diffeqs in *.
simpl in *.
exists x0. intros. apply H9; auto.
apply Hsuf. Qed.

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

Fixpoint term_unchanged (t:Term) (eqs:list DiffEq) : bool :=
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
  end.

Fixpoint formula_unchanged (F:Formula) (eqs:list DiffEq) : bool :=
  match F with
    | Comp t1 t2 _ =>
      andb (term_unchanged t1 eqs) (term_unchanged t2 eqs)
    | And F1 F2 =>
      andb (formula_unchanged F1 eqs) (formula_unchanged F2 eqs)
    | Or F1 F2 =>
      andb (formula_unchanged F1 eqs) (formula_unchanged F2 eqs)
    | Imp F1 F2 =>
      andb (formula_unchanged F1 eqs) (formula_unchanged F2 eqs)
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
  eval_term (next_term t) (hd tr) (hd (tl tr)) =
  eval_term t (hd tr) (hd (tl tr)).
Proof.
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
Qed.

Lemma extract_vars_0 : forall F H eqs,
  formula_unchanged H eqs = true ->
  (|- F --> Continuous eqs) ->
  (|- (F /\ next H) --> H) /\ (|- (F /\ H) --> next H).
Proof.
  induction H; intros eqs Hunch Hcont;
  simpl in *; intros; intuition; try discriminate;
  try apply andb_prop in Hunch; try destruct Hunch as [Hunch1 Hunch2];
  try solve [ eapply IHFormula1; eauto |
              eapply IHFormula2; eauto |
              left; eapply IHFormula1; eauto |
              right; eapply IHFormula2; eauto ].
  - unfold eval_comp in *; simpl.
    rewrite <- extract_vars_term_0 with (eqs:=eqs) (t:=t); auto;
    try rewrite <- extract_vars_term_0 with (eqs:=eqs) (t:=t0); auto;
    apply Hcont; auto.
  - unfold eval_comp in *; simpl.
    rewrite extract_vars_term_0 with (eqs:=eqs) (t:=t); auto;
    try rewrite extract_vars_term_0 with (eqs:=eqs) (t:=t0); auto;
    apply Hcont; auto.
  - eapply IHFormula2; eauto; intuition.
    apply H4. eapply IHFormula1; eauto.
  - eapply IHFormula2; eauto; intuition.
    apply H4. eapply IHFormula1; eauto.
Qed.

Lemma diff_ind_imp : forall F H G eqs,
  is_st_formula G ->
  is_st_formula H ->
  formula_unchanged H eqs = true ->
  (|- (F /\ H) --> G) ->
  (|- F --> Continuous eqs) ->
  (|- H --> deriv_formula G eqs) ->
  (|- F --> (next H --> next G)).
Proof.
  intros F H G eqs HstG HstH Hin Hinit Hcont Hind.
  apply imp_right.
  assert (|- (F /\ next H) --> H) by
      (eapply extract_vars_0; eauto).
  apply diff_ind with (Hyps:=H) (cp:=eqs); auto.
  - apply and_comm_left. eapply extract_vars_0; eauto.
    apply imp_id.      
  - apply and_left1; auto.
  - apply imp_trans with (F2:=F/\H); auto.
    apply and_right; auto. apply and_left1.
    apply imp_id.
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
  (|- F --> Continuous eqs) ->
  (|- F --> (zero_deriv_term t eqs) = t).
Proof.
  intros t eqs.
  induction t; intros F Hcont;
  try solve [simpl; unfold eval_comp; simpl; intuition |
            simpl in *; unfold eval_comp in *; simpl;
            simpl; intros tr HF;
            erewrite IHt1; eauto; erewrite IHt2; eauto].
  - unfold zero_deriv_term.
    destruct (List.existsb (diffeq_eqb v 0) eqs) eqn:?.
    + apply List.existsb_exists in Heqb.
      destruct Heqb as [d [Hd1 Hd2] ].
      apply diffeq_eqb_ok in Hd2. subst d.
      apply zero_deriv with (x:=v) (cp:=eqs); auto.
      simpl; unfold eval_comp; simpl;
      intuition.
    + simpl; unfold eval_comp; simpl; intuition.
Qed.

Lemma zero_deriv_formula_ok : forall F G eqs,
  (|- F --> Continuous eqs) ->
  (|- F --> zero_deriv_formula G eqs) ->
  (|- F --> G).
Proof.
  simpl; intros F G eqs Hcont Hzero tr HF.
  specialize (Hzero tr HF).
  induction G; simpl in *; auto.
  - pose proof (zero_deriv_term_ok t eqs).
    pose proof (zero_deriv_term_ok t0 eqs).
    specialize (H F Hcont). specialize (H0 F Hcont).
    simpl in *. unfold eval_comp in *. simpl in *.
    rewrite <- H; auto. rewrite <- H0; auto.
  - split; try apply IHG1;
    try apply IHG2; intuition.
  - destruct Hzero.
    + left; apply IHG1; auto.
    + right; apply IHG2; auto.
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
  |- Continuous eqs --> Unchanged (get_unchanged eqs).
Proof.
  intro eqs. pose proof (get_unchanged_ok eqs) as Hunch.
  revert Hunch.  generalize (get_unchanged eqs).
  intros l Hin. induction l.
  - simpl; intros; auto.
  - apply zero_deriv with (x:=a) (cp:=eqs).
    + apply Hin; intuition.
    + apply imp_id.
    + simpl (Unchanged (a :: l)).
      apply and_right.
      * apply and_left2. apply imp_id.
      * simpl; intros. apply IHl; auto.
        intros; apply Hin; intuition.
        apply H.
Qed.

Lemma unchanged_continuous : forall eqs F G,
  (|- F --> Continuous eqs) ->
  (|- (F /\ Unchanged (get_unchanged eqs)) --> G) ->
  (|- F --> G).
Proof.
  intros eqs F G Hcont Hunch.
  simpl; intros; apply Hunch.
  split; auto.
  apply unchanged_continuous_aux.
  apply Hcont; auto.
Qed.      

Close Scope HP_scope.