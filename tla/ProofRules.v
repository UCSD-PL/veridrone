Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import Rdefinitions.
Require Import Ranalysis1.

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

Definition formulas_equiv (F1 F2:Formula) :=
  (|- F1) <-> (|- F2).

Lemma formulas_equiv_trans : forall F1 F2 F3,
  formulas_equiv F1 F2 ->
  formulas_equiv F2 F3 ->
  formulas_equiv F1 F3.
Proof. firstorder. Qed.

Lemma formulas_equiv_refl : forall F,
  formulas_equiv F F.
Proof. firstorder. Qed.

Lemma formulas_equiv_sym : forall F1 F2,
  formulas_equiv F1 F2 ->
  formulas_equiv F2 F1.
Proof. firstorder. Qed.

Add Parametric Relation : Formula formulas_equiv
  reflexivity proved by formulas_equiv_refl
  symmetry proved by formulas_equiv_sym
  transitivity proved by formulas_equiv_trans
    as formulas.

(*
Add Parametric Morphism : And with
    signature Formula ==> Formula ==> Formula as and_mor.
*)

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
                 (option_map (MultT t2) (deriv_term t1 eqs))
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
(*
  intros. unfold derive.
  apply (derive_pt_D_in
           (fun t : R => eval_term e (f t))
           (fun t : R => eval_term (deriv_term e eqs)
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
Qed.*)
Admitted.

Lemma diff_ind : forall F1 F2 F3 F4 cp uc b t,
  let eqs := cons (DiffEqC t 1)
                  (List.app 
                     cp 
                     (List.map
                        (fun x => DiffEqC x (RealT R0)) uc)) in
  (|- (F1 /\ F2 /\ Unchanged uc /\ F3)
        --> deriv_formula F4 eqs) ->
  (|- ((F1 /\ F2 /\ (Continuous cp b t /\ Unchanged uc)) /\ F3) --> F4).
Admitted.

Lemma diff_ind2 : forall F1 F2 F4 cp uc b t,
  let eqs := cons (DiffEqC t 1)
                  (List.app 
                     cp 
                     (List.map
                        (fun x => DiffEqC x (RealT R0)) uc)) in
  (|- (F1 /\ F2 /\ Unchanged uc)
        --> deriv_formula F4 eqs) ->
  (|- ((F1 /\ F2 /\ (Continuous cp b t /\ Unchanged uc))) --> F4).
Admitted.

(*Definition eval_formula_known (known:list Formula) 
  (goal:Formula) : trace -> Prop :=
  eval_formula ((List.fold_right And TRUE known) --> goal).

Notation "l |- F" :=
  (forall tr, eval_formula_known l F tr)
    (at level 100).

Lemma known_start : forall F,
  (nil |- F) ->
  (|- F).
Proof. firstorder. Qed.

Lemma known_cons : forall F1 F2 l,
  (F1::l |- F2) ->
  (l |- F1 --> F2).
Proof. firstorder. Qed.

Lemma and_elim : forall F1 F2 l F,
  (l |- F1 --> (F2 --> F)) ->
  ((F1 /\ F2)::l |- F).
Proof. firstorder. Qed.

Lemma or_elim : forall F1 F2 l F,
  ( l |- F1 --> F) ->
  ( l |- F2 --> F) ->
  ((F1 \/ F2)::l |- F).
Proof. firstorder. Qed.*)

Close Scope HP_scope.