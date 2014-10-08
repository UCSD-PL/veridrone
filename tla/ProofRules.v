Require Import TLA.Syntax.
Require Import TLA.Semantics.

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

Lemma inv_ind : forall I N,
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

Close Scope HP_scope.