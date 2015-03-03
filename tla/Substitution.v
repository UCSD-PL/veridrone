Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.ProofRules.

Open Scope HP_scope.

(* Functions for substituting terms for
   variables in TLA Formulas and lemmas
   about these substitutions. The function
   that substitutes terms for variables in
   a formula is called subst_term_formula. *)

(* If next is true, substitutes t2 for x! in t2.
   If next is false, substitutes t2 for x in t2. *)
Fixpoint subst_term_term (t1 t2 : Term) (x : Var)
         (next:bool) :=
  match t1 with
    | VarNowT y =>
      if next
      then t1
      else if String.string_dec x y
           then t2
           else t1
    | VarNextT y =>
      if next
      then if String.string_dec x y
           then t2
           else t1
      else t1
    | PlusT t3 t4 =>
      PlusT (subst_term_term t3 t2 x next)
            (subst_term_term t4 t2 x next)
    | MinusT t3 t4 =>
      MinusT (subst_term_term t3 t2 x next)
             (subst_term_term t4 t2 x next)
    | MultT t3 t4 =>
      MultT (subst_term_term t3 t2 x next)
            (subst_term_term t4 t2 x next)
    | InvT t =>
      InvT (subst_term_term t t2 x next)
    | CosT t =>
      CosT (subst_term_term t t2 x next)
    | SinT t =>
      SinT (subst_term_term t t2 x next)
    | NatT _ => t1
    | RealT _ => t1
  end.

(* If next is true, substitutes t for x! in F.
   If next is false, substitutes t for x in F. *)
Fixpoint subst_term_formula (F:Formula) (t : Term) (x : Var)
         (next:bool) :=
  match F with
    | Comp t1 t2 op =>
      Comp (subst_term_term t1 t x next)
           (subst_term_term t2 t x next) op
    | And F1 F2 =>
           (subst_term_formula F1 t x next)
      //\\ (subst_term_formula F2 t x next)
    | Or F1 F2 =>
           (subst_term_formula F1 t x next)
      \\// (subst_term_formula F2 t x next)
    | Imp F1 F2 =>
           (subst_term_formula F1 t x next)
      -->> (subst_term_formula F2 t x next)
    | _ => F
  end.

(* Some notation *)
Notation "F [ t /! x ]" :=
  (subst_term_formula F t x true)
    (at level 50).
Notation "F [ t // x ]" :=
  (subst_term_formula F t x false)
    (at level 50).

(* And now a whole bunch of lemmas about
   substitutions. *)

Lemma subst_st_term : forall t1 t2 x b,
  is_st_term t1 = true ->
  is_st_term t2 = true ->
  is_st_term
    (subst_term_term t1 t2 x b) = true.
Proof.
  induction t1; simpl; auto; intros; try discriminate;
  try (apply andb_prop in H; intuition).
  - destruct b; destruct (String.string_dec x v); auto.
Qed.

Lemma subst_st_formula : forall F t x b,
  is_st_formula F ->
  is_st_term t = true ->
  is_st_formula
    (subst_term_formula F t x b).
Proof.
  induction F; simpl; auto; intros; intuition;
  apply subst_st_term; intuition.
Qed.

Lemma next_subst_term : forall t1 t2 x,
  is_st_term t1 = true ->
  next_term (subst_term_term t1 t2 x false) =
  subst_term_term (next_term t1) (next_term t2) x true.
Proof.
  induction t1; simpl; auto; intros; try discriminate;
  try solve [ apply andb_prop in H;
              rewrite IHt1_1; intuition;
              rewrite IHt1_2; intuition ].
  - destruct (String.string_dec x v); auto.
  - rewrite IHt1; intuition.
  - rewrite IHt1; intuition.
  - rewrite IHt1; intuition.
Qed.

Lemma next_subst_formula : forall F t x,
  is_st_formula F ->
  next (subst_term_formula F t x false) =
  subst_term_formula (next F) (next_term t) x true.
Proof.
  induction F; simpl; auto; intros;
  try solve [ rewrite IHF1; intuition;
              rewrite IHF2; intuition ].
  - repeat rewrite next_subst_term; intuition.
Qed.

Lemma subst_term_term_eq_varnext : forall t1 t2 x,
  |-- x! = t2 -->>
     subst_term_term t1 t2 x true = t1.
Proof.
  induction t1; simpl; unfold eval_comp;
  simpl; auto; intros;
  try (rewrite IHt1_1; auto;
       rewrite IHt1_2; auto).
  - destruct (String.string_dec x v); auto.
    subst x; auto.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
Qed.

Lemma subst_term_term_eq_varnow : forall t1 t2 (x:Var),
  |- x = t2 -->
     subst_term_term t1 t2 x false = t1.
Proof.
  induction t1; simpl; unfold eval_comp;
  simpl; auto; intros;
  try (rewrite IHt1_1; auto;
       rewrite IHt1_2; auto).
  - destruct (String.string_dec x v); auto.
    subst x; auto.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
Qed.

Lemma subst_term_term_eq_term : forall t1 t2 t3 x b,
  |- t2 = t3 -->
     subst_term_term t1 t2 x b =
     subst_term_term t1 t3 x b.
Proof.
  induction t1; simpl; unfold eval_comp;
  simpl; auto; intros;
  try (rewrite IHt1_1; eauto;
       rewrite IHt1_2; eauto).
  - destruct b; auto.
    destruct (String.string_dec x v); auto.
  - destruct b; auto.
    destruct (String.string_dec x v); auto.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
Qed.

Lemma subst_term_formula_eval : forall F t1 t2 x b,
  |- t1 = t2 -->
     ((subst_term_formula F t1 x b -->
       subst_term_formula F t2 x b) /\
      (subst_term_formula F t2 x b -->
       subst_term_formula F t1 x b)).
Proof.
  induction F; simpl; auto;
  unfold eval_comp; simpl; intros.
  - symmetry in H.
    rewrite subst_term_term_eq_term  with (t2:=t2) (t3:=t1);
      auto.
    rewrite subst_term_term_eq_term with (t2:=t2) (t3:=t1);
      auto.
  - intuition;
    try eapply IHF1;
    try eapply IHF2;
    eauto; simpl;
    unfold eval_comp; simpl; intuition.
  - intuition;
    [ left; eapply IHF1 |
      right; eapply IHF2 |
      left; eapply IHF1 |
      right; eapply IHF2 ];
    eauto; simpl;
    unfold eval_comp; simpl; intuition.
  - symmetry in H. intuition.
    + eapply IHF2;
      eauto; simpl;
      unfold eval_comp; simpl; intuition;
      apply H0;
      eapply IHF1;
      eauto; simpl;
      unfold eval_comp; simpl; intuition.
    + symmetry in H. eapply IHF2;
      eauto; simpl;
      unfold eval_comp; simpl; intuition;
      apply H0;
      eapply IHF1;
      eauto; simpl;
      unfold eval_comp; simpl; intuition.
Qed.

Lemma subst_term_formula_sub : forall F t1 t2 x y b,
  |- x! = t1 -->
     (subst_term_formula F
        (subst_term_term t2 t1 x true) y b -->
      subst_term_formula F t2 y b).
Proof.
  simpl; intros.
  eapply subst_term_formula_eval
  with (t2:=t2) (t1:=subst_term_term t2 t1 x true);
    auto.
  apply subst_term_term_eq_varnext; auto.
Qed.

Lemma subst_term_term_comm : forall t1 t2 t3 x y b1 b2,
  x <> y ->
  subst_term_term t2 t3 y b2 = t2 ->
  subst_term_term t3 t2 x b1 = t3 ->
  subst_term_term
    (subst_term_term t1 t2 x b1)
    t3 y b2 =
  subst_term_term
    (subst_term_term t1 t3 y b2)
    t2 x b1.
Proof.
  induction t1; simpl; auto; intros;
  try (rewrite IHt1_1; auto;
       rewrite IHt1_2; auto).
  - unfold subst_term_term;
    destruct b1; destruct b2; auto;
    destruct (String.string_dec x v);
    destruct (String.string_dec y v);
    try subst x; try subst y; intuition.
    + destruct (String.string_dec v v);
      intuition.
    + destruct (String.string_dec x v);
      intuition.
  - unfold subst_term_term;
    destruct b1; destruct b2; auto;
    destruct (String.string_dec x v);
    destruct (String.string_dec y v);
    try subst x; try subst y; intuition.
    + destruct (String.string_dec v v);
      intuition.
    + destruct (String.string_dec x v);
      intuition.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
Qed.

Lemma subst_term_formula_comm : forall F t1 t2 x y b1 b2,
  x <> y ->
  subst_term_term t1 t2 y b2 = t1 ->
  subst_term_term t2 t1 x b1 = t2 ->
  subst_term_formula
    (subst_term_formula F t1 x b1)
    t2 y b2 =
  subst_term_formula
    (subst_term_formula F t2 y b2)
    t1 x b1.
Proof.
  induction F; simpl; auto; intros;
  try (rewrite IHF1; auto;
       rewrite IHF2; auto).
  - rewrite subst_term_term_comm with (t1:=t); auto.
    rewrite subst_term_term_comm with (t1:=t0); auto.
Qed.

Lemma subst_formula_eq : forall F t (x:Var),
  |- x = t -->
     ((subst_term_formula F t x false --> F) /\
      (F --> subst_term_formula F t x false)).
Proof.
  induction F; simpl; auto; intros.
  - unfold eval_comp; simpl.
    rewrite <- subst_term_term_eq_varnow with (t1:=t);
      eauto.
    rewrite <- subst_term_term_eq_varnow with (t1:=t0);
      eauto.
  - intuition;
    try eapply IHF1;
    try eapply IHF2;
    eauto; intuition.
  - intuition;
    [ left; eapply IHF1 |
      right; eapply IHF2 |
      left; eapply IHF1 |
      right; eapply IHF2 ];
    eauto; intuition.
  - intuition;
    eapply IHF2; eauto;
    apply H0; eapply IHF1; eauto.
Qed.

Lemma subst_term_eq_next : forall t1 x t2,
  |- x! = t2
     --> subst_term_term t1 t2 x true =
         t1.
Proof.
  induction t1; simpl; unfold eval_comp;
  simpl; auto; intros;
  try (rewrite IHt1_1; auto;
       rewrite IHt1_2; auto).
  - destruct (String.string_dec x v);
    simpl; congruence.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
Qed.

Lemma subst_eq_next : forall F x t,
  |- x! = t
    --> ((F[t/!x] --> F) /\
         (F --> F[t/!x])).
Proof.
  induction F; simpl; try solve [intuition]; intros.
  - unfold eval_comp in *; simpl in *.
    repeat rewrite subst_term_eq_next;
      simpl; auto.
  - repeat split; intros;
    (eapply IHF1; eauto; intuition) ||
    (eapply IHF2; eauto; intuition).
  - split; intuition.
    + left; eapply IHF1; eauto; intuition.
    + right; eapply IHF2; eauto; intuition.
    + left; eapply IHF1; eauto; intuition.
    + right; eapply IHF2; eauto; intuition.
  - split; intros;
    eapply IHF2; eauto;
    apply H0; eapply IHF1; eauto.
Qed.

Close Scope HP_scope.