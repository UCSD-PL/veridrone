Require Import TLA.Semantics.
Require Import TLA.ProofRules.
Require Import TLA.Automation.

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
    | SqrtT t => SqrtT (subst_term_term t t2 x next)
    | ArctanT t => ArctanT (subst_term_term t t2 x next)
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
    | Syntax.Exists T F =>
      Syntax.Exists T (fun (i : T) => subst_term_formula (F i) t x next)
    | _ => F
  end.

(* Some notation *)
Notation "F [ t /! x ]" :=
  (subst_term_formula F t x true)
    (at level 50) : HP_scope.
Notation "F [ t // x ]" :=
  (subst_term_formula F t x false)
    (at level 50) : HP_scope.

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
  Admitted. 
(*
  induction t1; simpl; auto; intros; try discriminate;
  try solve [ apply andb_prop in H;
              rewrite IHt1_1; intuition;
              rewrite IHt1_2; intuition ].
  - destruct (String.string_dec x v); auto.
  - rewrite IHt1; intuition.
  - rewrite IHt1; intuition.
  - rewrite IHt1; intuition.
Qed.
*)
Require Import Coq.Logic.FunctionalExtensionality.

Ltac formula_exists_extensionality :=
  match goal with
    | [|- @eq Formula (Syntax.Exists _ ?f) (Syntax.Exists _ ?g)] =>
      cut (f = g);
      [let H := fresh "H" in intro H; rewrite H; auto | apply functional_extensionality]
  end.

Lemma next_subst_formula : forall F t x,
  is_st_formula F ->
  next (subst_term_formula F t x false) =
  subst_term_formula (next F) (next_term t) x true.
Proof.
  induction F; simpl; auto; intros;
  try solve [ rewrite IHF1; intuition;
              rewrite IHF2; intuition ].
  - repeat rewrite next_subst_term; intuition.
  - formula_exists_extensionality.
    intro. apply H. apply H0.
Qed.

Lemma subst_term_term_eq_varnext : forall t1 t2 x,
  x! = t2 |-- subst_term_term t1 t2 x true = t1.
Proof.
  Admitted. 
(*
  induction t1; intros; breakAbstraction; try tlaRefl;
  simpl; unfold eval_comp;
  simpl; auto; intros;
  try (rewrite IHt1_1; auto;
       rewrite IHt1_2; auto).
  - destruct (String.string_dec x v); auto.
    subst x; auto.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
Qed.
*)
Lemma subst_term_term_eq_varnow : forall t1 t2 (x:Var),
  |-- x = t2 -->>
     subst_term_term t1 t2 x false = t1.
Proof.
Admitted.
  (*
  induction t1; simpl; unfold tlaEntails; simpl;
  unfold eval_comp; simpl; auto; intros;
  try (rewrite IHt1_1; auto;
       rewrite IHt1_2; auto).
  - destruct (String.string_dec x v); auto.
    subst x; auto.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
Qed.*)

Lemma subst_term_term_eq_term : forall t1 t2 t3 x b,
  |-- t2 = t3 -->>
     subst_term_term t1 t2 x b =
     subst_term_term t1 t3 x b.
Proof.
  Admitted.
(*
  induction t1; simpl; unfold tlaEntails;
  simpl; unfold eval_comp; simpl; auto; intros;
  try (erewrite IHt1_1; eauto;
       erewrite IHt1_2; eauto).
  - destruct b; auto.
    destruct (String.string_dec x v); auto.
  - destruct b; auto.
    destruct (String.string_dec x v); auto.
  - erewrite IHt1; auto.
  - erewrite IHt1; auto.
  - erewrite IHt1; auto.
Qed.
*)
Lemma subst_term_formula_eval : forall F t1 t2 x b,
  |-- t1 = t2 -->>
     ((subst_term_formula F t1 x b -->>
       subst_term_formula F t2 x b) //\\
      (subst_term_formula F t2 x b -->>
       subst_term_formula F t1 x b)).
Proof.
  induction F; simpl; auto;
  unfold tlaEntails; simpl;
  unfold eval_comp; simpl; intros; try tauto.
  - symmetry in H0.
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
  - symmetry in H0. intuition.
    + eapply IHF2;
      eauto; simpl;
      unfold eval_comp; simpl; intuition;
      apply H1;
      eapply IHF1;
      eauto; simpl;
      unfold eval_comp; simpl; intuition.
    + symmetry in H0. eapply IHF2;
      eauto; simpl;
      unfold eval_comp; simpl; intuition;
      apply H1;
      eapply IHF1;
      eauto; simpl;
      unfold eval_comp; simpl; intuition.
  - intuition;
    inversion H2; clear H2;
    exists x0;
    specialize (H x0 t1 t2 x b tr);
    simpl in H; unfold eval_comp in H;
    apply H in H0;
    intuition.
Qed.

Lemma subst_term_formula_sub : forall F t1 t2 x y b,
  |-- x! = t1 -->>
     (subst_term_formula F
        (subst_term_term t2 t1 x true) y b -->>
      subst_term_formula F t2 y b).
Proof.
  simpl; unfold tlaEntails; simpl; intros.
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
Admitted.
(*  induction t1; simpl; auto; intros;
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
*)

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
  - formula_exists_extensionality.
    intros. apply H; assumption.
Qed.

Lemma subst_formula_eq : forall t (x:Var) F,
  |-- x = t -->>
     ((subst_term_formula F t x false -->> F) //\\
      (F -->> subst_term_formula F t x false)).
Proof.
  induction F; try solve [ simpl; unfold tlaEntails; simpl; auto; intros ].
  - simpl; unfold tlaEntails; simpl; auto; intros.
    unfold eval_comp; simpl.
    erewrite <- subst_term_term_eq_varnow with (t1:=t0);
      eauto.
    erewrite <- subst_term_term_eq_varnow with (t1:=t1);
      eauto.
    red. simpl. eassumption.
  - simpl; unfold tlaEntails; simpl; auto; intros.
    intuition;
    try eapply IHF1;
    try eapply IHF2;
    eauto; intuition.
  - intros. simpl; restoreAbstraction.
    charge_intro.
    apply landAdj in IHF1.
    rewrite landtrueL in IHF1.
    apply landAdj in IHF2.
    rewrite landtrueL in IHF2.
    tlaAssert (x = t). reflexivity.
    etransitivity. eapply IHF1.
    rewrite IHF2.
    charge_intro. charge_fwd.
    charge_split; charge_intro;
    repeat rewrite Lemmas.land_lor_distr_L;
    apply lorL; charge_fwd.
    apply lorR1. charge_tauto.
    apply lorR2. charge_tauto.
    apply lorR1. charge_tauto.
    apply lorR2. charge_tauto.
  - simpl. restoreAbstraction.
    charge_intro.
    apply landAdj in IHF1.
    rewrite landtrueL in IHF1.
    apply landAdj in IHF2.
    rewrite landtrueL in IHF2.
    tlaAssert (x = t). reflexivity.
    etransitivity. eapply IHF1.
    rewrite IHF2.
    clear. charge_intro.
    charge_split; charge_intros; charge_fwd; charge_tauto.
  - simpl. restoreAbstraction.
    charge_intro; charge_split; charge_intro; charge_fwd.
    { specialize (H x0).
      apply landAdj in H. rewrite landtrueL in H.
      rewrite H.
      eapply lexistsR; instantiate(1 :=x0).
      charge_fwd. charge_tauto. }
    { specialize (H x0).
      apply landAdj in H. rewrite landtrueL in H.
      rewrite H.
      eapply lexistsR; instantiate(1 :=x0).
      charge_fwd. charge_tauto. }
Qed.

Lemma subst_term_eq_next : forall t1 x t2,
  |-- x! = t2
     -->> subst_term_term t1 t2 x true =
         t1.
Proof.
Admitted.
(*
  induction t1; simpl; unfold tlaEntails;
  simpl; unfold eval_comp; simpl; auto; intros;
  try (rewrite IHt1_1; auto;
       rewrite IHt1_2; auto).
  - destruct (String.string_dec x v);
    simpl; congruence.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
  - rewrite IHt1; auto.
Qed.
*)
Lemma subst_eq_next : forall F x t,
  |-- x! = t
    -->> ((F[t/!x] -->> F) //\\
         (F -->> F[t/!x])).
Proof.
  induction F; simpl; unfold tlaEntails; simpl;
  try solve [intuition]; intros.
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
    apply H1; eapply IHF1; eauto.
  - split; intro H2; inversion H2; clear H2;
    specialize (H x0 x t tr); simpl in H;
    apply H in H0; inversion H0;
    try eexists; eauto.
Qed.

Close Scope HP_scope.
