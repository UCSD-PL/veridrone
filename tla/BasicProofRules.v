Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.Automation.

(* Various proof rules for TLA in general *)

Open Scope HP_scope.

(* First, a few functions for expressing
   the proof rules *)

(* Puts ! on all variables in a Term *)
Fixpoint next_term (t:Term) :=
  match t with
    | NatT n => NatT n
    | RealT r => RealT r
    | VarNowT x => VarNextT x
    | VarNextT x => VarNextT x
    | PlusT t1 t2 => PlusT (next_term t1)
                           (next_term t2)
    | MinusT t1 t2 => MinusT (next_term t1)
                             (next_term t2)
    | MultT t1 t2 => MultT (next_term t1)
                           (next_term t2)
    | InvT t => InvT (next_term t)
    | CosT t => CosT (next_term t)
    | SinT t => SinT (next_term t)
  end.

(* Puts ! on all variables in a Formula *)
Fixpoint next (F:Formula) :=
  match F with
    | TRUE => ltrue
    | FALSE => lfalse
    | Comp t1 t2 op => Comp (next_term t1) (next_term t2) op
    | And F1 F2 => next F1 //\\ next F2
    | Or F1 F2 => next F1 \\// next F2
    | Imp F1 F2 => next F1 -->> next F2
    | Syntax.Exists _ f => Exists x, next (f x)
    | Syntax.Forall _ f => Forall x, next (f x)
    | PropF P => PropF P
    | Always F => Always (next F)
    | Eventually F => Eventually (next F)
    | Embed P => Embed (fun _ en => P en en)
  end.

(* Returns true iff the Term has no ! *)
Fixpoint is_st_term (t:Term) : bool :=
  match t with
    | NatT _ => true
    | RealT _ => true
    | VarNowT _ => true
    | VarNextT x => false
    | PlusT t1 t2 => andb (is_st_term t1)
                          (is_st_term t2)
    | MinusT t1 t2 => andb (is_st_term t1)
                           (is_st_term t2)
    | MultT t1 t2 => andb (is_st_term t1)
                          (is_st_term t2)
    | InvT t => is_st_term t
    | CosT t => is_st_term t
    | SinT t => is_st_term t
  end.

(* Prop expressing that the Formula has no
   !. This cannot be a bool because of
   Forall and Exists. *)
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
    | Syntax.Exists _ f =>
      forall x, is_st_formula (f x)
    | Syntax.Forall _ f =>
      forall x, is_st_formula (f x)
    | PropF _ => True
    | _ => False
  end.

(* The bool version of is_st_formula. This
   one is incomplete. If it returns true,
   the Formula does not have any !, but if
   it returns false, the Formula may or may
   not have a !. This incompleteness is because
   of Forall and Exists. *)
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

(* Now a few helper lemmas *)


Lemma next_term_tl : forall t s1 s2 s3,
  is_st_term t = true ->
  eval_term (next_term t) s1 s2 =
  eval_term t s2 s3.
Proof.
  intros t s1 s2 s3 Hst.
  induction t; auto; simpl in *;
  try discriminate;
  try (try apply andb_prop in Hst; intuition;
       rewrite H1; rewrite H2; auto).
Qed.

Lemma next_formula_tl : forall F tr,
  is_st_formula F ->
  (eval_formula (next F) tr <->
   eval_formula F (Stream.tl tr)).
Proof.
  intros F tr Hst; induction F; simpl in *;
  try tauto.
  - unfold eval_comp in *. simpl in *.
    rewrite <- next_term_tl with (s1:=Stream.hd tr) (t:=t).
    rewrite <- next_term_tl with (s1:=Stream.hd tr) (t:=t0).
    intuition. intuition. intuition.
  - split; intro He; destruct He as [x ?];
    exists x; apply H; auto.
  - split; intros; apply H; auto.
Qed.

(* And finally the proof rules *)

(* A discrete induction rule *)
Lemma inv_discr_ind : forall I N,
  is_st_formula I ->
  (|-- (I //\\ N) -->> (next I)) ->
  (|-- (I //\\ []N) -->> []I).
Proof.
  intros I N Hst Hind. simpl in *.
  intros tr _ [HI HAN] n. fold eval_formula in *.
  induction n; auto.
  simpl. rewrite Stream.nth_suf_tl.
  apply next_formula_tl; intuition.
  eapply Hind; fold eval_formula.
  simpl. trivial.
  auto.
Qed.

Lemma discr_ind : forall P A I N,
    is_st_formula I ->
    (P |-- [] A) ->
    (A |-- I //\\ N -->> next I) ->
    (P |-- (I //\\ []N) -->> []I).
Proof.
  intros. rewrite H0; clear H0.
  intro. simpl; intros.
  induction n.
  { simpl. tauto. }
  { simpl. rewrite Stream.nth_suf_tl.
    apply next_formula_tl; auto.
    apply H1; auto.
    split; auto. destruct H2. apply H3. }
Qed.

Lemma discr_indX : forall P A IndInv,
    is_st_formula IndInv ->
    P |-- [] A ->
    P |-- IndInv ->
    A //\\ IndInv |-- next IndInv ->
    P |-- []IndInv.
Proof.
  intros.
  intro. simpl; intros.
  specialize (H0 _ H3).
  induction n.
  { simpl. intros; eapply H1. auto. }
  { simpl. rewrite Stream.nth_suf_tl.
    apply next_formula_tl; auto.
    apply H2; auto.
    split; auto. }
Qed.


Section in_context.
  Variable C : Formula.

(* A variety of basic propositional
   and temporal logic proof rules *)
Lemma imp_trans : forall F1 F2 F3,
  (C |-- F1 -->> F2) ->
  (C |-- F2 -->> F3) ->
  (C |-- F1 -->> F3).
Proof. intros; charge_tauto. Qed.

Lemma always_imp : forall F1 F2,
  (|-- F1 -->> F2) ->
  (C |-- []F1 -->> []F2).
Proof. tlaIntuition. Qed.

Lemma always_and_left : forall F1 F2 F3,
  (C |-- [](F1 //\\ F2) -->> F3) ->
  (C |-- ([]F1 //\\ []F2) -->> F3).
Proof. tlaIntuition. Qed.

Lemma and_right : forall F1 F2 F3,
  (C |-- F1 -->> F2) ->
  (C |-- F1 -->> F3) ->
  (C |-- F1 -->> (F2 //\\ F3)).
Proof. intros; charge_tauto. Qed.

Lemma and_left1 : forall F1 F2 F3,
  (C |-- F1 -->> F3) ->
  (C |-- (F1 //\\ F2) -->> F3).
Proof. intros; charge_tauto. Qed.

Lemma and_left2 : forall F1 F2 F3,
  (C |-- F2 -->> F3) ->
  (C |-- (F1 //\\ F2) -->> F3).
Proof. intros; charge_tauto. Qed.

Lemma imp_id : forall F,
  |-- F -->> F.
Proof. intros; charge_tauto. Qed.

Lemma or_next : forall F1 F2 N1 N2,
  (C |-- (F1 //\\ N1) -->> F2) ->
  (C |-- (F1 //\\ N2) -->> F2) ->
  (C |-- (F1 //\\ (N1 \\// N2)) -->> F2).
Proof. tlaIntuition. Qed.

Lemma or_left : forall F1 F2 F3,
  (C |-- F1 -->> F3) ->
  (C |-- F2 -->> F3) ->
  (C |-- (F1 \\// F2) -->> F3).
Proof. tlaIntuition. Qed.

Lemma or_right1 : forall F1 F2 F3,
  (C |-- F1 -->> F2) ->
  (C |-- F1 -->> (F2 \\// F3)).
Proof. tlaIntuition. Qed.

Lemma or_right2 : forall F1 F2 F3,
  (C |-- F1 -->> F3) ->
  (C |-- F1 -->> (F2 \\// F3)).
Proof. tlaIntuition. Qed.

Lemma imp_right : forall F1 F2 F3,
  (C |-- (F1 //\\ F2) -->> F3) ->
  (C |-- F1 -->> (F2 -->> F3)).
Proof. intros; charge_tauto. Qed.

Lemma imp_strengthen : forall F1 F2 F3,
  (C |-- F1 -->> F2) ->
  (C |-- (F1 //\\ F2) -->> F3) ->
  (C |-- F1 -->> F3).
Proof. intros; charge_tauto. Qed.

Lemma and_assoc_left : forall F1 F2 F3 F4,
  (C |-- (F1 //\\ (F2 //\\ F3)) -->> F4) ->
  (C |-- ((F1 //\\ F2) //\\ F3) -->> F4).
Proof. intros; charge_tauto. Qed.

Lemma and_comm_left : forall F1 F2 F3,
  (C |-- (F2 //\\ F1) -->> F3) ->
  (C |-- (F1 //\\ F2) -->> F3).
Proof. intros; charge_tauto. Qed.

Lemma forall_right : forall T F G,
  (forall x, |-- F -->> G x) ->
  (C |-- F -->> @lforall Formula _ T G).
Proof. tlaIntuition. Qed.

Close Scope HP_scope.

End in_context.

Lemma always_tauto : forall G P, |-- P -> G |-- [] P.
Proof. tlaIntuition. Qed.

Lemma next_inv : forall N I,
  is_st_formula I ->
  (|-- [](N //\\ I) -->> [](N //\\ I //\\ next I)).
Proof.
  intros. breakAbstraction. intuition.
  - apply H1.
  - apply H1.
  - apply next_formula_tl; auto.
    rewrite <- Stream.nth_suf_Sn.
    apply H1.
Qed.

Lemma next_inv' : forall G P Q Z,
  is_st_formula Q ->
  (|-- P -->> Q) ->
  (|-- P //\\ next Q -->> Z) ->
  (G |-- []P -->> []Z).
Proof.
  tlaIntuition.
  - apply H1; auto.
    split; auto.
    apply next_formula_tl; auto.
    rewrite <- Stream.nth_suf_Sn. auto.
Qed.

(** Always **)
Lemma Always_and : forall P Q,
    []P //\\ []Q -|- [](P //\\ Q).
Proof.
  intros. split.
  { breakAbstraction. intros. intuition. }
  { breakAbstraction; split; intros; edestruct H; eauto. }
Qed.

Lemma Always_or : forall P Q,
    []P \\// []Q |-- [](P \\// Q).
Proof. tlaIntuition. Qed.

Lemma always_st : forall Q,
    is_st_formula Q ->
    [] Q -|- [] (Q //\\ next Q).
Proof.
  intros. split.
  { rewrite <- Always_and. charge_split; try charge_tauto.
    breakAbstraction. intros.
    rewrite next_formula_tl; auto.
    rewrite <- Stream.nth_suf_Sn. eauto. }
  { rewrite <- Always_and. charge_tauto. }
Qed.

Lemma Always_now : forall P I,
  P |-- []I ->
  P |-- I.
Proof.
  breakAbstraction.
  intros P I H tr HP.
  apply (H tr HP 0).
Qed.


(** Existential quantification **)
Lemma exists_entails : forall T F1 F2,
  (forall x, F1 x |-- F2 x) ->
  Exists x : T, F1 x |-- Exists x : T, F2 x.
Proof.
  tlaIntuition.  destruct H0.
  exists x. intuition.
Qed.
