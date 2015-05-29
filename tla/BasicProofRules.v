Require Import Coq.Classes.Morphisms.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Automation.
Require Import Rdefinitions.

(* Various proof rules for TLA in general *)

Open Scope HP_scope.

Lemma exists_iff : forall {T} (P Q: T -> Prop),
    (forall x, P x <-> Q x) ->
    ((exists x, P x) <-> (exists x, Q x)).
Proof.
  split; destruct 1; eexists; apply H; eauto.
Qed.
Lemma forall_iff : forall {T} (P Q: T -> Prop),
    (forall x, P x <-> Q x) ->
    ((forall x, P x) <-> (forall x, Q x)).
Proof. split; intuition; firstorder. Qed.

Global Instance Proper_eval_formula
: Proper (eq ==> Stream.stream_eq eq ==> iff) eval_formula.
Proof.
  red. red. intros. subst.
  red.
  induction y; simpl; intros; try tauto.
  { eapply Stream.stream_eq_eta in H.
    rewrite Stream.stream_eq_eta in H.
    destruct H as [ ? [ ? ? ] ].
    rewrite H. rewrite H0. reflexivity. }
  { rewrite IHy1; eauto.
    rewrite IHy2; eauto.
    reflexivity. }
  { rewrite IHy1; eauto.
    rewrite IHy2; eauto.
    reflexivity. }
  { rewrite IHy1; eauto.
    rewrite IHy2; eauto.
    reflexivity. }
  { admit. }
  { eapply exists_iff; intros.
    eauto. }
  { eapply forall_iff; intros.
    eauto. }
  { eapply exists_iff; intros.
    eapply IHy.
    eapply Stream.stream_eq_eta in H.
    destruct H.
    constructor; simpl; auto.
    reflexivity. }
  { eapply forall_iff. intros.
    eapply IHy.
    eapply Stream.Proper_nth_suf_stream_eq; eauto. }
  { eapply exists_iff; intros.
    eapply IHy.
    eapply Stream.Proper_nth_suf_stream_eq; eauto. }
  { do 2 rewrite Stream.stream_eq_eta in H.
    destruct H as [ ? [ ? ? ] ].
    rewrite H. rewrite H0. reflexivity. }
  { eapply IHy. eapply Stream.Proper_stream_map; eauto.
    red. intros. subst. reflexivity. }
Qed.

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
    | Continuous w => Continuous (fun st' => next (w st'))
    | Enabled F => Enabled (next F)
    | Always F => Always (next F)
    | Eventually F => Eventually (next F)
    | Embed P => Embed (fun _ en => P en en)
    | Rename s P => Rename s (next P)
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
    | Rename _ x => is_st_formula x
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
    | Rename _ x => is_st_formula_b x
    | _ => false
  end.

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
  fst (Stream.hd tr1) = fst (Stream.hd tr2) ->
  eval_formula F tr2.
Proof.
  induction F; intros; simpl in *; auto;
  try tauto; try discriminate.
  - unfold eval_comp in *. simpl in *.
    rewrite st_term_hd
    with (t:=t) (s3:=fst (Stream.hd (Stream.tl tr1)));
      intuition.
    rewrite st_term_hd
    with (t:=t0) (s3:=fst (Stream.hd (Stream.tl tr1)));
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
  - eapply IHF; eauto.
    destruct tr1; destruct tr2. simpl in H1.
    simpl. destruct H1. reflexivity.
Qed.

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
  induction F; simpl in *; intros ;
  try tauto.
  - unfold eval_comp in *. simpl in *.
    rewrite <- next_term_tl with (s1:=fst (Stream.hd tr)) (t:=t).
    rewrite <- next_term_tl with (s1:=fst (Stream.hd tr)) (t:=t0).
    intuition. intuition. intuition.
  - rewrite IHF1; try rewrite IHF2; tauto.
  - rewrite IHF1; try rewrite IHF2; tauto.
  - rewrite IHF1; try rewrite IHF2; tauto.
  - eapply exists_iff.
    intros; eapply H; eauto.
  - eapply forall_iff; eauto.
  - rewrite IHF; eauto.
    eapply Proper_eval_formula. reflexivity.
    eapply Stream.stream_map_tl. apply eq_equivalence.
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

Lemma eventually_imp : forall F1 F2,
  (|-- F1 -->> F2) ->
  (C |-- <>F1 -->> <>F2).
Proof.
  tlaIntuition. destruct H1. exists x. auto.
Qed.

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

(* Enabled *)
Lemma Enabled_action : forall P,
    (forall st, exists st',
          eval_formula P (Stream.Cons st (Stream.forever st'))) ->
    |-- Enabled P.
Proof.
  breakAbstraction; intros.
  specialize (H (Stream.hd tr)). destruct H.
  exists (Stream.forever x). auto.
Qed.

Lemma ex_state : forall (v : Var) (P : state -> Prop),
    (exists st,
        (exists val, P
          (fun v' => if String.string_dec v v'
                     then val else st v'))) ->
      exists st, P st.
Proof.
  intros. destruct H. destruct H. eauto.
Qed.

Lemma ex_state_any : forall (P : state -> Prop),
    (forall st, P st) ->
    exists st, P st.
Proof.
  intros. exists (fun _ => 0%R). eauto.
Qed.

Definition find_term (m : RenameMap) (x : Var) : option Term :=
  option_map
    (@snd _ Term)
    (List.find (fun p =>
                  if String.string_dec x (fst p)
                  then true else false) m).

(* Some renaming functions and proof rules. *)
Fixpoint rename_term (m : RenameMap) (t:Term) :=
  match t with
    | NatT n => NatT n
    | RealT r => RealT r
    | VarNowT x =>
      match find_term m x with
      | Some t => t
      | None => VarNowT x
      end
    | VarNextT x =>
      match find_term m x with
      | Some t => next_term t
      | None => VarNextT x
      end
    | PlusT t1 t2 => PlusT (rename_term m t1)
                           (rename_term m t2)
    | MinusT t1 t2 => MinusT (rename_term m t1)
                             (rename_term m t2)
    | MultT t1 t2 => MultT (rename_term m t1)
                           (rename_term m t2)
    | InvT t => InvT (rename_term m t)
    | CosT t => CosT (rename_term m t)
    | SinT t => SinT (rename_term m t)
  end.

Fixpoint rename_formula (m : RenameMap) (F:Formula) :=
  match F with
    | TRUE => ltrue
    | FALSE => lfalse
    | Comp t1 t2 op => Comp (rename_term m t1)
                            (rename_term m t2) op
    | And F1 F2 => rename_formula m F1 //\\ rename_formula m F2
    | Or F1 F2 => rename_formula m F1 \\// rename_formula m F2
    | Imp F1 F2 => rename_formula m F1 -->> rename_formula m F2
    | Syntax.Exists _ f => Exists x, rename_formula m (f x)
    | Syntax.Forall _ f => Forall x, rename_formula m (f x)
    | PropF P => PropF P
    | Continuous w => Rename m (Continuous w)
    | Enabled F => Rename m (Enabled F)
    | Always F => Always (rename_formula m F)
    | Eventually F => Eventually (rename_formula m F)
    | Embed P => Rename m (Embed P)
    | Rename s P => Rename m (Rename s P)
  end.

Lemma find_term_now_Some_ok : forall m x t st1 st2,
  List.Forall (fun p => eq (is_st_term (snd p)) true) m ->
  find_term m x = Some t ->
  eval_term t st1 st2 =
  subst_state m st1 x.
Proof.
  induction m; unfold find_term; simpl.
  - discriminate.
  - intros. destruct a. simpl in *.
    match goal with
    |- context [ String.string_dec ?e1 ?e2 ] =>
    destruct (String.string_dec e1 e2)
    end.
    + subst. simpl in *.
      apply List.Forall_inv in H. simpl in *.
      inversion H0. subst.
      apply st_term_hd. auto.
    + apply IHm; auto. inversion H. auto.
Qed.


Lemma find_term_now_None_ok : forall m x st1 st2,
  find_term m x = None ->
  eval_term (VarNowT x) st1 st2 =
  subst_state m st1 x.
Proof.
  induction m; unfold find_term; simpl.
  - auto.
  - intros. destruct a. simpl in *.
    match goal with
    |- context [ String.string_dec ?e1 ?e2 ] =>
    destruct (String.string_dec e1 e2)
    end.
    + simpl in *. discriminate.
    + apply IHm; auto.
Qed.

Lemma find_term_next_Some_ok : forall m x t st1 st2,
  List.Forall (fun p => eq (is_st_term (snd p)) true) m ->
  find_term m x = Some t ->
  eval_term (next_term t) st1 st2 =
  subst_state m st2 x.
Proof.
  induction m; unfold find_term; simpl.
  - discriminate.
  - intros. destruct a. simpl in *.
    match goal with
    |- context [ String.string_dec ?e1 ?e2 ] =>
    destruct (String.string_dec e1 e2)
    end.
    + subst. simpl in *.
      apply List.Forall_inv in H. simpl in *.
      inversion H0. subst.
      apply next_term_tl. auto.
    + apply IHm; auto. inversion H. auto.
Qed.

Lemma find_term_next_None_ok : forall m x st1 st2,
  find_term m x = None ->
  eval_term (VarNextT x) st1 st2 =
  subst_state m st2 x.
Proof.
  induction m; unfold find_term; simpl.
  - auto.
  - intros. destruct a. simpl in *.
    match goal with
    |- context [ String.string_dec ?e1 ?e2 ] =>
    destruct (String.string_dec e1 e2)
    end.
    + simpl in *. discriminate.
    + apply IHm; auto.
Qed.

Lemma Rename_term_ok : forall m t st1 st2,
  List.Forall (fun p => eq (is_st_term (snd p)) true) m ->
  eval_term (rename_term m t) st1 st2 =
  eval_term t (subst_state m st1) (subst_state m st2).
Proof.
  induction t; simpl; intros; auto;
  try solve [rewrite IHt1; auto; rewrite IHt2; auto |
             rewrite IHt; auto ].
  - destruct (find_term m v) eqn:?.
    + erewrite find_term_now_Some_ok; auto.
    + erewrite find_term_now_None_ok; auto.
  - destruct (find_term m v) eqn:?.
    + erewrite find_term_next_Some_ok; auto.
    + erewrite find_term_next_None_ok; auto.
Qed.

Lemma Rename_true : forall m,
  Rename m TRUE -|- TRUE.
Proof.
  intros; split; breakAbstraction; auto.
Qed.

Lemma Rename_false : forall m,
  Rename m FALSE -|- FALSE.
Proof.
  intros; split; breakAbstraction; auto.
Qed.


Lemma Rename_comp : forall m t1 t2 op,
  List.Forall (fun p => eq (is_st_term (snd p)) true) m ->
  Rename m (Comp t1 t2 op) -|-
  rename_formula m (Comp t1 t2 op).
Proof.
  split; breakAbstraction; intros.
    + unfold eval_comp in *.
      repeat (rewrite Rename_term_ok; auto).
      destruct tr as [st1 [st2 tr]]. auto.
    + unfold eval_comp in *.
      repeat (rewrite Rename_term_ok in H0; auto).
      destruct tr as [st1 [st2 tr]]. auto.
Qed.

Lemma Rename_and : forall m F1 F2,
  Rename m (F1 //\\ F2) -|-
  Rename m F1 //\\ Rename m F2.
Proof.
  intros; split; breakAbstraction; auto.
Qed.

Lemma Rename_or : forall m F1 F2,
  Rename m (F1 \\// F2) -|-
  Rename m F1 \\// Rename m F2.
Proof.
  intros; split; breakAbstraction; auto.
Qed.

Lemma Rename_impl : forall m F1 F2,
  Rename m (F1 -->> F2) -|-
  Rename m F1 -->> Rename m F2.
Proof.
  intros; split; breakAbstraction; auto.
Qed.

Lemma Rename_prop : forall m P,
  Rename m (PropF P) -|- PropF P.
Proof.
  intros; split; breakAbstraction; auto.
Qed.

Lemma Rename_exists : forall T m f,
  Rename m (Syntax.Exists T f) -|-
  Syntax.Exists T (fun x => Rename m (f x)).
Proof.
  intros; split; breakAbstraction; auto.
Qed.

Lemma Rename_forall : forall T m f,
  Rename m (Syntax.Forall T f) -|-
  Syntax.Forall T (fun x => Rename m (f x)).
Proof.
  intros; split; breakAbstraction; auto.
Qed.

Lemma Rename_always : forall m F,
  Rename m (Always F) -|-
  Always (Rename m F).
Proof.
  intros; split; breakAbstraction; intros.
  { specialize (H n).
    rewrite Stream.stream_map_nth_suf in H; auto. }
  { rewrite Stream.stream_map_nth_suf; auto. }
Qed.

Lemma Rename_eventually : forall m F,
  Rename m (Eventually F) -|-
  Eventually (Rename m F).
Proof.
  intros; split; breakAbstraction; intros.
  { destruct H as [n H].
    rewrite Stream.stream_map_nth_suf in H; eauto. }
  { destruct H as [n H].
    exists n. rewrite Stream.stream_map_nth_suf; auto. }
Qed.

Lemma Rename_ok : forall m F,
  List.Forall (fun p => eq (is_st_term (snd p)) true) m ->
  rename_formula m F -|- Rename m F.
Proof.
  induction F; intros.
  - apply Rename_true with (m:=m).
  - apply Rename_false with (m:=m).
  - rewrite Rename_comp; auto.
  - rewrite Rename_and. simpl rename_formula.
    restoreAbstraction. rewrite IHF1; auto.
    rewrite IHF2; auto.
  - rewrite Rename_or. simpl rename_formula.
    restoreAbstraction. rewrite IHF1; auto.
    rewrite IHF2; auto.
  - rewrite Rename_impl. simpl rename_formula.
    restoreAbstraction. rewrite IHF1; auto.
    rewrite IHF2; auto.
  - rewrite Rename_prop. simpl rename_formula.
    split; charge_tauto.
  - split; charge_tauto.
  - rewrite Rename_exists. simpl rename_formula.
    split; breakAbstraction; intros.
    + destruct H1. specialize (H x H0). destruct H.
      revert H0 H1. breakAbstraction. intros. exists x. 
      auto.
    + destruct H1. specialize (H x H0). destruct H.
      revert H0 H1. breakAbstraction. intros. exists x. 
      auto.
  - rewrite Rename_forall. simpl rename_formula.
    split; breakAbstraction; intros.
    + specialize (H x H0). destruct H. revert H H1.
      breakAbstraction. intros. auto.
    + specialize (H x H0). destruct H. revert H H1.
      breakAbstraction. intros. auto.
  - simpl rename_formula. auto.
  - rewrite Rename_always. simpl rename_formula.
    split; tlaRevert; apply always_imp; rewrite IHF;
    auto; charge_tauto.
  - rewrite Rename_eventually. simpl rename_formula.
    split; tlaRevert; apply eventually_imp; rewrite IHF;
    auto; charge_tauto.
  - simpl rename_formula. split; charge_tauto.
  - simpl rename_formula. split; charge_tauto.
Qed.

Ltac Rename_rewrite :=
  repeat first [ rewrite Rename_true |
                 rewrite Rename_false |
                 rewrite Rename_comp |
                 rewrite Rename_and |
                 rewrite Rename_or |
                 rewrite Rename_impl |
                 rewrite Rename_prop |
                 rewrite Rename_exists |
                 rewrite Rename_forall |
                 rewrite Rename_always |
                 rewrite Rename_eventually ].

Lemma Proper_Rename m :
  Proper (lentails ==> lentails) (Rename m).
Proof.
  red. red. breakAbstraction. intuition.
Qed.

Existing Instance Proper_Rename.
