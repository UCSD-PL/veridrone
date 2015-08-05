Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Automation.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.R_sqrt.
Require Import Coq.Reals.Ratan.
Require Import Coq.Lists.List.

(* Various proof rules for TLA in general *)

Open Scope HP_scope.

Ltac morphism_intro :=
  repeat (intros; match goal with
                  | |- Proper (_ ==> _)%signature _ => red
                  | |- (_ ==> _)%signature _ _ => red
                  end; intros).


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
Lemma impl_iff : forall (P Q R S : Prop),
    (P <-> Q) ->
    (P -> (R <-> S)) ->
    ((P -> R) <-> (Q -> S)).
Proof.
  intros. tauto.
Qed.
Lemma and_iff : forall (P Q R S : Prop),
    (P <-> Q) ->
    (P -> (R <-> S)) ->
    ((P /\ R) <-> (Q /\ S)).
Proof.
  intros. tauto.
Qed.
Lemma or_iff : Proper (iff ==> iff ==> iff) or.
Proof.
  morphism_intro. tauto.
Qed.

Lemma lequiv_to_iff
: forall (P Q : Formula),
    (P -|- Q) <-> (forall st, eval_formula P st <-> eval_formula Q st).
Proof.
  split.
  { intros. destruct H; split; auto. }
  { intro. split; intro; apply H. }
Qed.

Global Instance Proper_eval_formula
: Proper (lequiv ==> Stream.stream_eq eq ==> iff) eval_formula.
Proof.
  red. red.
  induction x;
    morphism_intro;
    try match goal with
        | H : _ -|- _ |- _ => rewrite lequiv_to_iff in H ; rewrite <- H ; clear H
        end; simpl; try tauto.
  { destruct H0. destruct H0.
    rewrite H. rewrite H0. reflexivity. }
  { eapply and_iff; intros; first [ eapply IHx1 | eapply IHx2 ]; eauto. }
  { eapply or_iff; intros; first [ eapply IHx1 | eapply IHx2 ]; eauto. }
  { eapply impl_iff; intros; first [ eapply IHx1 | eapply IHx2 ]; eauto. }
  { eapply exists_iff; intros.
    eapply H; eauto. }
  { eapply forall_iff; intros.
    eapply H; eauto. }
  { eapply exists_iff; intros.
    destruct H0. rewrite H.
    reflexivity. }
  { eapply forall_iff; intros.
    eapply IHx. reflexivity.
    eapply Stream.Proper_nth_suf_stream_eq; eauto. }
  { eapply exists_iff; intros.
    eapply IHx. reflexivity.
    eapply Stream.Proper_nth_suf_stream_eq; eauto. }
  { destruct H0. destruct H0.
    rewrite H. rewrite H0. reflexivity. }
  { eapply IHx. reflexivity.
    eapply Stream.Proper_stream_map; eauto.
    reflexivity. }
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
    | SqrtT t => SqrtT (next_term t)
    | ArctanT t => ArctanT (next_term t)
    | ExpT t => ExpT (next_term t)
    | MaxT t1 t2 => MaxT (next_term t1) (next_term t2)
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
    | SqrtT t => is_st_term t
    | ArctanT t => is_st_term t
    | ExpT t => is_st_term t
    | MaxT t1 t2 => andb (is_st_term t1)
                         (is_st_term t2)
  end.

(* Prop expressing that the Formula has no
   !. This cannot be a bool because of
   Forall and Exists. *)
Fixpoint is_st_formula (F:Formula) : Prop :=
  match F with
    | TRUE => True
    | FALSE => True
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
  Stream.hd tr1 = Stream.hd tr2 ->
  eval_formula F tr2.
Proof.
  induction F; intros; simpl in *; auto;
  try tauto; try discriminate.
  - unfold eval_comp in *. simpl in *.
    rewrite st_term_hd
    with (t:=t) (s3:=Stream.hd (Stream.tl tr1));
      intuition.
    rewrite st_term_hd
    with (t:=t0) (s3:=Stream.hd (Stream.tl tr1));
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
    rewrite <- next_term_tl with (s1:=Stream.hd tr) (t:=t).
    rewrite <- next_term_tl with (s1:=Stream.hd tr) (t:=t0).
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

Lemma next_st_formula_entails :
  forall A B,
    is_st_formula A ->
    is_st_formula B ->
    A |-- B ->
    next A |-- next B.
Proof.
  breakAbstraction. intros.
  apply next_formula_tl; auto.
  apply H1. apply next_formula_tl; auto.
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

Lemma lor_right2 : forall {P Q : Formula},
    Q |-- P \\// Q.
Proof. intros. charge_tauto. Qed.

Lemma trans_it : forall A B C D,
    C |-- A ->
    B |-- D ->
    A -->> B |-- C -->> D.
Proof.
  intros. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma land_distr :
  forall A B C,
    (A //\\ B) //\\ (C //\\ B) -|- (A //\\ C) //\\ B.
Proof. split; charge_tauto. Qed.

Lemma lor_intro1 :
  forall A B,
    A |-- A \\// B.
Proof. intros; charge_tauto. Qed.

Lemma lor_intro2 :
  forall A B,
    B |-- A \\// B.
Proof. intros; charge_tauto. Qed.

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

Lemma Exists_with_st : forall G P (t : Term),
    (forall x : R, G |-- t = x -->> P x) ->
    G |-- Exists x : R, P x.
Proof.
  breakAbstraction.
  intros.
  specialize (H _ tr H0 eq_refl).
  eexists. eauto.
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

Lemma ex_state_flow_any : forall (P : (state * flow) -> Prop),
  (forall f, exists st, P (st, f)) ->
  exists stf, P stf.
Proof.
  intros. specialize (H (fun _ _ => R0)).
  destruct H. eauto.
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

(*
Definition find_term (m : RenameMap) (x : Var) : option Term :=
  option_map
    (@snd _ Term)
    (List.find (fun p =>
                  if String.string_dec x (fst p)
                  then true else false) m).*)

(* Some renaming functions and proof rules. *)
Fixpoint rename_term (m : RenameMap) (t:Term) :=
  match t with
    | NatT n => NatT n
    | RealT r => RealT r
    | VarNowT x => m x
    | VarNextT x => next_term (m x)
    | PlusT t1 t2 => PlusT (rename_term m t1)
                           (rename_term m t2)
    | MinusT t1 t2 => MinusT (rename_term m t1)
                             (rename_term m t2)
    | MultT t1 t2 => MultT (rename_term m t1)
                           (rename_term m t2)
    | InvT t => InvT (rename_term m t)
    | CosT t => CosT (rename_term m t)
    | SinT t => SinT (rename_term m t)
    | SqrtT t => SqrtT (rename_term m t)
    | ArctanT t => ArctanT (rename_term m t)
    | ExpT t => ExpT (rename_term m t)
    | MaxT t1 t2 => MaxT (rename_term m t1)
                         (rename_term m t2)
  end.

Definition RenameMap_compose (m m' : RenameMap) : RenameMap :=
  fun x => rename_term m (m' x).

Arguments RenameMap_compose _ _ _ /.

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
    | Enabled F => Rename m (Enabled F)
    | Always F => Always (rename_formula m F)
    | Eventually F => Eventually (rename_formula m F)
    | Embed P => Rename m (Embed P)
    | Rename s P => rename_formula (RenameMap_compose m s) P
  end.

Lemma Rename_term_ok : forall m t st1 st2,
  (forall x, is_st_term (m x) = true) ->
  eval_term (rename_term m t) st1 st2 =
  eval_term t (subst_state m st1) (subst_state m st2).
Proof.
  induction t; simpl; intros; auto;
  try solve [rewrite IHt1; auto; rewrite IHt2; auto |
             rewrite IHt; auto ].
  - unfold subst_state.
    apply st_term_hd; auto.
  - unfold subst_state.
    apply next_term_tl; auto.
Qed.

Lemma Rename_True : forall m,
  Rename m TRUE -|- TRUE.
Proof.
  intros; split; breakAbstraction; auto.
Qed.

Lemma Rename_False : forall m,
  Rename m FALSE -|- FALSE.
Proof.
  intros; split; breakAbstraction; auto.
Qed.

Lemma Rename_Comp : forall m t1 t2 op,
  (forall x, is_st_term (m x) = true) ->
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

Lemma Rename_PropF : forall m P,
  Rename m (PropF P) -|- PropF P.
Proof.
  intros; split; breakAbstraction; auto.
Qed.

Lemma Rename_Exists : forall T m f,
  Rename m (Syntax.Exists T f) -|-
  Syntax.Exists T (fun x => Rename m (f x)).
Proof.
  intros; split; breakAbstraction; auto.
Qed.

Lemma Rename_Forall : forall T m f,
  Rename m (Syntax.Forall T f) -|-
  Syntax.Forall T (fun x => Rename m (f x)).
Proof.
  intros; split; breakAbstraction; auto.
Qed.

Lemma Rename_Always : forall m F,
  Rename m (Always F) -|-
  Always (Rename m F).
Proof.
  intros; split; breakAbstraction; intros.
  { specialize (H n).
    rewrite Stream.stream_map_nth_suf in H; auto. }
  { rewrite Stream.stream_map_nth_suf; auto. }
Qed.

Lemma Rename_Eventually : forall m F,
  Rename m (Eventually F) -|-
  Eventually (Rename m F).
Proof.
  intros; split; breakAbstraction; intros.
  { destruct H as [n H].
    rewrite Stream.stream_map_nth_suf in H; eauto. }
  { destruct H as [n H].
    exists n. rewrite Stream.stream_map_nth_suf; auto. }
Qed.

Fixpoint to_RenameMap (m : list (Var * Term)) : RenameMap :=
  match m with
  | nil => fun x => x
  | (y, t) :: m =>
    fun x => if String.string_dec x y
             then t else to_RenameMap m x
  end.

(*
Definition VarRenameMap (m : list (Var * Var)) : RenameMap :=
  List.map (fun p => (fst p, VarNowT (snd p))) m.

Lemma VarRenameMap_derivable : forall f m,
    (forall x,
        Ranalysis1.derivable (fun t => f t x)) ->
    forall x,
      Ranalysis1.derivable
        (fun t => subst_state (VarRenameMap m) (f t) x).
Proof.
  intros.
  induction m.
  - simpl. auto.
  - simpl. destruct a. simpl.
    destruct (String.string_dec x v).
    + subst. apply H.
    + auto.
Qed.

Require Coq.Reals.Ranalysis4.

Lemma subst_VarRenameMap_derive_distr :
  forall m f z pf1 pf2,
    subst_state (VarRenameMap m)
          (fun x =>
             Ranalysis1.derive (fun t : R => f t x) (pf1 x) z) =
    fun x =>
      Ranalysis1.derive (fun t : R =>
                           subst_state (VarRenameMap m) (f t) x)
                        (pf2 x)
                        z.
Proof.
  intros. apply functional_extensionality.
  intros. generalize (pf2 x). clear pf2.
  induction m; intros.
  - simpl. apply Ranalysis4.pr_nu_var. auto.
  - destruct a. simpl in *.
    destruct (String.string_dec x v).
    + subst. apply Ranalysis4.pr_nu_var.
      auto.
    + erewrite IHm. auto.
Qed.*)

Lemma Rename_Enabled
: forall P m,
    Enabled (Rename m P) |-- Rename m (Enabled P).
Proof.
  Opaque Stream.stream_map.
  breakAbstraction. intros.
  destruct H.
  simpl.
  destruct tr. simpl in H.
  eapply Proper_eval_formula in H. 2: reflexivity.
  2: symmetry. 2: eapply Stream.stream_map_cons. 2: eauto.
  eauto.
Qed.

Lemma Rename_Rename :
  forall P m m',
    (forall x, is_st_term (m x) = true) ->
    Rename m (Rename m' P) -|-
    Rename (RenameMap_compose m m') P.
Proof.
  intros. apply lequiv_to_iff. intros.
  simpl.
  rewrite Stream.stream_map_compose
    by eauto with typeclass_instances.
  unfold RenameMap_compose. apply Proper_eval_formula.
  { reflexivity. }
  { eapply Stream.Proper_stream_map.
    2: instantiate (1:=eq); reflexivity.
    morphism_intro. subst. unfold subst_state.
    apply FunctionalExtensionality.functional_extensionality.
    intros. rewrite Rename_term_ok by auto. reflexivity. }
Qed.

Fixpoint st_term_renamings (F : Formula) : Prop :=
  match F with
    | TRUE | FALSE | Comp _ _ _ | PropF _ | Embed _ => True
    | And F1 F2 | Or F1 F2 | Imp F1 F2 =>
        st_term_renamings F1 /\ st_term_renamings F2
    | Syntax.Exists _ f | Syntax.Forall _ f =>
        forall x, st_term_renamings (f x)
    | Enabled F | Always F | Eventually F => st_term_renamings F
    | Rename s P =>
       (forall x, is_st_term (s x) = true) /\ st_term_renamings P
  end.

Lemma rename_term_st_term : forall t m,
  (forall x, is_st_term (m x) = true) ->
  is_st_term t = true ->
  is_st_term (rename_term m t) = true.
Proof.
  induction t; auto;
  try solve
      [ simpl; intros; apply andb_prop in H0; destruct H0;
        rewrite IHt1; auto; rewrite IHt2; auto |
        simpl; auto |
        simpl; discriminate ].
Qed.

Lemma Rename_ok : forall F m
  (Hst : st_term_renamings F),
  (forall x, is_st_term (m x) = true) ->
  rename_formula m F -|- Rename m F.
Proof.
  induction F; intros.
  - apply Rename_True with (m:=m).
  - apply Rename_False with (m:=m).
  - rewrite Rename_Comp; auto.
  - rewrite Rename_and. simpl rename_formula.
    simpl in Hst. destruct Hst. restoreAbstraction.
    rewrite IHF1; auto. rewrite IHF2; auto.
  - rewrite Rename_or. simpl rename_formula.
    simpl in Hst. destruct Hst. restoreAbstraction.
    rewrite IHF1; auto. rewrite IHF2; auto.
  - rewrite Rename_impl. simpl rename_formula.
    simpl in Hst. destruct Hst. restoreAbstraction.
    rewrite IHF1; auto. rewrite IHF2; auto.
  - rewrite Rename_PropF. simpl rename_formula.
    split; charge_tauto.
  - rewrite Rename_Exists. simpl rename_formula.
    split; breakAbstraction; intros.
    + destruct H1. specialize (H x _ (Hst x) H0). destruct H.
      revert H0 H1. breakAbstraction. intros. exists x.
      auto.
    + destruct H1. specialize (H x _ (Hst x) H0). destruct H.
      revert H0 H1. breakAbstraction. intros. exists x.
      auto.
  - rewrite Rename_Forall. simpl rename_formula.
    split; breakAbstraction; intros.
    + specialize (H x _ (Hst x) H0). destruct H. revert H H1.
      breakAbstraction. intros. auto.
    + specialize (H x _ (Hst x) H0). destruct H. revert H H1.
      breakAbstraction. intros. auto.
  - simpl rename_formula. auto.
  - rewrite Rename_Always. simpl rename_formula.
    split; tlaRevert; apply always_imp; rewrite IHF;
    auto; charge_tauto.
  - rewrite Rename_Eventually. simpl rename_formula.
    split; tlaRevert; apply eventually_imp; rewrite IHF;
    auto; charge_tauto.
  - simpl rename_formula. split; charge_tauto.
  - simpl rename_formula. rewrite Rename_Rename by auto.
    rewrite <- IHF.
    + reflexivity.
    + simpl in Hst. tauto.
    + unfold RenameMap_compose. simpl in Hst.
      destruct Hst. intros. apply rename_term_st_term; auto.
Qed.

Lemma is_st_term_to_RenameMap : forall ls (x : Var),
    forallb (fun x => is_st_term (snd x)) ls = true ->
    is_st_term (to_RenameMap ls x) = true.
Proof.
  induction ls.
  { simpl in *. reflexivity. }
  { simpl in *. intros.
    eapply Bool.andb_true_iff in H.
    destruct H.
    destruct a; simpl in *.
    destruct (String.string_dec x v); subst; auto. }
Qed.

Ltac rw_side_condition :=
  repeat first [ split | intros ];
  try solve [ apply is_st_term_to_RenameMap ; reflexivity ].

Hint Rewrite Rename_True Rename_False Rename_Comp
     Rename_and Rename_or Rename_impl Rename_PropF
     Rename_Exists Rename_Forall
     Rename_Always Rename_Eventually
     Rename_Enabled using eauto with rw_rename : rw_rename.

Ltac Rename_rewrite :=
  autorewrite with rw_rename.

Definition RenameListC (l : list (String.string * String.string)) :
  list (Var * Term) :=
  List.map (fun p => (fst p, VarNowT (snd p))) l.

Global Instance Proper_Rename :
  Proper (eq ==> lentails ==> lentails) Rename.
Proof.
  morphism_intro.
  breakAbstraction. subst. intuition.
Qed.

Global Instance Proper_Enabled :
  Proper (lequiv ==> lequiv) Enabled.
Proof.
  red. red. unfold lequiv, lentails. simpl.
  unfold tlaEntails. simpl. intros. split.
  { intros. destruct H0. exists x0. intuition. }
  { intros. destruct H0. exists x0. intuition. }
Qed.

Global Instance Proper_Always :
  Proper (lequiv ==> lequiv) Always.
Proof.
  red. red. unfold lequiv, lentails. simpl.
  intuition. restoreAbstraction. tlaRevert. apply always_imp.
  charge_tauto.
  restoreAbstraction. tlaRevert.
  apply always_imp. charge_tauto.
Qed.

Global Instance Proper_Enabled_lentails : Proper (lentails ==> lentails) Enabled.
Proof.
  morphism_intro.
  breakAbstraction.
  intros.
  destruct H0. exists x0. eauto.
Qed.

Require Import Coq.Classes.Morphisms.
Global Instance Proper_Rename_lequiv :
  Proper (eq ==> lequiv ==> lequiv) Rename.
Proof.
  morphism_intro. split.
  - rewrite H0; subst; reflexivity.
  - rewrite <- H0; subst; reflexivity.
Qed.

Ltac rename_hyp m H :=
  apply (Proper_Rename (to_RenameMap m)
                       (to_RenameMap m))
  in H; [ | reflexivity ].
