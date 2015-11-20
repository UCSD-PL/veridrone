Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Logic.Syntax.
Require Import Logic.Semantics.
Require Import Logic.Automation.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.R_sqrt.
Require Import Coq.Reals.Ratan.
Require Import Coq.Lists.List.

(* Various proof rules for our logic in general *)

Local Open Scope HP_scope.

Ltac morphism_intro :=
  repeat (intros; match goal with
                  | |- Proper (_ ==> _)%signature _ => red
                  | |- (_ ==> _)%signature _ _ => red
                  end; intros).

(* TODO: All of these should be available in ExtLib *)
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

Existing Class is_st_formula.

Hint Extern 1 (is_st_formula _) => solve [ compute ; tauto ] : typeclass_instances.

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

Theorem is_st_formula_b_ok
: forall F, is_st_formula_b F = true -> is_st_formula F.
Proof.
  induction F; simpl; intros; try congruence; auto;
  try apply Bool.andb_true_iff in H; tauto.
Qed.

Hint Extern 0 (is_st_formula ?X) => solve [ eapply (is_st_formula_b_ok X) ; reflexivity ] : typeclass_instances.

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

Lemma next_And :
  forall A B,
    next (A //\\ B) -|- next A //\\ next B.
Proof. reflexivity. Qed.

Lemma next_Rename :
  forall A sigma,
    next (Rename sigma A) -|- Rename sigma (next A).
Proof. reflexivity. Qed.

Lemma land_limpl :
  forall P Q R,
    P -->> (Q //\\ R) -|- (P -->> Q) //\\ (P -->> R).
Proof.
  split.
  { charge_split; charge_intros.
    { eapply Lemmas.lcut.
      { charge_use; charge_assumption. }
      { charge_tauto. } }
    { eapply Lemmas.lcut.
      { charge_use; charge_assumption. }
      { charge_tauto. } } }
  { charge_tauto. }
Qed.

Lemma always_tauto : forall G P, |-- P -> G |-- [] P.
Proof. tlaIntuition. Qed.

Lemma always_tauto_inv :
  forall P,
    |--[]P ->
    |-- P.
Proof.
  breakAbstraction. intros.
  specialize (H tr I 0). auto.
Qed.

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

Lemma Always_imp : forall C F1 F2,
  (|-- F1 -->> F2) ->
  (C |-- []F1 -->> []F2).
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

Lemma Enabled_action' : forall P Q,
    is_st_formula Q ->
    (forall st,
        eval_formula Q (Stream.forever st) ->
        exists st',
          eval_formula P (Stream.Cons st (Stream.forever st'))) ->
    Q |-- Enabled P.
Proof.
  breakAbstraction; intros.
  specialize (H0 (Stream.hd tr)).
  eapply st_formula_hd in H1;
    [ apply H0 in H1 | assumption | reflexivity ]. 
  destruct H1. exists (Stream.forever x). auto.
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

Global Instance Proper_Enabled :
  Proper (lequiv ==> lequiv) Enabled.
Proof.
  red. red. unfold lequiv, lentails. simpl.
  unfold tlaEntails. simpl. intros. split.
  { intros. destruct H0. exists x0. intuition. }
  { intros. destruct H0. exists x0. intuition. }
Qed.

Global Instance Proper_Always_lequiv
: Proper (lequiv ==> lequiv) Always.
Proof.
  red. red. unfold lequiv, lentails. simpl.
  intuition. restoreAbstraction. tlaRevert. apply Always_imp.
  charge_tauto.
  restoreAbstraction. tlaRevert.
  apply Always_imp. charge_tauto.
Qed.

Global Instance Proper_Always_entails
: Proper (lentails ==> lentails) Always.
Proof.
 red. red. intros.
 tlaRevert.
 eapply Always_imp. charge_tauto.
Qed.

Global Instance Proper_Enabled_lentails
: Proper (lentails ==> lentails) Enabled.
Proof.
  morphism_intro.
  breakAbstraction.
  intros.
  destruct H0. exists x0. eauto.
Qed.

Global Instance Proper_PropF_lequiv
: Proper (iff ==> lequiv) PropF.
Proof.
  morphism_intro. compute. tauto.
Qed.

Global Instance Proper_PropF_lentails
: Proper (Basics.impl ==> lentails) PropF.
Proof.
  morphism_intro. compute. tauto.
Qed.

Lemma PropF_and : forall P Q, PropF (P /\ Q) -|- PropF P //\\ PropF Q.
Proof. compute. tauto. Qed.
