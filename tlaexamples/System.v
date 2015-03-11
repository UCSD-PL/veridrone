Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Classes.RelationClasses.
Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import TLA.ArithFacts.
Import LibNotations.

Open Scope HP_scope.
Open Scope string_scope.

Definition World (dvars : list Var)
           (world : list DiffEq) : Formula :=
  Continuous (("t"'::=--1)::world ++
                          (List.map
                             (fun x => x ' ::= 0) dvars))%list.

Definition Discr (cvars : list Var)
           (Prog : Formula) (d : R) : Formula :=
  Prog //\\ "t"! <= d //\\ Unchanged cvars.

Definition Next (dvars cvars : list Var)
           (Prog: Formula) (world : list DiffEq)
           (WConstraint : Formula) (d : R) :=
       ((World dvars world //\\ WConstraint) \\//
         Discr cvars Prog d)
  \\// Unchanged ("t"::dvars++cvars)%list.

Definition Sys (dvars cvars : list Var)
           (Init Prog: Formula) (world : list DiffEq)
           (WConstraint : Formula) (d : R) : Formula :=
  ("t" <= d //\\ Init) //\\
     [](Next dvars cvars Prog world WConstraint d //\\ 0 <= "t").

Ltac tlaRevert := first [ apply landAdj | apply lrevert ].

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

Lemma Always_now : forall P I,
  P |-- []I ->
  P |-- I.
Proof.
  breakAbstraction.
  intros P I H tr HP.
  apply (H tr HP 0).
Qed.

Ltac decompose_hyps :=
  repeat rewrite land_lor_distr_R;
  repeat rewrite land_lor_distr_L;
  repeat apply lorL.

Definition TimeBound d : Formula := 0 <= "t" <= d.

Lemma Sys_bound_t : forall P dvars cvars Init Prog w WC d,
    P |-- Sys dvars cvars Init Prog w WC d ->
    P |-- []TimeBound d.
Proof.
  intros. unfold Sys.
  rewrite <- Always_and with (P:=0 <= "t") (Q:="t" <= d). tlaSplit.
  - rewrite H. unfold Sys. rewrite <- Always_and. tlaAssume.
  - apply discr_indX with (A:=Next dvars cvars Prog w WC d).
    + tlaIntuition.
    + rewrite H. unfold Sys. rewrite <- Always_and. tlaAssume.
    + rewrite H. unfold Sys. tlaAssume.
    + unfold Next. decompose_hyps.
      * eapply diff_ind with (Hyps:=TRUE);
        try solve [tlaIntuition].
        { unfold World. tlaAssume. }
        { solve_linear. }
      * solve_linear.
      * solve_linear.
Qed.

Definition InvariantUnder (vars : list Var) (F : Formula) : Prop :=
  F //\\ Unchanged vars |-- next F.

Definition all_in {T} (l1 l2 : list T) :=
  forall x, List.In x l1 -> List.In x l2.

Theorem all_in_dec_ok : forall (l1 l2 : list Var),
  List.forallb
    (fun x => if List.in_dec String.string_dec x l2
              then true else false) l1 = true ->
  all_in l1 l2.
Proof.
  red. intros.
  rewrite List.forallb_forall in H.
  apply H in H0.
  destruct (List.in_dec String.string_dec x l2);
    auto; discriminate.
Qed.

Instance Reflexive_all_in {T} : Reflexive (@all_in T).
Proof. red; red; tauto. Qed.

Instance Transitive_all_in {T} : Transitive (@all_in T).
Proof. unfold all_in; red; intros. eauto. Qed.

Lemma World_weaken : forall dvars dvars' w w',
    all_in dvars dvars' ->
    all_in w w' ->
    World dvars' w' |-- World dvars w.
Proof.
Admitted.

Lemma Unchanged_In : forall ls l,
    List.In l ls ->
    Unchanged ls |-- l! = l.
Proof.
  induction ls; simpl.
  { inversion 1. }
  { intros. destruct H; restoreAbstraction.
    { subst. charge_tauto. }
    { rewrite IHls; eauto. charge_tauto. } }
Qed.

Lemma Unchanged_weaken : forall vars' vars,
    all_in vars' vars ->
    Unchanged vars |-- Unchanged vars'.
Proof.
  induction vars'.
  { intros. tlaIntuition. }
  { intros. red in H.
    simpl. restoreAbstraction.
    tlaSplit.
    { apply Unchanged_In. apply H. left. reflexivity. }
    { eapply IHvars'. red. intros. eapply H. right. assumption. } }
Qed.

Lemma Discr_weaken : forall cvars cvars' P P' d d',
    all_in cvars cvars' ->
    P' |-- P ->
    (d >= d')%R ->
    Discr cvars' P' d' |-- Discr cvars P d.
Proof.
  unfold Discr. intros.
  rewrite Unchanged_weaken; eauto. solve_linear.
Qed.

Theorem Sys_weaken : forall dvars dvars' cvars cvars'
                            I I' P P' w w' WC WC' d d',
  all_in dvars dvars' ->
  all_in cvars cvars' ->
  I' |-- I ->
  P' |-- P ->
  all_in w w' ->
  WC' |-- WC ->
  (d >= d')%R ->
  (Sys dvars' cvars' I' P' w' WC' d' |-- Sys dvars cvars I P w WC d).
Proof.
  do 14 intro.
  intros Hdvars Hcvars HI HP Hw HWC Hd.
  unfold Sys.
  apply lrevert.
  rewrite HI; clear HI.
  tlaIntro.
  repeat tlaSplit; try tlaAssume.
  { do 2 apply landL1. clear - Hd. solve_linear. }
  { tlaRevert.
    apply always_imp. tlaIntro.
    repeat tlaSplit; try tlaAssume.
    rewrite landC. tlaRevert. apply forget_prem.
    tlaIntro. unfold Next.
    erewrite World_weaken by eauto.
    rewrite HWC.
    erewrite Discr_weaken by eauto.
    erewrite Unchanged_weaken. tlaAssume.
    revert Hdvars Hcvars.
    clear.
    unfold all_in. intros. specialize (Hdvars x).
    specialize (Hcvars x).
    revert H. simpl. repeat rewrite List.in_app_iff. intuition. }
Qed.

Ltac sys_apply_with_weaken H :=
  eapply imp_trans; [ | apply H ];
  eapply Sys_weaken;
  try solve [ apply all_in_dec_ok ; reflexivity
            | apply imp_id
            | reflexivity ].

Theorem sys_by_induction :
  forall P A dvars cvars Init Prog Inv IndInv w WC (d:R),
  is_st_formula IndInv ->
  P |-- Sys dvars cvars Init Prog w WC d ->
  P //\\ Init |-- IndInv ->
  P |-- [] A ->
  A //\\ IndInv //\\ TimeBound d |-- Inv ->
  InvariantUnder ("t"::dvars ++ cvars)%list IndInv ->
  A //\\ IndInv //\\ World dvars w //\\ WC |-- next IndInv ->
  A //\\ IndInv //\\ TimeBound d //\\ next (TimeBound d)
          //\\ Discr cvars Prog d |-- next IndInv ->
  P |-- [] Inv.
Proof.
  intros P A dvars cvars Init Prog Inv IndInv w WC d
         Hst Hsys Hinit Ha Hinv InvUnder Hw Hdiscr.
  tlaAssert ([]TimeBound d).
  - eapply Sys_bound_t. rewrite Hsys. tlaAssume.
  - tlaIntro. tlaAssert ([]IndInv).
    + tlaAssert ([]A); [rewrite Ha; tlaAssume | tlaIntro ].
      tlaAssert (Sys dvars cvars Init Prog w WC d);
        [ rewrite Hsys; tlaAssume | tlaIntro ].
      apply discr_indX with
      (A:=Next dvars cvars Prog w WC d //\\
               TimeBound d //\\ next (TimeBound d) //\\ A).
        { assumption. }
        { unfold Sys. repeat rewrite <- Always_and. repeat tlaSplit.
          - tlaAssume.
          - tlaAssume.
          - rewrite always_st with (Q:=TimeBound d);
            (rewrite <- Always_and; tlaAssume) || tlaIntuition.
          - tlaAssume. }
        { rewrite <- Hinit. unfold Sys. charge_tauto. }
        { unfold Next. decompose_hyps.
          - rewrite <- Hw. charge_tauto.
          - rewrite <- Hdiscr. charge_tauto.
          - unfold InvariantUnder in *. rewrite <- InvUnder.
            charge_tauto. }
    + rewrite Ha. tlaRevert. tlaRevert.
      repeat rewrite <- uncurry. repeat rewrite Always_and.
      apply always_imp. charge_intros. rewrite <- Hinv.
      charge_tauto.
Qed.

Section ComposeDiscrete.

  Variable Is : Formula.
  Variable Ic : Formula.
  Variable dvars : list Var.
  Variable cvars : list Var.
  Variable w : list DiffEq.
  Variable WC : Formula.
  Variable d : R.
  Variable S : Formula.
  Variable C : Formula.
  Variable P : Formula.
  Variable E : Formula.

  Theorem compose_discrete :
    |-- Sys dvars cvars Is S w WC d -->> []E ->
    |-- Sys dvars cvars Ic (C //\\ E) w WC d -->> []P ->
    |-- Sys dvars cvars (Is //\\ Ic) (S //\\ C) w WC d -->> [](P //\\ E).
(*  Proof.
    Opaque World Discr.
    simpl. intros Hs Hc tr [ [HIs HIc] HN] n.
    split.
    - apply Hc. intuition.
      + pose proof (HN n0). intuition.
        right. Transparent Discr. revert H.
        unfold Discr. simpl. intuition.
(*        apply Hs. intuition.
        * specialize (HN n1). intuition.
          right. simpl in *. intuition.
        * apply HN.
      + apply HN.
    - apply Hs. intuition.
      + specialize (HN n0). intuition.
        right. simpl in *. intuition.
      + apply HN.
  Qed.
*)*)
Admitted.

End ComposeDiscrete.

Section ComposeWorld.

  Variable Iw : Formula.
  Variable Id : Formula.
  Variable dvars : list Var.
  Variable cvars : list Var.
  Variable w : list DiffEq.
  Variable WC : Formula.
  Variable d : R.
  Variable D : Formula.
  Variable P : Formula.
  Variable E : Formula.

  Theorem compose_world :
    |-- (Iw //\\ [](World dvars w //\\ WC)) -->> []E ->
    InvariantUnder cvars E ->
    |-- Sys dvars cvars Id (D //\\ E) w WC d -->> []P ->
    |-- Sys dvars cvars (Iw //\\ Id) D w WC d -->> [](P //\\ E).
  Admitted.

End ComposeWorld.
