Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import TLA.ArithFacts.
Require Import TLA.Automation.
Require Import TLA.EnabledLemmas.
Require Import ChargeTactics.Lemmas.
Require Import Coq.Lists.ListSet.

Open Scope HP_scope.
Open Scope string_scope.

(* Convenience functions to say that all variables in a list
   have derivative 0. *)
Definition AllConstant (vars : list Var) : state->Formula :=
  fun st' => List.fold_right
               (fun x a => st' x = 0 //\\ a)
               TRUE vars.

(* Adds time derivative to an Evolution. *)
Definition mkEvolution (world : state->Formula) : state->Formula :=
  fun st' => st' "t" = --1 //\\ st' "T" = 0 //\\ world st'.

Definition World (world : state->Formula) : Formula :=
  Continuous (mkEvolution world).

Definition TDiscrete (d : R) : Formula :=
  "t"! <= d //\\ "T"! = "t"!.

Definition Discr (Prog : Formula) (d : R) : Formula :=
  Prog //\\ TDiscrete d.

Definition Next (Prog: Formula) (world : state->Formula)
           (unch:list Term) (d : R) :=
  let w := World world in
  let d := Discr Prog d in
  let steps := w \\// d
  in      steps
     \\// (Enabled d -->> lfalse)
(*     \\// (Enabled w -->> lfalse) *)
     \\// UnchangedT (("t":Term)::("T":Term)::unch)%list.

Definition PartialNext (Prog: Formula)
           (world : state->Formula)
           (unch:list Term) (d : R) :=
  let w := World world in
  let d := Discr Prog d in
  let steps := w \\// d
  in      steps
     \\// UnchangedT (("t":Term)::("T":Term)::unch)%list.

Definition sysD (Init Prog: Formula) (world : state->Formula)
           (unch : list Term) (d : R) : Formula :=
  ("t" <= d //\\ "T" = "t" //\\ Init) //\\
     [](Next Prog world unch d //\\ 0 <= "t").

Definition Partial_sysD (Init Prog: Formula)
           (world : state->Formula)
           (unch : list Term) (d : R) : Formula :=
  ("t" <= d //\\ "T" = "t" //\\ Init) //\\
     [](PartialNext Prog world unch d //\\ 0 <= "t").

Record SysRec
: Type := Sys
{ Init : Formula
; Prog : Formula
; world : Evolution
; unch : list Term
; maxTime : R }.

Definition SysD (s : SysRec)
: Formula :=
  sysD s.(Init) s.(Prog) s.(world) s.(unch) s.(maxTime).

Definition PartialSysD (s : SysRec)
: Formula :=
  Partial_sysD s.(Init) s.(Prog) s.(world) s.(unch) s.(maxTime).

Definition SysCompose (a b : SysRec) : SysRec :=
{| Init  := a.(Init) //\\ b.(Init)
 ; Prog  := a.(Prog) //\\ b.(Prog)
 ; world := fun st' => a.(world) st' //\\ b.(world) st'
 ; unch := a.(unch) ++ b.(unch)
 ; maxTime := Rmin a.(maxTime) b.(maxTime)
 |}.

Definition SysRename (m : RenameMap) (m' : state->RenameMap)
           (s : SysRec)
: SysRec :=
{| Init := Rename m s.(Init)
 ; Prog := Rename m s.(Prog)
 ; world := fun st' : state =>
          (Forall x : Var, st' x = m' st' x) //\\
          Rename m (s.(world) (fun x : Var => st' x))
 ; unch := List.map (rename_term m) s.(unch)
 ; maxTime := s.(maxTime)
 |}.

Definition SysSafe (a : SysRec) : Formula :=
  SysD a -->> PartialSysD a.

Definition set_subset {T} (a b : list T) : Prop :=
  forall x, List.In x a -> List.In x b.

Definition set_equiv {T} (a b : list T) : Prop :=
  set_subset a b /\ set_subset b a.

Instance Reflexive_set_subset {T} : Reflexive (@set_subset T).
Proof.
  red. red. tauto.
Qed.

Instance Transitive_set_subset {T} : Transitive (@set_subset T).
Proof.
  red. red. intros. eapply H0. eapply H. assumption.
Qed.

Theorem set_equiv_iff : forall {T} (a b : list T),
    set_equiv a b <-> (forall x, List.In x a <-> List.In x b).
Proof.
  intros. split.
  { destruct 1. split; eauto. }
  { split; red; firstorder. }
Qed.

Instance Reflexive_set_equiv {T} : Reflexive (@set_equiv T).
Proof.
  red. red. split; reflexivity.
Qed.

Instance Transitive_set_equiv {T} : Transitive (@set_equiv T).
Proof.
  red. intros.
  eapply set_equiv_iff.
  rewrite set_equiv_iff in H.
  rewrite set_equiv_iff in H0.
  firstorder.
Qed.

Instance Symmetric_set_equiv {T} : Symmetric (@set_equiv T).
Proof.
  red. intros. unfold set_equiv in *. tauto.
Qed.

Definition SysRec_equiv (a b : SysRec) : Prop :=
  set_equiv a.(unch) b.(unch) /\
  (a.(Init) -|- b.(Init)) /\
  (a.(Prog) -|- b.(Prog)) /\
  (forall st', (a.(world) st' -|- b.(world) st')) /\
  a.(maxTime) = b.(maxTime).

Global Instance Reflexive_SysRec_equiv
  : Reflexive SysRec_equiv.
Proof.
  red. unfold SysRec_equiv. intros.
  repeat split; reflexivity.
Qed.

Global Instance Symmetric_SysRec_equiv
  : Symmetric SysRec_equiv.
Proof.
  red. unfold SysRec_equiv. intros.
  intuition. specialize (H2 st'). rewrite H2.
  auto.
Qed.

Global Instance Transitive_SysRec_equiv
  : Transitive SysRec_equiv.
Proof.
  red. unfold SysRec_equiv. intros.
  intuition; etransitivity; eauto.
Qed.

Ltac morphism_intro :=
  repeat (intros; match goal with
                  | |- Proper (_ ==> _)%signature _ => red
                  | |- (_ ==> _)%signature _ _ => red
                  end; intros).

Lemma lequiv_limpl : forall {L} (LL : ILogicOps L) {LLO : ILogic L} (P Q R S : L),
    (P -|- R) ->
    (Q -|- S) ->
    (P -->> Q -|- R -->> S).
Proof.
  intros. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma Proper_mkEvolution_lequiv
: Proper (pointwise_relation _ lequiv ==> pointwise_relation _ lequiv) mkEvolution.
Proof.
  red. red. red. intros. unfold mkEvolution.
  rewrite H. reflexivity.
Qed.
Existing Instance Proper_mkEvolution_lequiv.

Lemma Proper_mkEvolution_lentails
: Proper (pointwise_relation _ lentails ==> pointwise_relation _ lentails) mkEvolution.
Proof.
  red. red. red. intros. unfold mkEvolution.
  rewrite H. reflexivity.
Qed.
Existing Instance Proper_mkEvolution_lentails.

Lemma Proper_World_lequiv
: Proper (pointwise_relation _ lequiv ==> lequiv) World.
Proof.
  red. red. intros. unfold World.
  rewrite H. reflexivity.
Qed.
Existing Instance Proper_World_lequiv.

Lemma Proper_World_lentails
: Proper (pointwise_relation _ lentails ==> lentails) World.
Proof.
  red. red. intros. unfold World.
  rewrite H. reflexivity.
Qed.
Existing Instance Proper_World_lentails.


Lemma Proper_Discr : Proper (lequiv ==> eq ==> lequiv) Discr.
Proof.
  red. red. red. intros. unfold Discr.
  subst. rewrite H. reflexivity.
Qed.
Existing Instance Proper_Discr.

Global Instance Proper_maxTime :
  Proper (SysRec_equiv ==> eq) maxTime.
Proof.
  unfold SysRec_equiv. morphism_intro. tauto.
Qed.

Global Instance Proper_Prog :
  Proper (SysRec_equiv ==> lequiv) Prog.
Proof.
  unfold SysRec_equiv. morphism_intro. tauto.
Qed.

Lemma UnchangedT_In : forall x xs,
    List.In x xs ->
    UnchangedT xs |-- next_term x = x.
Proof.
  induction xs.
  - inversion 1.
  - destruct 1; subst; simpl; restoreAbstraction.
    + charge_tauto.
    + rewrite <- IHxs; auto.
      charge_tauto.
Qed.

Instance Proper_UnchangedT_lentails
  : Proper (set_subset --> lentails) UnchangedT.
Proof.
  red. red. unfold Basics.flip.
  induction y.
  { intros. simpl; restoreAbstraction. eapply ltrueR. }
  { simpl; restoreAbstraction. intros.
    charge_split.
    { eapply UnchangedT_In. apply H. left. reflexivity. }
    { eapply IHy. clear - H. red in H. red.
      intros. eapply H. right. assumption. } }
Qed.

Instance Proper_UnchangedT_lequiv : Proper (set_equiv ==> lequiv) UnchangedT.
Proof.
  split; apply Proper_UnchangedT_lentails; eapply H.
Qed.

Instance Proper_set_equiv_cons {T}
  : Proper (eq ==> set_equiv ==> set_equiv) (@cons T).
Proof.
  red. red. red. split; subst.
  { red. destruct 1; subst. left; auto. right; eauto.
    eapply H0. eauto. }
  { red. destruct 1; subst. left; auto. right; eauto.
    eapply H0. eauto. }
Qed.

Lemma Proper_Next
: Proper (lequiv ==> (pointwise_relation _ lequiv) ==> set_equiv ==> eq ==> lequiv) Next.
Proof.
  red. red. red. red. red. intros.
  subst. unfold Next.
  rewrite H0; clear H0.
  rewrite H; clear H.
  rewrite H1. reflexivity.
Qed.
Existing Instance Proper_Next.

Lemma Proper_SysD : Proper (SysRec_equiv ==> lequiv) SysD.
Proof.
  red. red. intros.
  unfold SysD. red in H.
  destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ].
  rewrite H3; clear H3.
  unfold sysD.
  rewrite H0; clear H0.
  rewrite H1; clear H1.
  rewrite H; clear H.
  change (forall st' : state, world x st' -|- world y st')
    with (pointwise_relation _ lequiv (world x) (world y))
    in H2.
  rewrite H2. reflexivity.
Qed.
Existing Instance Proper_SysD.

Lemma Proper_PartialNext :
  Proper (lequiv ==> (pointwise_relation _ lequiv) ==>
                 set_equiv ==> eq ==> lequiv) PartialNext.
Proof.
  morphism_intro. unfold PartialNext.
  subst.
  rewrite H0. rewrite H. rewrite H1. reflexivity.
Qed.
Existing Instance Proper_PartialNext.


Lemma Proper_PartialSysD :
  Proper (SysRec_equiv ==> lequiv) PartialSysD.
Proof.
  red. red. intros.
  unfold PartialSysD.
  unfold Partial_sysD.
  destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ].
  rewrite H; clear H.
  rewrite H0; clear H0.
  rewrite H3; clear H3.
  rewrite H1; clear H1.
  change (forall st' : state, world x st' -|- world y st')
    with (pointwise_relation _ lequiv (world x) (world y))
    in H2.
  rewrite H2; clear H2.
  reflexivity.
Qed.
Existing Instance Proper_PartialSysD.

Lemma Proper_SysSafe :
  Proper (SysRec_equiv ==> lequiv) SysSafe.
Proof.
  red. red. intros. unfold SysSafe.
  rewrite H. reflexivity.
Qed.
Existing Instance Proper_SysSafe.

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

Definition TimeBound d : Formula :=
  0 <= "t" //\\ "t" <= "T" <= d.

Lemma mkEvolution_st_formula :
  forall w,
    (forall st : state, is_st_formula (w st)) ->
    forall st : state, is_st_formula (mkEvolution w st).
Proof.
  simpl. intros. intuition.
Qed.

Lemma PartialSys_bound_t : forall P (a : SysRec),
    (forall st, is_st_formula (a.(world) st)) ->
    P |-- PartialSysD a ->
    P |-- []TimeBound a.(maxTime).
Proof.
  intros.
  unfold SysD in *. unfold TimeBound. rewrite <- Always_and.
  tlaSplit.
  - rewrite H0. unfold PartialSysD, Partial_sysD.
    rewrite <- Always_and. tlaAssume.
  - apply discr_indX
    with (A:=PartialNext a.(Prog) a.(world)
                  a.(unch) a.(maxTime)).
    + tlaIntuition.
    + rewrite H0.
      unfold PartialSysD, Partial_sysD, PartialNext.
      rewrite <- Always_and. tlaAssume.
    + rewrite H0. solve_linear.
    + unfold PartialNext. decompose_hyps.
      * pose proof (mkEvolution_st_formula a.(world)).
        specialize (H1 H). clear H.
        eapply diff_ind with (Hyps:=TRUE);
        try solve [tlaIntuition].
        { unfold World. tlaAssume. }
        { apply H1. }
        { solve_linear. }
      * solve_linear.
      * solve_linear.
Qed.

Lemma Sys_bound_t : forall P (a : SysRec),
    (forall st, is_st_formula (a.(world) st)) ->
    forall Hsafe : P |-- SysSafe a,
    P |-- SysD a ->
    P |-- []TimeBound a.(maxTime).
Proof.
  intros.
  unfold SysSafe in *.
  assert (P |-- PartialSysD a).
  { charge_apply Hsafe. charge_tauto. }
  apply PartialSys_bound_t; auto.
Qed.

Definition InvariantUnder (unch : list Term)
           (F : Formula) : Prop :=
  F //\\ UnchangedT unch |-- next F.

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

Lemma VarsAgree_val : forall x xs s,
  List.In x xs ->
  VarsAgree xs s |-- x = (s x).
Proof.
  induction xs.
  - tlaIntuition.
  - intros. simpl in H. destruct H.
    + subst a. charge_assumption.
    + rewrite <- IHxs.
      * charge_assumption.
      * auto.
Qed.

Lemma VarsAgree_weaken : forall xs xs' s,
  all_in xs xs' ->
  VarsAgree xs' s |-- VarsAgree xs s.
Proof.
  induction xs.
  - tlaIntuition.
  - intros. simpl VarsAgree. restoreAbstraction.
    rewrite <- VarsAgree_val with (x:=a) (xs:=xs').
    + charge_split.
      * charge_tauto.
      * rewrite IHxs; try charge_tauto.
        unfold all_in in *. intuition.
    + intuition.
Qed.

Lemma VarsAgree_app : forall xs1 xs2 s,
  VarsAgree (xs1 ++ xs2) s -|-
  VarsAgree xs1 s //\\ VarsAgree xs2 s.
Proof.
  induction xs1; intros.
  - tlaIntuition. split; charge_tauto.
  - simpl VarsAgree. restoreAbstraction.
    rewrite IHxs1. split; charge_tauto.
Qed.

Lemma AVarsAgree_val : forall x xs s,
  List.In x xs ->
  AVarsAgree xs s |-- x! = (s x).
Proof.
  induction xs.
  - tlaIntuition.
  - intros. simpl in H. destruct H.
    + subst a. charge_assumption.
    + rewrite <- IHxs.
      * charge_assumption.
      * auto.
Qed.

Lemma AVarsAgree_weaken : forall xs xs' s,
  all_in xs xs' ->
  AVarsAgree xs' s |-- AVarsAgree xs s.
Proof.
  induction xs.
  - tlaIntuition.
  - intros. simpl AVarsAgree. restoreAbstraction.
    rewrite <- AVarsAgree_val with (x:=a) (xs:=xs').
    + charge_split.
      * charge_tauto.
      * rewrite IHxs; try charge_tauto.
        unfold all_in in *. intuition.
    + intuition.
Qed.

Lemma AVarsAgree_app : forall xs1 xs2 s,
  AVarsAgree (xs1 ++ xs2) s -|-
  AVarsAgree xs1 s //\\ AVarsAgree xs2 s.
Proof.
  induction xs1; intros.
  - tlaIntuition. split; charge_tauto.
  - simpl AVarsAgree. restoreAbstraction.
    rewrite IHxs1. split; charge_tauto.
Qed.

Lemma exists_entails : forall T F1 F2,
  (forall x, F1 x |-- F2 x) ->
  Exists x : T, F1 x |-- Exists x : T, F2 x.
Proof.
  tlaIntuition.  destruct H0.
  exists x. intuition.
Qed.

Lemma all_in_map : forall A B (l l':list A) (f:A->B),
  all_in l l' ->
  all_in (List.map f l) (List.map f l').
Proof.
  unfold all_in; simpl; intros.
  apply List.in_map_iff.
  apply List.in_map_iff in H0. destruct H0.
  exists x0. intuition.
Qed.

Lemma World_weaken : forall w w',
    (forall st', w' st' |-- w st') ->
    World w' |-- World w.
Proof.
  intros. eapply Proper_World_lentails. eauto.
Qed.

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

Lemma UnchangedT_weaken : forall unch' unch,
    all_in unch' unch ->
    UnchangedT unch |-- UnchangedT unch'.
Proof.
  induction unch'.
  { intros. tlaIntuition. }
  { intros. red in H.
    simpl. restoreAbstraction.
    tlaSplit.
    { apply UnchangedT_In. apply H. left. reflexivity. }
    { eapply IHunch'. red. intros. eapply H. right. assumption. } }
Qed.

Lemma Discr_weaken : forall P P' d d',
    P' |-- P ->
    (d >= d')%R ->
    Discr P' d' |-- Discr P d.
Proof.
  unfold Discr. intros. rewrite H. solve_linear.
Qed.

Theorem PartialSys_weaken :
  forall I I' P P' w w' unch unch' d d',
    I' |-- I ->
    P' |-- P ->
    (forall st', w' st' |-- w st') ->
    all_in unch unch' ->
    (d >= d')%R ->
    PartialSysD (Sys I' P' w' unch' d') |--
    PartialSysD (Sys I P w unch d).
Proof.
  do 10 intro.
  intros HI HP Hw Hunch Hd.
  unfold PartialSysD, Partial_sysD, PartialNext;
    simpl.
  restoreAbstraction.
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
    erewrite Discr_weaken at 1 by eauto.
    erewrite World_weaken at 1 by eauto.
    erewrite UnchangedT_weaken at 1 by eauto.
    decompose_hyps; charge_tauto. }
Qed.

Lemma Partial_refinement :
  forall s, PartialSysD s |-- SysD s.
Proof.
  intros. destruct s.
  unfold PartialSysD, Partial_sysD, PartialNext,
  SysD, sysD, Next; simpl; restoreAbstraction.
  charge_split.
  { charge_tauto. }
  { tlaRevert. apply forget_prem. apply always_imp.
    charge_intros. decompose_hyps.
    { charge_left. charge_left. charge_tauto. }
    { charge_left. charge_right. charge_tauto. }
    { charge_right. charge_right. charge_tauto. } }
Qed.

Theorem Sys_weaken : forall I I' P P' w w' unch unch' d d',
  forall Hsafe : |-- SysSafe (Sys I' P' w' unch' d'),
  I' |-- I ->
  P' |-- P ->
  (forall st', w' st' |-- w st') ->
  all_in unch unch' ->
  (d >= d')%R ->
  SysD (Sys I' P' w' unch' d') |--
  SysD (Sys I P w unch d).
Proof.
  intros.
  unfold SysSafe in Hsafe. apply landAdj in Hsafe.
  rewrite landtrueL in Hsafe.
  rewrite Hsafe. clear Hsafe.
  rewrite <- Partial_refinement.
  apply PartialSys_weaken; auto.
Qed.

Ltac sys_apply_with_weaken H :=
  eapply imp_trans; [ | apply H ];
  eapply Sys_weaken;
  try solve [ apply all_in_dec_ok ; reflexivity
            | apply imp_id
            | reflexivity ].

Theorem PartialSys_by_induction :
  forall P A Init Prog Inv IndInv w unch (d:R),
  is_st_formula IndInv ->
  P |-- PartialSysD (Sys Init Prog w unch d) ->
  (forall st', is_st_formula (w st')) ->
  P //\\ Init |-- IndInv ->
  P |-- [] A ->
  A //\\ IndInv //\\ TimeBound d |-- Inv ->
  InvariantUnder (("t":Term)::("T":Term)::unch)%list IndInv ->
  A //\\ IndInv //\\ TimeBound d //\\ next (TimeBound d)
    //\\ World w |-- next IndInv ->
  A //\\ IndInv //\\ TimeBound d //\\ next (TimeBound d)
          //\\ Discr Prog d |-- next IndInv ->
  P |-- [] Inv.
Proof.
  intros P A Init Prog Inv IndInv w unch d
         Hst Hsys Hstw Hinit Ha Hinv InvUnder Hw Hdiscr.
  unfold PartialSysD, Partial_sysD in *;
    simpl in *. restoreAbstraction.
  tlaAssert ([]TimeBound d).
  - change d with (maxTime {|
               Init := Init;
               Prog := Prog;
               world := w;
               unch := unch;
               maxTime := d |}).
    eapply PartialSys_bound_t;
      [ assumption | rewrite Hsys; charge_assumption ].
  - tlaIntro. tlaAssert ([]IndInv).
    + tlaAssert ([]A); [rewrite Ha; tlaAssume | tlaIntro ].
      apply discr_indX with
      (A:=PartialNext Prog w unch d //\\
               TimeBound d //\\ next (TimeBound d) //\\ A).
        { assumption. }
        { restoreAbstraction.
          rewrite Hsys.
          repeat rewrite <- Always_and.
          repeat charge_split.
          - charge_tauto.
          - charge_tauto.
          - rewrite always_st with (Q:=TimeBound d);
            (unfold TimeBound; simpl next;
            repeat rewrite <- Always_and; charge_tauto)
            || tlaIntuition.
          - rewrite always_st with (Q:=TimeBound d);
            (unfold TimeBound; simpl next;
            repeat rewrite <- Always_and; charge_tauto)
            || tlaIntuition. }
        { rewrite <- Hinit. unfold SysD.
          charge_split; [charge_tauto | ].
          rewrite Hsys. charge_tauto. }
        { unfold PartialNext. decompose_hyps.
          - rewrite <- Hw. charge_tauto.
          - rewrite <- Hdiscr. charge_tauto.
          - unfold InvariantUnder in *. rewrite <- InvUnder.
            charge_tauto. }
    + rewrite Ha. tlaRevert. tlaRevert.
      repeat rewrite <- uncurry. repeat rewrite Always_and.
      apply always_imp. charge_intros. rewrite <- Hinv.
      charge_tauto.
Qed.

Theorem Sys_by_induction :
  forall P A Init Prog Inv IndInv w unch (d:R),
  is_st_formula IndInv ->
  P |-- SysD (Sys Init Prog w unch d) ->
  (forall st', is_st_formula (w st')) ->
  forall Hsafe : P |-- SysSafe (Sys Init Prog w unch d),
  P //\\ Init |-- IndInv ->
  P |-- [] A ->
  A //\\ IndInv //\\ TimeBound d |-- Inv ->
  InvariantUnder (("t":Term)::("T":Term)::unch)%list IndInv ->
  A //\\ IndInv //\\ TimeBound d //\\ next (TimeBound d)
    //\\ World w |-- next IndInv ->
  A //\\ IndInv //\\ TimeBound d //\\ next (TimeBound d)
          //\\ Discr Prog d |-- next IndInv ->
  P |-- [] Inv.
Proof.
  intros. unfold SysSafe in *.
  eapply PartialSys_by_induction; eauto.
  charge_tauto.
Qed.

(** TODO: move this **)
Lemma charge_and_use : forall P Q C,
    C |-- P ->
    C //\\ P |-- Q ->
    C |-- P //\\ Q.
Proof.
  intros. charge_tauto.
Qed.

Theorem Enabled_and (A B : Formula) :
  Enabled (A //\\ B) |-- Enabled A //\\ Enabled B.
Proof.
  breakAbstraction. intros. split; destruct H;
  exists x; tauto.
Qed.

Theorem Enabled_imp (A B : Formula) :
  A |-- B ->
  Enabled A |-- Enabled B.
Proof.
  breakAbstraction. intros. destruct H0.
  eauto.
Qed.

Theorem PartialComposeRefine (a b : SysRec) :
  PartialSysD (SysCompose a b) |-- PartialSysD a.
Proof.
  unfold SysCompose, PartialSysD, Partial_sysD,
  PartialNext.
  simpl. restoreAbstraction.
  repeat rewrite <- Always_and.
  repeat charge_split; try charge_tauto.
  { tlaAssert (Rmin (maxTime a) (maxTime b) <= maxTime a);
    [ solve_linear; apply Rmin_l | tlaIntro ].
    - solve_linear. }
  { tlaRevert. apply forget_prem.
    charge_intros.
    rewrite Always_and.
    tlaRevert. apply always_imp.
    charge_intros. decompose_hyps.
    - apply lorR1. apply lorR1.
      rewrite World_weaken.
      + charge_tauto.
      + intros. charge_tauto.
    - apply lorR1. apply lorR2.
      unfold Discr. repeat charge_split; try charge_tauto.
      + tlaAssert (Rmin (maxTime a) (maxTime b) <= maxTime a);
        [ solve_linear; apply Rmin_l | tlaIntro ].
        solve_linear.
    - apply lorR2.
      charge_split; try charge_tauto.
      rewrite UnchangedT_weaken.
      + charge_tauto.
      + unfold all_in. intros. apply List.in_or_app.
        tauto. }
Qed.

Theorem ComposeRefine (a b : SysRec) G :
  forall Hsafe : G |-- SysSafe (SysCompose a b),
  G //\\ SysD (SysCompose a b) |-- SysD a.
Proof.
  intro.
  unfold SysSafe in Hsafe. apply landAdj in Hsafe.
  rewrite Hsafe.
  rewrite PartialComposeRefine.
  apply Partial_refinement.
Qed.

Theorem PartialComposeComm (a b : SysRec) :
  PartialSysD (SysCompose a b) |--
  PartialSysD (SysCompose b a).
Proof.
  intros.
  unfold SysCompose, PartialSysD, Partial_sysD, PartialNext.
  simpl. restoreAbstraction.
  repeat rewrite <- Always_and.
  repeat charge_split; try charge_tauto.
  { solve_linear. rewrite Rmin_comm. auto. }
  { tlaRevert. apply forget_prem.
    charge_intros.
    rewrite Always_and.
    tlaRevert. apply always_imp.
    charge_intros. decompose_hyps.
    - apply lorR1. apply lorR1.
      rewrite World_weaken.
      + charge_tauto.
      + tlaIntuition.
    - apply lorR1. apply lorR2.
      unfold Discr. repeat charge_split; try charge_tauto.
      + solve_linear. rewrite Rmin_comm. auto.
    - apply lorR2.
      charge_split; try charge_assumption.
      rewrite UnchangedT_weaken; [ charge_assumption | ].
      unfold all_in. intros. apply List.in_or_app.
      apply List.in_app_or in H. intuition. }
Qed.

Theorem ComposeComm (a b : SysRec) :
  SysD (SysCompose a b) |-- SysD (SysCompose b a).
Proof.
  intros. unfold SysCompose, SysD, sysD, Next.
  simpl. restoreAbstraction.
  repeat rewrite <- Always_and.
  repeat charge_split; try charge_tauto.
  { solve_linear. rewrite Rmin_comm. auto. }
  { tlaRevert. apply forget_prem.
    charge_intros.
    rewrite Always_and.
    tlaRevert. apply always_imp.
    charge_intros. decompose_hyps.
    - apply lorR1. apply lorR1.
      rewrite World_weaken.
      + charge_tauto.
      + tlaIntuition.
    - apply lorR1. apply lorR2.
      unfold Discr. repeat charge_split; try charge_tauto.
      + solve_linear. rewrite Rmin_comm. auto.
    - apply lorR2. apply lorR1. charge_intros. unfold Discr.
      charge_use. tlaRevert. apply forget_prem. charge_intros.
      apply Enabled_imp. rewrite Rmin_comm.
      repeat charge_split; try charge_tauto.
    - apply lorR2. apply lorR2.
      charge_split; try charge_assumption.
      rewrite UnchangedT_weaken; [ charge_assumption | ].
      unfold all_in. intros. apply List.in_or_app.
      apply List.in_app_or in H. intuition. }
Qed.

Instance Proper_app_set_equiv {T}
  : Proper (set_equiv ==> set_equiv ==> set_equiv) (@app T).
Proof.
  red. red. red. intros.
  rewrite set_equiv_iff.
  rewrite set_equiv_iff in H.
  rewrite set_equiv_iff in H0.
  intros. do 2 rewrite List.in_app_iff.
  setoid_rewrite H. setoid_rewrite H0. reflexivity.
Qed.

Theorem Proper_SysCompose
: Proper (SysRec_equiv ==> SysRec_equiv ==> SysRec_equiv) SysCompose.
Proof.
  unfold SysRec_equiv in *.
  red. red. red. intros.
  Require Import ExtLib.Tactics.
  forward_reason.
  unfold SysCompose. simpl. restoreAbstraction.
  rewrite H; clear H. rewrite H0; clear H0.
  rewrite H8; clear H8.
  rewrite H4; clear H4.
  rewrite H5; clear H5.
  rewrite H6; clear H6.
  rewrite H1; clear H1.
  rewrite H2; clear H2.
  setoid_rewrite H7; clear H7.
  setoid_rewrite H3; clear H3.
  intuition.
Qed.
Existing Instance Proper_SysCompose.

Lemma set_equiv_app_comm : forall {T} a b,
    @set_equiv T (a ++ b) (b ++ a).
Proof.
  intros. rewrite set_equiv_iff.
  intros.
  repeat rewrite List.in_app_iff.
  tauto.
Qed.

Theorem SysCompose_Comm
: forall a b, SysRec_equiv (SysCompose a b) (SysCompose b a).
Proof.
  red. intros.
  unfold SysCompose; destruct a; destruct b; simpl.
  restoreAbstraction.
  split.
  { eapply set_equiv_app_comm. }
  split.
  { rewrite landC. reflexivity. }
  split.
  { rewrite landC. reflexivity. }
  split.
  { intros; rewrite landC. reflexivity. }
  { apply Rmin_comm. }
Qed.

Theorem PartialCompose (a b : SysRec) P Q G :
  G |-- PartialSysD a -->> [] P ->
  G //\\ [] P |-- PartialSysD b -->> [] Q ->
  G |-- PartialSysD (SysCompose a b) -->> [](P //\\ Q).
Proof.
  intros Ha Hb.
  rewrite <- Always_and.
  tlaIntro. tlaAssert ([]P).
  - charge_apply Ha.
    tlaAssert G; [ charge_tauto | charge_intros ].
    rewrite PartialComposeRefine.
    charge_tauto.
  - tlaAssert (PartialSysD b).
    + rewrite PartialComposeComm;
      rewrite PartialComposeRefine.
      charge_tauto.
    + charge_tauto.
Qed.

Theorem Compose (a b : SysRec) P Q G :
  forall Hsafe : G |-- SysSafe (SysCompose a b),
  G |-- SysD a -->> [] P ->
  G //\\ [] P |-- SysD b -->> [] Q ->
  G |-- SysD (SysCompose a b) -->> [](P //\\ Q).
Proof.
  intros Hsafe Ha Hb.
  rewrite <- Always_and.
  tlaIntro. tlaAssert ([]P).
  - charge_apply Ha.
    tlaAssert G; [ charge_tauto | charge_intros ].
    rewrite ComposeRefine.
    charge_tauto. auto.
  - tlaAssert (SysD b).
    + rewrite ComposeComm; rewrite ComposeRefine.
      charge_tauto. rewrite SysCompose_Comm. assumption.
    + charge_tauto.
Qed.

Lemma always_impl_distr : forall Q R,
    [] (Q -->> R) |-- [] Q -->> [] R.
Proof.
  intros.
  charge_intro.
  rewrite Always_and.
  tlaRevert.
  eapply always_imp.
  charge_tauto.
Qed.

Ltac charge_exfalso :=
  etransitivity; [ | eapply lfalseL ].

Theorem SysSafe_rule
: forall P S
    (Hprog : P |-- [] Enabled (Discr S.(Prog) S.(maxTime))),
    P |-- SysSafe S.
Proof.
  unfold SysSafe.
  intros.
  unfold SysD, PartialSysD, sysD, Partial_sysD.
  charge_intro.
  charge_split.
  - charge_tauto.
  - rewrite <- landA. tlaRevert.
    tlaAssert (P); [ charge_assumption | rewrite Hprog at 2 ].
    repeat rewrite <- always_impl_distr.
    apply always_tauto.
    unfold Next, PartialNext.
    charge_intros. charge_split; [ | charge_tauto ].
    decompose_hyps; try charge_tauto.
    { charge_exfalso. charge_tauto. }
Qed.

Definition Inductively (P I : Formula) : Formula :=
  P //\\ [](P //\\ I -->> next P).

Lemma InductivelyCompose : forall P Q E,
    Inductively P (Q //\\ E) //\\
    Inductively Q (P //\\ E)
    |-- Inductively (P //\\ Q) E.
Proof.
  unfold Inductively.
  intros. charge_split; try charge_tauto.
  intros.
  transitivity
    ([](P //\\ (Q //\\ E) -->> next P) //\\
       [](Q //\\ (P //\\ E) -->> next Q)).
  - charge_tauto.
  - rewrite Always_and.
    tlaRevert. eapply BasicProofRules.always_imp.
    charge_tauto.
Qed.

Lemma World_Compose : forall a b,
  World (world (SysCompose a b)) |--
  World a.(world) //\\ World b.(world).
Proof.
  intros. charge_split;
  (rewrite World_weaken;
   [ charge_assumption |
     simpl; restoreAbstraction;
     intros; charge_tauto ]).
Qed.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma String_dec_ite_eq : forall T x y (P Q:T),
  x = y ->
  (if String.string_dec x y
  then P else Q) = P.
Proof.
  intros. subst. destruct (String.string_dec y y); try congruence.
Qed.

Lemma String_dec_ite_neq : forall T x y (P Q:T),
  x <> y ->
  (if String.string_dec x y
  then P else Q) = Q.
Proof.
  intros. destruct (String.string_dec x y); try congruence.
Qed.


Lemma subst_st_distr : forall m st,
  subst_state m st = (fun x => subst_state m st x).
Proof. reflexivity. Qed.

Definition NotRenamed (m : RenameMap) (x : Var) :=
  eq (m x) x.

Lemma NotRenamed_subst : forall m x,
  NotRenamed m x ->
  forall st, subst_state m st x = st x.
Proof.
  unfold NotRenamed, subst_state. intros. rewrite H.
  reflexivity.
Qed.

Lemma next_term_idempotent : forall t,
  next_term (next_term t) = next_term t.
Proof.
  induction t; simpl; auto;
  repeat match goal with
         | H : _ |- _ => rewrite H
         end; auto.
Qed.

Lemma Rename_next_term : forall a m,
    rename_term m (next_term a) = next_term (rename_term m a).
Proof.
  induction a; simpl; intros; eauto;
  repeat match goal with
         | H : _ |- _ => rewrite H
         end; auto.
  rewrite next_term_idempotent. reflexivity.
Qed.

Lemma Rename_UnchangedT : forall m unch,
  (forall x, is_st_term (m x) = true) ->
  Rename m (UnchangedT unch) -|-
  UnchangedT (List.map (rename_term m) unch).
Proof.
  intros.
  induction unch0.
  { simpl. compute. tauto. }
  { simpl. restoreAbstraction.
    rewrite Rename_and. rewrite IHunch0.
    rewrite Rename_Comp; auto.
    unfold rename_formula.
    rewrite Rename_next_term. reflexivity. }
Qed.

Hint Rewrite Rename_UnchangedT using eauto with rw_rename : rw_rename.

Theorem PartialSysRename_sound
: forall s m m'
         (H_is_st : forall st, is_st_formula (s.(world) st)),
  (forall x : Var, deriv_term (m x) = Some (fun st' : state => m' st' x)) ->
  NotRenamed m "t" ->
  NotRenamed m "T" ->
  PartialSysD (SysRename m m' s) |--
  Rename m (PartialSysD s).
Proof.
  intros. destruct s.
  unfold PartialSysD, Partial_sysD, PartialNext,
  World, Discr, TDiscrete in *.
  simpl in *.
  restoreAbstraction.
  unfold NotRenamed in *.
  Rename_rewrite.
  apply land_lentails_m.
  { simpl rename_formula.
    rewrite H1. rewrite H0. reflexivity. }
  tlaRevert. eapply always_imp. charge_intro.
  apply land_lentails_m.
  2: simpl rename_formula; rewrite H0; reflexivity.
  eapply lorL; [ charge_left | charge_right ];
  repeat match goal with
         |- context [ rename_formula ?m ?e ]
         => simpl (rename_formula m e)
         end.
  { eapply lorL; [ charge_left | charge_right ].
    { unfold mkEvolution.
      erewrite <- Rename_Continuous_deriv_term; eauto.
      eapply Proper_Continuous_entails. intro.
      Rename_rewrite. simpl rename_formula.
      charge_tauto. }
    { rewrite H0. rewrite H1. reflexivity. } }
  { rewrite H0. rewrite H1. charge_tauto. }
Qed.

Theorem SysRename_sound
: forall s m m'
         (H_is_st : forall st, is_st_formula (s.(world) st)),
  (forall x : Var, deriv_term (m x) = Some (fun st' : state => m' st' x)) ->
  NotRenamed m "t" ->
  NotRenamed m "T" ->
  (Rename m (Enabled (Discr s.(Prog) s.(maxTime))) |--
          Enabled (Rename m (Discr s.(Prog) s.(maxTime)))) ->
  SysD (SysRename m m' s) |-- Rename m (SysD s).
Proof.
  intros. destruct s.
  unfold SysD, sysD, Next,
  World, Discr, TDiscrete in *.
  simpl in *.
  restoreAbstraction.
  unfold NotRenamed in *.
  Rename_rewrite.
  apply land_lentails_m.
  { simpl rename_formula.
    rewrite H0. rewrite H1. reflexivity. }
  tlaRevert. eapply always_imp. charge_intro.
  apply land_lentails_m.
  2: simpl rename_formula; rewrite H0; reflexivity.
  eapply lorL; [ charge_left | charge_right ];
  repeat match goal with
         |- context [ rename_formula ?m ?e ]
         => simpl (rename_formula m e)
         end.
  { eapply lorL; [ charge_left | charge_right ].
    { unfold mkEvolution.
      erewrite <- Rename_Continuous_deriv_term; eauto.
      eapply Proper_Continuous_entails. intro.
      Rename_rewrite. simpl rename_formula.
      charge_tauto. }
    { rewrite H0. rewrite H1. reflexivity. } }
  { eapply lorL; [ charge_left | charge_right ].
    { rewrite H2. eapply limpl_lentails_m.
      { eapply Proper_Enabled. Rename_rewrite.
        simpl rename_formula. rewrite H0. rewrite H1.
        reflexivity. }
      { reflexivity. } }
    { rewrite H0. rewrite H1. reflexivity. } }
Qed.

Lemma SysCompose_SysRename
  : forall a b r r',
    SysRec_equiv (SysRename r r' (SysCompose a b))
                 (SysCompose (SysRename r r' a)
                             (SysRename r r' b)).
Proof.
  intros. unfold SysCompose, SysRename, SysRec_equiv; simpl.
  rewrite List.map_app.
  split; [ reflexivity | ].
  split; [ Rename_rewrite ; reflexivity | ].
  split; [ Rename_rewrite ; reflexivity | ].
  split; try reflexivity.
  intros; Rename_rewrite.
  restoreAbstraction. split; charge_tauto.
Qed.

Lemma Prog_SysRename :
  forall s m m',
    Prog (SysRename m m' s) -|- Rename m (Prog s).
Proof.
  simpl. intros. reflexivity.
Qed.

Lemma Prog_SysCompose :
  forall a b,
    Prog (SysCompose a b) -|- Prog a //\\ Prog b.
Proof.
  simpl. restoreAbstraction. intros. split; charge_tauto.
Qed.

Definition Sys_rename_formula (m : RenameMap)
           (m' : state->RenameMap) (s : SysRec)
: SysRec :=
{| Init := rename_formula m s.(Init)
 ; Prog := rename_formula m s.(Prog)
 ; world := fun st' : state =>
          (Forall x : Var, st' x = m' st' x) //\\
          rename_formula m (s.(world) (fun x : Var => st' x))
 ; unch := List.map (rename_term m) s.(unch)
 ; maxTime := s.(maxTime)
 |}.

Lemma SysRename_rename_formula_equiv :
  forall m m' s,
    st_term_renamings (Init s) ->
    st_term_renamings (Prog s) ->
    (forall x : Var, is_st_term (m x) = true) ->
    (forall st', st_term_renamings (world s st')) ->
    SysRec_equiv (SysRename m m' s)
                 (Sys_rename_formula m m' s).
Proof.
  intros. unfold SysRec_equiv.
  repeat split; try reflexivity; simpl in *;
  restoreAbstraction;
  try solve [rewrite Rename_ok; auto | intuition |
             rewrite Rename_ok; simpl; intuition |
             rewrite Rename_ok in *; intuition].
Qed.

Lemma subst_enabled_sys_discr :
  forall s m m' xs f,
    next_state_vars (Discr s.(Prog) s.(maxTime)) xs ->
    witness_function m f xs ->
    NotRenamed m "t" ->
    NotRenamed m "T" ->
    |-- Enabled (Discr s.(Prog) s.(maxTime)) ->
    |-- Enabled (Discr (SysRename m m' s).(Prog)
                       (SysRename m m' s).(maxTime)).
Proof.
  intros. simpl. restoreAbstraction. unfold Discr, TDiscrete.
  assert (Rename m ("t"! <= maxTime s) |--
          "t"! <= maxTime s)%HP as Hd.
  { breakAbstraction. intros. destruct tr as [? [? ?]].
    simpl in *. unfold subst_state in *. rewrite H1 in *.
    simpl in *. auto. }
  assert (Rename m ("T"! = "t"!) |--
          "T"! = "t"!)%HP as Hd2.
  { breakAbstraction. intros. destruct tr as [? [? ?]].
    simpl in *. unfold subst_state in *. rewrite H1 in *.
    rewrite H2 in *. simpl in *. auto. }
  { rewrite <- Hd. rewrite <- Hd2. clear Hd Hd2.
    repeat rewrite <- Rename_and.
    eapply subst_enabled_noenv; eauto. }
Qed.

Ltac sysrename_side_cond :=
  match goal with
  | [ |- forall _ : state, is_st_formula _ ]
    => tlaIntuition; abstract is_st_term_list
  | [ |- NotRenamed _ _ ]
    => reflexivity
  | [ |- _ ] => apply deriv_term_list; reflexivity
  end.

Ltac discharge_PartialSys_rename_formula :=
  match goal with
    |- { _ : _ & _ |-- Rename (to_RenameMap ?m)
                              (PartialSysD ?s) }
    => exists (Sys_rename_formula
                 (to_RenameMap m)
                 (deriv_term_RenameList m) s)
  end;
  rewrite <- SysRename_rename_formula_equiv
    by rw_side_condition;
  apply PartialSysRename_sound;
  sysrename_side_cond.

Ltac discharge_Sys_rename_formula :=
  match goal with
    |- { _ : _ & _ |-- Rename (to_RenameMap ?m) (SysD ?s) }
    => exists (Sys_rename_formula
                 (to_RenameMap m)
                 (deriv_term_RenameList m) s)
  end;
  rewrite <- SysRename_rename_formula_equiv
    by rw_side_condition;
  apply SysRename_sound;
  match goal with
  | [ |- context [ Enabled _ ] ] =>  idtac
  | [ |- forall _ : state, is_st_formula _ ]
    => tlaIntuition; abstract is_st_term_list
  | [ |- NotRenamed _ _ ]
    => reflexivity
  | [ |- _ ] => apply deriv_term_list; reflexivity
  end.

Ltac discharge_sysrec_equiv_rename :=
  match goal with
  | |- {_ : _ &
            SysRec_equiv
              (SysRename (to_RenameMap ?m) _ ?s) _ } =>
    exists
      (Sys_rename_formula (to_RenameMap m)
                          (deriv_term_RenameList m) s)
  end;
  apply SysRename_rename_formula_equiv;
  rw_side_condition.

Ltac rewrite_rename_pf s :=
  let H := fresh in
  pose proof (projT2 s) as H;
    cbv beta in H; rewrite <- H; clear H.
