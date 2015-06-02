Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import TLA.ArithFacts.
Require Import TLA.Automation.
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
  fun st' => st' "t" = --1 //\\  world st'.

Definition World (world : state->Formula) : Formula :=
  Continuous (mkEvolution world).

Definition Discr (Prog : Formula) (d : R) : Formula :=
  Prog //\\ "t"! <= d.

Definition Next (Prog: Formula) (world : state->Formula)
           (unch:list Term) (d : R) :=
  let w := World world in
  let d := Discr Prog d in
  let steps := w \\// d
  in      steps
     \\// (Enabled d -->> lfalse)
(*     \\// (Enabled w -->> lfalse) *)
     \\// UnchangedT (("t":Term)::unch)%list.

Definition Next_or_stuck (Prog: Formula) (world : state->Formula)
           (unch:list Term) (d : R) :=
  let w := World world in
  let d := Discr Prog d in
  let steps := w \\// d
  in      steps
     \\// UnchangedT (("t":Term)::unch)%list.

Definition sysD (Init Prog: Formula) (world : state->Formula)
           (unch : list Term) (d : R) : Formula :=
  ("t" <= d //\\ Init) //\\
     [](Next Prog world unch d //\\ 0 <= "t").

Definition sysD_or_stuck (Init Prog: Formula) (world : state->Formula)
           (unch : list Term) (d : R) : Formula :=
  ("t" <= d //\\ Init) //\\
     [](Next_or_stuck Prog world unch d //\\ 0 <= "t").

Record SysRec
: Type := Sys
{ Init : Formula
; Prog : Formula
; world : state->Formula
; unch : list Term
; maxTime : R }.

Definition SysD (s : SysRec)
: Formula :=
  sysD s.(Init) s.(Prog) s.(world) s.(unch) s.(maxTime).

Definition SysD_or_stuck (s : SysRec)
: Formula :=
  sysD_or_stuck s.(Init) s.(Prog) s.(world) s.(unch) s.(maxTime).

Definition SysCompose (a b : SysRec) : SysRec :=
{| Init  := a.(Init) //\\ b.(Init)
 ; Prog  := a.(Prog) //\\ b.(Prog)
 ; world := fun st' => a.(world) st' //\\ b.(world) st'
 ; unch := a.(unch) ++ b.(unch)
 ; maxTime := Rmin a.(maxTime) b.(maxTime)
 |}.

Definition SysRename (m : list (Var * Term)) (s : SysRec)
  : SysRec :=
  {| Init := Rename m s.(Init)
   ; Prog := Rename m s.(Prog)
   ; world := fun st' => Rename m (s.(world) (subst_state m st'))
   ; unch := List.map (rename_term m) s.(unch)
   ; maxTime := s.(maxTime)
  |}.

Definition SysSafe (a : SysRec) : Formula :=
  SysD a -->> SysD_or_stuck a.

Definition SysRec_equiv (a b : SysRec) : Prop :=
  a.(unch) = b.(unch) /\
  (a.(Init) -|- b.(Init)) /\
  (a.(Prog) -|- b.(Prog)) /\
  (forall st', (a.(world) st' -|- b.(world) st')) /\
  a.(maxTime) = b.(maxTime).

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

Lemma Proper_mkEvolution : Proper (pointwise_relation _ lequiv ==> pointwise_relation _ lequiv) mkEvolution.
Proof.
  red. red. red. intros. unfold mkEvolution.
  rewrite H. reflexivity.
Qed.
Existing Instance Proper_mkEvolution.

Lemma Proper_World : Proper (pointwise_relation _ lequiv ==> lequiv) World.
Proof.
  red. red. intros. unfold World.
  rewrite H. reflexivity.
Qed.
Existing Instance Proper_World.

Lemma Proper_Discr : Proper (lequiv ==> eq ==> lequiv) Discr.
Proof.
  red. red. red. intros. unfold Discr.
  subst. rewrite H. reflexivity.
Qed.
Existing Instance Proper_Discr.

Lemma Proper_Next : Proper (lequiv ==> (pointwise_relation _ lequiv) ==> eq ==> eq ==> lequiv) Next.
Proof.
  red. red. red. red. red. intros.
  subst. unfold Next.
  rewrite H0.
  rewrite H. reflexivity.
Qed.
Existing Instance Proper_Next.


Lemma Proper_SysD : Proper (SysRec_equiv ==> lequiv) SysD.
Proof.
  red. red. intros.
  unfold SysD. red in H.
  destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ].
  rewrite H3. clear H3.
  rewrite H; clear H.
  unfold sysD.
  rewrite H0; clear H0.
  rewrite H1.
  change (forall st' : state, world x st' -|- world y st')
    with (pointwise_relation _ lequiv (world x) (world y)) in H2.
  rewrite H2. reflexivity.
Qed.
Existing Instance Proper_SysD.

Lemma Proper_Next_or_stuck : Proper (lequiv ==> (pointwise_relation _ lequiv) ==> eq ==> eq ==> lequiv) Next_or_stuck.
Proof.
  morphism_intro. unfold Next_or_stuck.
  subst.
  rewrite H0. rewrite H. reflexivity.
Qed.
Existing Instance Proper_Next_or_stuck.


Lemma Proper_SysD_or_stuck : Proper (SysRec_equiv ==> lequiv) SysD_or_stuck.
Proof.
  red. red. intros.
  unfold SysD_or_stuck.
  unfold sysD_or_stuck.
  destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ].
  rewrite H; clear H.
  rewrite H0; clear H0.
  rewrite H3; clear H3.
  rewrite H1; clear H1.
  change (forall st' : state, world x st' -|- world y st')
    with (pointwise_relation _ lequiv (world x) (world y)) in H2.
  rewrite H2; clear H2.
  reflexivity.
Qed.
Existing Instance Proper_SysD_or_stuck.

Lemma Proper_SysSafe :
  Proper (SysRec_equiv ==> lequiv) SysSafe.
Proof.
  red. red. intros. unfold SysSafe.
  rewrite H. reflexivity.
Qed.
Existing Instance Proper_SysSafe.

(*Ltac tlaRevert := first [ apply landAdj | apply lrevert ]. *)

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

Require Import ChargeTactics.Lemmas.

Ltac decompose_hyps :=
  repeat rewrite land_lor_distr_R;
  repeat rewrite land_lor_distr_L;
  repeat apply lorL.

Definition TimeBound d : Formula := 0 <= "t" <= d.

Lemma mkEvolution_st_formula :
  forall w,
    (forall st : state, is_st_formula (w st)) ->
    forall st : state, is_st_formula (mkEvolution w st).
Proof.
  simpl. intros. intuition.
Qed.

Lemma Sys_bound_t : forall P (a : SysRec),
    (forall st, is_st_formula (a.(world) st)) ->
    forall Hsafe : P |-- SysSafe a,
    P |-- SysD a ->
    P |-- []TimeBound a.(maxTime).
Proof.
  intros.
  unfold SysSafe in *.
  assert (P |-- SysD_or_stuck a).
  { charge_apply Hsafe. charge_split. reflexivity. assumption. }
  clear - H1 H. rename H1 into H0.
  unfold SysD in *.
  rewrite <- Always_and with (P:=0 <= "t") (Q:="t" <= a.(maxTime)).
  tlaSplit.
  - rewrite H0. unfold SysD_or_stuck, sysD_or_stuck, sysD.
    rewrite <- Always_and. tlaAssume.
  - apply discr_indX
    with (A:=Next_or_stuck a.(Prog) a.(world)
                  a.(unch) a.(maxTime)).
    + tlaIntuition.
    + rewrite H0.
      unfold SysD_or_stuck,sysD_or_stuck,Next_or_stuck,sysD,Next.
      rewrite <- Always_and. tlaAssume.
    + rewrite H0. unfold sysD. tlaAssume.
    + unfold Next_or_stuck. decompose_hyps.
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
  intros.
  unfold World.
  repeat (apply exists_entails; intros).
  repeat charge_split; try solve [tlaAssume].
  breakAbstraction; unfold is_solution; intros;
    intuition.
  destruct tr as [[st1 f] ?]. simpl in *.
  destruct H0 as [r [Hr [Hstart [Hend Hsol]]]].
  exists r. intuition.
    match goal with
    | [ H : context[solves_diffeqs] |- _ ]
        => let pf := fresh "pf" in
           let Hcont := fresh "Hcont" in
           destruct H as [pf Hcont]; exists pf
    end.
    unfold solves_diffeqs in *; intros.
    specialize (Hcont z H0).
    unfold mkEvolution in *.
    simpl in *.
    decompose [and] Hcont.
    split.
    { intuition. }
    { specialize (H (fun x1 : Var =>
             Ranalysis1.derive (fun t : R => f t x1) (pf x1) z) (Stream.forever (f z, fun _ _ => R0))).
      intuition.
    }
    Qed.
(*
    erewrite Hcont; eauto.
    simpl in *; intuition. right.
    apply List.in_or_app.
    match goal with
    | [ H : _ |- _ ]
      => apply List.in_app_or in H
    end; intuition. right.
    apply List.in_map_iff.
    match goal with
    | [ H : _ |- _ ]
      => let x := fresh "x" in
         apply List.in_map_iff in H;
           destruct H as [x ?]; exists x
    end; intuition.
  - fold VarsAgree. simpl VarsAgree.
    repeat rewrite List.map_app with (f:=get_var).
    repeat rewrite VarsAgree_app. charge_split.
    + erewrite VarsAgree_weaken with (xs:=List.map get_var w).
      * tlaIntuition.
      * apply all_in_map; auto.
    + erewrite VarsAgree_weaken with
      (xs:=List.map get_var
                    (List.map (fun x1 : Var => x1 '  ::= 0)
                              dvars0))
        (xs':=List.map get_var
                       (List.map (fun x1 : Var => x1 '  ::= 0)
                                 dvars')).
      * tlaIntuition.
      * repeat apply all_in_map; auto.
  - fold AVarsAgree. simpl AVarsAgree.
    repeat rewrite List.map_app with (f:=get_var).
    repeat rewrite AVarsAgree_app. charge_split.
    + erewrite AVarsAgree_weaken with (xs:=List.map get_var w).
      * tlaIntuition.
      * apply all_in_map; auto.
    + erewrite AVarsAgree_weaken with
      (xs:=List.map get_var
                    (List.map (fun x1 : Var => x1 '  ::= 0)
                              dvars0))
        (xs':=List.map get_var
                       (List.map (fun x1 : Var => x1 '  ::= 0)
                                 dvars')).
      * tlaIntuition.
      * repeat apply all_in_map; auto.
*)

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

Lemma UnchangedT_In : forall ls l,
    List.In l ls ->
    UnchangedT ls |-- next_term l = l.
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
  do 11 intro.
  intros HI HP Hw Hunch Hd.
  unfold SysSafe in Hsafe. apply landAdj in Hsafe.
  rewrite landtrueL in Hsafe.
  rewrite Hsafe.
  unfold SysD, sysD, Init, Next, SysD_or_stuck,
  sysD_or_stuck, Next_or_stuck;
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

Ltac sys_apply_with_weaken H :=
  eapply imp_trans; [ | apply H ];
  eapply Sys_weaken;
  try solve [ apply all_in_dec_ok ; reflexivity
            | apply imp_id
            | reflexivity ].

Theorem Sys_by_induction :
  forall P A Init Prog Inv IndInv w unch (d:R),
  is_st_formula IndInv ->
  P |-- SysD (Sys Init Prog w unch d) ->
  (forall st', is_st_formula (w st')) ->
  forall Hsafe : P |-- SysSafe (Sys Init Prog w unch d),
  P //\\ Init |-- IndInv ->
  P |-- [] A ->
  A //\\ IndInv //\\ TimeBound d |-- Inv ->
  InvariantUnder (("t":Term)::unch)%list IndInv ->
  A //\\ IndInv //\\ TimeBound d //\\ next (TimeBound d)
    //\\ World w |-- next IndInv ->
  A //\\ IndInv //\\ TimeBound d //\\ next (TimeBound d)
          //\\ Discr Prog d |-- next IndInv ->
  P |-- [] Inv.
Proof.
  intros P A Init Prog Inv IndInv w unch d
         Hst Hsys Hstw Hsafe Hinit Ha Hinv InvUnder Hw Hdiscr.
  tlaAssert ([]TimeBound d).
  - change d with (maxTime {|
               Init := Init;
               Prog := Prog;
               world := w;
               unch := unch;
               maxTime := d |}).
    eapply Sys_bound_t;
      [ assumption | assumption | rewrite Hsys; tlaAssume ].
  - tlaIntro. tlaAssert ([]IndInv).
    + tlaAssert ([]A); [rewrite Ha; tlaAssume | tlaIntro ].
      tlaAssert (SysD_or_stuck (Sys Init Prog w unch d));
        [ | tlaIntro ].
      { unfold SysSafe in Hsafe. charge_apply Hsafe.
        charge_split; try charge_tauto. }
      apply discr_indX with
      (A:=Next_or_stuck Prog w unch d //\\
               TimeBound d //\\ next (TimeBound d) //\\ A).
        { assumption. }
        { unfold SysD_or_stuck, sysD_or_stuck, Next_or_stuck. simpl.
          restoreAbstraction.
          repeat rewrite <- Always_and.
          repeat tlaSplit.
          - tlaAssume.
          - tlaAssume.
          - rewrite always_st with (Q:=TimeBound d);
            (unfold TimeBound; simpl next;
            repeat rewrite <- Always_and; charge_tauto)
            || tlaIntuition.
          - rewrite always_st with (Q:=TimeBound d);
            (unfold TimeBound; simpl next;
            repeat rewrite <- Always_and; charge_tauto)
            || tlaIntuition.
          - tlaAssume. }
        { rewrite <- Hinit. unfold SysD. charge_tauto. }
        { unfold Next_or_stuck. decompose_hyps.
          - rewrite <- Hw. charge_tauto.
          - rewrite <- Hdiscr. charge_tauto.
          - unfold InvariantUnder in *. rewrite <- InvUnder.
            charge_tauto. }
    + rewrite Ha. tlaRevert. tlaRevert.
      repeat rewrite <- uncurry. repeat rewrite Always_and.
      apply always_imp. charge_intros. rewrite <- Hinv.
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

(*
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
        |-- SysD (Sys dvars cvars Is S w WC d) -->> []E ->
    []E |-- SysD (Sys dvars cvars Ic C w WC d) -->> []P ->
    |-- SysD (Sys dvars cvars (Is //\\ Ic) (S //\\ C) w WC d) -->>
        [](P //\\ E).
  Proof.
    intros.
    rewrite <- Always_and.
    tlaIntro. rewrite (landC ([]P) ([]E)). apply charge_and_use.
    { charge_apply H.
      eapply Sys_weaken; try reflexivity.
      charge_tauto. charge_tauto. }
    { charge_apply H0. charge_split; try charge_tauto.
      erewrite Sys_weaken;
        try first [ charge_assumption |
                    reflexivity |
                    charge_tauto ]. }
  Qed.

End ComposeDiscrete.
*)

(*
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
        |-- SysD (Sys dvars cvars Iw ltrue w WC d) -->> []E ->
    []E |-- SysD (Sys dvars cvars Id D w ltrue d) -->> []P ->
    |-- SysD (Sys dvars cvars (Iw //\\ Id) D w WC d) -->>
        [](P //\\ E).
  Proof.
    intros.
    rewrite <- Always_and.
    tlaIntro. rewrite (landC ([]P) ([]E)). apply charge_and_use.
    { charge_apply H.
      eapply Sys_weaken; try reflexivity.
      charge_tauto. charge_tauto. }
    { charge_apply H0. charge_split; try charge_tauto.
      erewrite Sys_weaken;
        try first [ charge_assumption |
                    reflexivity |
                    charge_tauto ]. }
  Qed.

End ComposeWorld.
*)

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

Theorem ComposeRefine (a b : SysRec) :
  forall Hsafe : |-- SysSafe (SysCompose a b),
  SysD (SysCompose a b) |-- SysD a.
Proof.
  intro.
  unfold SysSafe in Hsafe. apply landAdj in Hsafe.
  rewrite landtrueL in Hsafe. rewrite Hsafe.
  unfold SysCompose, SysD_or_stuck, SysD, sysD_or_stuck,
  sysD, Next_or_stuck, Next.
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
    - apply lorR2. apply lorR2.
      charge_split; try charge_tauto.
      rewrite UnchangedT_weaken.
      + charge_tauto.
      + unfold all_in. intros. apply List.in_or_app.
        tauto. }
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

Axiom Proper_SysCompose : Proper (SysRec_equiv ==> SysRec_equiv ==> SysRec_equiv) SysCompose.
Existing Instance Proper_SysCompose.

Axiom SysCompose_Comm : forall a b, SysRec_equiv (SysCompose a b) (SysCompose b a).

Theorem Compose (a b : SysRec) P Q G :
  forall Hsafe : |-- SysSafe (SysCompose a b),
  G |-- SysD a -->> [] P ->
  G //\\ [] P |-- SysD b -->> [] Q ->
  G |-- SysD (SysCompose a b) -->> [](P //\\ Q).
Proof.
  intros Hsafe Ha Hb.
  rewrite <- Always_and.
  tlaIntro. tlaAssert ([]P).
  - charge_apply Ha. rewrite ComposeRefine.
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
    (Hprog : P |-- [] Enabled (Discr S.(Prog) S.(maxTime)))
(*    (Hcont : P |-- [] (Enabled (World S.(dvars) S.(world) //\\ S.(WConstraint)))) *),
    P |-- SysSafe S.
Proof.
  unfold SysSafe.
  intros.
  unfold SysD, SysD_or_stuck, sysD, sysD_or_stuck.
  charge_intro.
  charge_split.
  - charge_tauto.
  - rewrite <- landA. tlaRevert.
    tlaAssert (P); [ charge_assumption | rewrite Hprog at 2 ].
(*    tlaAssert (P); [ charge_assumption | rewrite Hcont at 2 ]. *)
    repeat rewrite <- always_impl_distr.
    apply always_tauto.
    unfold Next, Next_or_stuck.
    charge_intros. charge_split; [ | charge_tauto ].
    decompose_hyps; try charge_tauto.
    { charge_exfalso. charge_tauto. }
Qed.

(*
Lemma VarRenameMap_rw : forall m st x,
  subst (VarRenameMap m) st x =
  st
    match List.find (fun p => if String.string_dec (fst p) x
                          then true else false) m with
    | Some (_,y) => y
    | None => x
    end.
Proof.
  induction m.
  - simpl. intuition.
  - simpl. intros. destruct a. simpl.
    destruct (String.string_dec x v).
    + subst; destruct (String.string_dec v v); congruence.
    + destruct (String.string_dec v x); try congruence.
      apply IHm.
Qed.
*)


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

(*
Definition FlipMap {A B} (l : list (A * B)) :=
  List.map (fun p => (snd p, fst p)) l.

Lemma VarRenameMap_inverse :
  forall m st,
    subst (VarRenameMap m)
          (subst
             (VarRenameMap
                (FlipMap m)) 
              st) = st.
Proof.
  induction m.
  - simpl; auto.
  - simpl. intros.
    apply functional_extensionality.
    intros. destruct a. simpl.
    destruct (String.string_dec x v).
    + subst; destruct (String.string_dec v0 v0);
      congruence.
    +*)

(*
Lemma VarRenameMap_deriv_inverse :
  forall m f z pf,
    subst (VarRenameMap m)
          (fun x =>
             Ranalysis1.derive
               (fun t =>
                  subst
                    (VarRenameMap (FlipMap m))
                    (f t) x)
               (VarRenameMap_derivable
                  f  (FlipMap m) pf x)
               z) =
   (fun x => Ranalysis1.derive
               (fun t => f t x) (pf x) z).
Proof.
  intros. erewrite subst_VarRenameMap_derive_distr.
  apply functional_extensionality. intros.
  apply Ranalysis4.pr_nu_var.
  apply functional_extensionality. intros.
  rewrite VarRenameMap_inverse. auto.
Grab Existential Variables.
intros. specialize (pf x).
match goal with
| [ _ : Ranalysis1.derivable ?f1 |- Ranalysis1.derivable ?f2 ] =>
  assert (f1 = f2)
end.
{ apply functional_extensionality. intros.
  rewrite VarRenameMap_inverse. auto. }
{ rewrite <- H. auto. }
Qed.

Lemma FlipMap_inv :
  forall {A B} (m : list (A * B)), m = (FlipMap (FlipMap m)).
Proof.
  induction m.
  - auto.
  - simpl. destruct a. simpl.
    rewrite <- IHm. auto.
Qed.
*)


(*
Lemma Rename_continuous : forall m m' w,
  (forall v e f pf1, List.In (v,e) m -> exists e' pf2,
                 List.In (v,e') m' /\
                 Ranalysis1.derive
                   (fun t => eval_term e (f t) (f t)) pf1 =
                 fun t => eval_term (e' (derive_stateF f pf2 t))
                                     (f t) (f t)) ->
  Rename m (Continuous w) -|-
  Continuous
  (fun st' =>
     Rename m (w (subst
       (List.map (fun p => (fst p, (snd p) st')) m') st'))).
Proof.
  Opaque Stream.stream_map.
  split; breakAbstraction; intros.
  - destruct H as [r [f [Hr [Hsol [Hstart Hend]]]]].
    exists r. exists f.
    intuition.
    + clear Hstart Hend. unfold is_solution, solves_diffeqs in *.
      destruct Hsol as [pf Hsol]. exists pf.
      intros. specialize (Hsol z H).

Lemma Rename_continuous : forall m w,
  Rename m (Continuous w) -|-
  Continuous (fun st' => Rename m (w st')).
Proof.
  Opaque Stream.stream_map.
  split; breakAbstraction; intros.
  - destruct H as [r [f [Hr [Hsol [Hstart Hend]]]]].
    exists r. exists (fun t => subst m (f t)).
    intuition.
    + clear Hstart Hend. unfold is_solution, solves_diffeqs in *.
SearchAbout Ranalysis1.derivable.

w := fun st' => st' x = 5
f x := fun t => 5*t
x -> y
fun st' => Rename (x -> y) (st' x = 5)

      destruct Hsol as [pf Hsol].
      unfold Ranalysis1.derivable, Ranalysis1.derivable_pt in *.
*)

Definition NotRenamed (m : RenameMap) (x : Var) :=
  forall y t, List.In (y, t) m -> x <> y.

Lemma NotRenamed_find_term : forall m x,
  NotRenamed m x -> find_term m x = None.
Proof.
  induction m.
  - unfold NotRenamed; simpl; intros; auto.
  - unfold NotRenamed; simpl; intros.
    destruct a. unfold find_term. simpl.
    destruct (String.string_dec x v).
    * specialize (H v t). intuition congruence.
    * rewrite <- (IHm x); auto.
      unfold NotRenamed; intros. eapply H; eauto.
Qed.

Lemma find_term_NotRenamed : forall m x,
  find_term m x = None -> NotRenamed m x.
Proof.
  induction m.
  - unfold NotRenamed; simpl; intros; auto.
  - unfold NotRenamed; simpl; intros.
    destruct a. destruct H0.
    * inversion H0. subst.
      intro. subst. unfold find_term in *.
      simpl in *; destruct (String.string_dec y y);
      simpl in *; auto; discriminate.
    * unfold NotRenamed in *. specialize (IHm x).
      eapply IHm; eauto.
      unfold find_term in *. simpl in *.
      destruct (String.string_dec x v); simpl in *;
      auto; discriminate.
Qed.

Lemma NotRenamed_subst : forall m x,
  NotRenamed m x ->
  forall st, subst_state m st x = st x.
Proof.
  induction m.
  - auto.
  - unfold NotRenamed. simpl. intros. destruct a.
    destruct (String.string_dec x v).
    + specialize (H v t). intuition congruence.
    + rewrite IHm; auto. unfold NotRenamed. intros.
      eapply H; eauto.
Qed.

Lemma VarRenameMap_is_st_term : forall m,
  List.Forall (fun p : Var * Term => (is_st_term (snd p) = true)%type)
              (VarRenameMap m).
Proof.
  induction m; simpl; auto.
Qed.

Lemma next_term_idempotent : forall t,
  next_term (next_term t) = next_term t.
Proof.
  induction t; simpl; auto;
  repeat match goal with
         | H : _ |- _ => rewrite H
         end; auto.
Qed.

Lemma Rename_next_term : forall a m, rename_term m (next_term a) = next_term (rename_term m a).
Proof.
  induction a; simpl; intros; eauto;
  repeat match goal with
         | H : _ |- _ => rewrite H
         end; auto.
  - destruct (find_term m v); reflexivity.
  - destruct (find_term m v). rewrite next_term_idempotent. reflexivity.
    reflexivity.
Qed.

Lemma Rename_UnchangedT : forall m unch,
    (List.Forall (fun p : Var * Term => (is_st_term (snd p) = true)%type) m) ->
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

(** TODO: Move this **)
Lemma Rename_Enabled'
: forall P m,
    Rename m (Enabled P) |-- Enabled (Rename m P).
Proof.
  Opaque Stream.stream_map.
  breakAbstraction. intros.
  destruct H.
  simpl.
  destruct tr. simpl in H.
  simpl.
  Transparent Stream.stream_map. simpl in H.
  Opaque Stream.stream_map.
  (* only if m is invertible *)
Abort.

Theorem SysRename_sound
: forall s m'
         (H_is_st : forall st, is_st_formula (s.(world) st)),
  let m := VarRenameMap m' in
  NotRenamed m "t" ->
  (Rename m (Enabled (Discr s.(Prog) s.(maxTime))) |--
          Enabled (Rename m (Discr s.(Prog) s.(maxTime)))) ->
  SysD (SysRename m s) |-- Rename m (SysD s).
Proof.
  intros. destruct s. unfold SysD, sysD, Next, World, Discr in *. simpl in *.
  restoreAbstraction. Rename_rewrite; auto; try apply VarRenameMap_is_st_term.
  apply land_lentails_m.
  { simpl rename_formula. repeat rewrite NotRenamed_find_term; auto.
    reflexivity. }
  tlaRevert. eapply always_imp. charge_intro.
  apply land_lentails_m.
  2: simpl rename_formula; repeat rewrite NotRenamed_find_term; auto; reflexivity.
  rewrite H0.
  rewrite Rename_UnchangedT by eapply VarRenameMap_is_st_term.
  repeat match goal with
         |- context [ rename_formula ?m ?e ]
         => simpl (rename_formula m e)
         end.
  repeat rewrite NotRenamed_find_term; auto.
  subst m.
  rewrite <- Rename_Continuous.
  apply lor_lentails_m; try reflexivity.
  { apply lor_lentails_m; try reflexivity.
    eapply Proper_Continuous_entails.
    red. intros.
    unfold mkEvolution.
    Rename_rewrite.
    apply land_lentails_m; auto.
    simpl rename_formula.
    rewrite NotRenamed_subst by eauto. reflexivity.
    eauto using VarRenameMap_is_st_term. }
  { apply lor_lentails_m; try reflexivity.
    apply limpl_lentails_m; try reflexivity.
    red. rewrite Rename_and.
    rewrite Rename_Comp by eauto using VarRenameMap_is_st_term.
    simpl rename_formula.
    rewrite NotRenamed_find_term by eauto. reflexivity. }
  { unfold mkEvolution. simpl. intros.
    split; auto. }
Qed.
