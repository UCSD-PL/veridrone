Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.ListSet.
Require Import ChargeTactics.Lemmas.
Require Import ChargeTactics.Indexed.
Require Import ExtLib.Tactics.
Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import TLA.ArithFacts.
Require Import TLA.Automation.
Require Import TLA.EnabledLemmas.
Require Import TLA.Inductively.

Local Open Scope HP_scope.
Local Open Scope string_scope.

(** TODO: Move this **)
Lemma land_dup : forall A : Formula, A -|- A //\\ A.
Proof. intros; split; charge_tauto. Qed.


(* Adds time derivative to an Evolution.
 * - the global time is stored in [t]
 * - the time until the next discrete step is stored in [T]
 *)
Definition mkEvolution (world : Evolution) : Evolution :=
  fun st' => st' "T" = --1 //\\ world st'.

Definition World (world : Evolution) : Formula :=
  Continuous (mkEvolution world) //\\ 0 < "T" //\\ 0 <= "T"!.

Definition TimeBound (d : R) : Formula :=
  0 <= "T" <= d.

Definition Discr (Prog : ActionFormula) (d : R) : ActionFormula :=
  Prog //\\ "T" = 0 //\\ 0 <= "T"! <= d.

Definition Sys (P : ActionFormula) (w : Evolution) (d : R) : ActionFormula :=
  "T" <= d //\\ (Discr P d \\// World w).

Definition System (P : ActionFormula) (w : Evolution) (d : R) : ActionFormula :=
  Sys P w d \\// (Enabled (Sys P w d) -->> lfalse).

Definition TimedPreserves (delta : R) (P : StateFormula) (A : ActionFormula) : Formula :=
  Preserves (P //\\ 0 <= "T" <= delta) A.

Definition SysNeverStuck (delta : R) (I : StateFormula) (A : ActionFormula) : Formula :=
  0 <= "T" <= delta //\\ I -->> Enabled A.

Global Instance Proper_mkEvolution_lentails
: Proper (lentails ==> lentails) mkEvolution.
Proof.
  unfold mkEvolution. morphism_intro.
  rewrite Evolution_lentails_lentails in H.
  apply Evolution_lentails_lentails.
  simpl in *. restoreAbstraction.
  intros. rewrite H. reflexivity.
Qed.

Global Instance Proper_mkEvolution_lequiv
: Proper (lequiv ==> lequiv) mkEvolution.
Proof.
  unfold mkEvolution. morphism_intro.
  eapply Evolution_lequiv_lequiv.
  intro.
  eapply Evolution_lequiv_lequiv with (x:=x0) in H.
  rewrite H. reflexivity.
Qed.

Global Instance Proper_World_lequiv
: Proper (lequiv ==> lequiv) World.
Proof.
  unfold World; morphism_intro.
  rewrite H. reflexivity.
Qed.

Global Instance Proper_World_lentails
: Proper (lentails ==> lentails) World.
Proof.
  unfold World; morphism_intro.
  rewrite H. reflexivity.
Qed.

Global Instance Proper_Discr
: Proper (lequiv ==> eq ==> lequiv) Discr.
Proof.
  morphism_intro; unfold Discr.
  subst. rewrite H. reflexivity.
Qed.

Global Instance Proper_Sys_lequiv
: Proper (lequiv ==> lequiv ==> eq ==> lequiv) Sys.
Proof.
  unfold Sys, Discr, World. morphism_intro.
  subst. rewrite H; clear H. rewrite H0; clear H0. reflexivity.
Qed.

Global Instance Proper_Sys_lentails
: Proper (lentails ==> lentails ==> eq ==> lentails) Sys.
Proof.
  unfold Sys, Discr, World. morphism_intro.
  subst. rewrite H; clear H. rewrite H0; clear H0. reflexivity.
Qed.

Global Instance Proper_System_lequiv
: Proper (lequiv ==> lequiv ==> eq ==> lequiv) System.
Proof.
  unfold System, Discr, World. morphism_intro.
  subst. rewrite H; clear H. rewrite H0; clear H0. reflexivity.
Qed.

Theorem Preserves_Sys
: forall P Prog IndInv (w : Evolution) (d:R),
  (forall st', is_st_formula (w st')) ->
  P //\\ IndInv //\\ 0 <= "T"! <= "T" //\\ "T" <= d (* This could be "T"! < "T" *)
    //\\ World w |-- next IndInv ->
  P //\\ IndInv //\\ "T" = 0 //\\ 0 <= "T"! <= d
    //\\ Discr Prog d |-- next IndInv ->
  P |-- Preserves IndInv (Sys Prog w d).
Proof.
  intros P Prog IndInv world delta.
  intros Hst_world Hworld Hdiscr.
  unfold Preserves.
  charge_revert.
  charge_intros. unfold Sys.
  decompose_hyps.
  { rewrite <- Hdiscr. unfold Discr.
    charge_tauto. }
  { rewrite <- Hworld.
    simpl. restoreAbstraction.
    unfold World; repeat charge_split; try charge_tauto.
    charge_assert (Exists T : R, "T" = T //\\ ("T") ! <= T).
    { apply Exists_with_st with (t:="T"). intros.
      charge_intros. charge_split; [ charge_assumption | ].
      eapply diff_ind with (G:="T" <= x) (Hyps:=ltrue).
      - compute; tauto.
      - compute; tauto.
      - charge_assumption.
      - unfold mkEvolution.
        intros. simpl. split; auto.
      - simpl next. restoreAbstraction; charge_tauto.
      - solve_linear.
      - charge_tauto.
      - solve_linear. }
    { charge_intros.
      charge_fwd.
      solve_linear. } }
Qed.

Definition SafeAndReactive d (I : StateFormula) (S : ActionFormula)
  : Formula :=
  TimedPreserves d I S //\\ SysNeverStuck d I S.

Lemma SysSystem_TimedPreserves
: forall G I P w d,
  G |-- TimedPreserves d I (Sys P w d) ->
  G |-- SysNeverStuck  d I (Sys P w d) ->
  G |-- TimedPreserves d I (System P w d).
Proof.
  intros. unfold SysNeverStuck, TimedPreserves, Preserves in *.
  rewrite (land_dup G).
  rewrite H at 1.
  rewrite H0.
  charge_revert.
  unfold System.
  charge_intros.
  decompose_hyps.
  - charge_tauto.
  - charge_exfalso. charge_tauto.
Qed.

Theorem SafeAndReactive_TimedPreserves
: forall G I D w d,
  G |-- SafeAndReactive d I (Sys D w d) ->
  G |-- TimedPreserves d I (System D w d).
Proof.
  intros. rewrite H. unfold SafeAndReactive.
  apply SysSystem_TimedPreserves; charge_tauto.
Qed.

Theorem SystemSys
: forall G I P w d,
    G |-- TimedPreserves d I (System P w d) ->
    G |-- TimedPreserves d I (Sys P w d).
Proof.
  unfold TimedPreserves, Preserves. intros.
  rewrite H.
  unfold System. charge_tauto.
Qed.

Definition SysDisjoin_simpl
: forall D1 D2 W d,
    Sys D1 W d \\// Sys D2 W d -|- Sys (D1 \\// D2) W d.
Proof.
  unfold Sys. intros.
  split.
  { decompose_hyps; charge_tauto. }
  { unfold Discr. decompose_hyps; charge_tauto. }
Qed.

Theorem SysDisjoin_compose
: forall G D1 D2 w d P Q,
    G |-- TimedPreserves d P (Sys D1 w d) ->
    G |-- TimedPreserves d Q (Sys D2 w d) ->
    G |-- TimedPreserves d (P \\// Q) (Sys ((P //\\ D1) \\// (Q //\\ D2)) w d).
Proof.
  intros.
  etransitivity.
  2: eapply Proper_Preserves_lequiv.
  3: symmetry; eapply SysDisjoin_simpl.
  2: reflexivity.
  rewrite land_dup.
  rewrite H at 1; rewrite H0.
  unfold TimedPreserves.
  rewrite Preserves_Or.
  unfold Preserves.
  charge_intros.
  simpl next; restoreAbstraction.
  charge_assert (next P //\\ 0 <= ("T") ! //\\ ("T") ! <= d \\//
                 next Q //\\ 0 <= ("T") ! //\\ ("T") ! <= d).
  { charge_use.
    - charge_revert. charge_revert. charge_clear.
      charge_intros.
      unfold Sys, Discr.
      charge_cases; charge_tauto.
    - charge_revert. charge_clear. charge_intros.
      charge_cases; charge_tauto. }
  { charge_clear. charge_intros; charge_cases; charge_tauto. }
Qed.

Theorem NeverStuck_disjoin
: forall G D1 D2 w d P Q,
    is_st_formula P ->
    is_st_formula Q ->
    G |-- SysNeverStuck d P (Sys D1 w d) ->
    G |-- SysNeverStuck d Q (Sys D2 w d) ->
    G |-- SysNeverStuck d (P \\// Q) (Sys ((P //\\ D1) \\// (Q //\\ D2)) w d).
Proof.
  unfold SysNeverStuck.
  do 7 intro. intros Hst_P Hst_Q.
  intros.
  rewrite land_dup.
  rewrite H at 1; rewrite H0.
  rewrite <- SysDisjoin_simpl.
  rewrite <- Enabled_or.
  charge_intros. charge_cases.
  - charge_left.
    charge_assert (P //\\ Enabled (Sys D1 w d)); [ charge_tauto | ].
    rewrite Enabled_and_push by assumption.
    charge_clear.
    charge_intro. apply Proper_Enabled_lentails.
    unfold Sys, Discr. charge_cases; charge_tauto.
  - charge_right.
    charge_assert (Q //\\ Enabled (Sys D2 w d)); [ charge_tauto | ].
    rewrite Enabled_and_push by assumption.
    apply forget_prem.
    charge_intro. apply Proper_Enabled_lentails.
    unfold Sys, Discr. charge_cases; charge_tauto.
Qed.

(* MOVE *)
Lemma mkEvolution_and
: forall P Q, mkEvolution P //\\ mkEvolution Q -|- mkEvolution (P //\\ Q).
Proof.
  unfold mkEvolution; simpl; intros.
  eapply Evolution_lequiv_lequiv.
  intros. Transparent Charge.Logics.ILInsts.ILFun_Ops.
  simpl. Opaque Charge.Logics.ILInsts.ILFun_Ops.
  restoreAbstraction.
  split; charge_tauto.
Qed.

Definition SysCompose_simpl
: forall D1 D2 W1 W2 d,
    Sys (D1 //\\ D2) (W1 //\\ W2) d |-- Sys D1 W1 d //\\ Sys D2 W2 d.
Proof.
  unfold Sys, Discr, World; intros.
  { repeat charge_cases. charge_tauto.
    charge_right. charge_right.
    rewrite <- mkEvolution_and. rewrite Continuous_and.
    charge_tauto. }
(*
  { repeat charge_cases.
    - charge_tauto.
    - charge_exfalso. solve_linear.
    - charge_exfalso. solve_linear.
    - charge_right. repeat charge_split; try charge_tauto.
      charge_assert (Continuous (mkEvolution W1) //\\
                     Continuous (mkEvolution W2)).
      { charge_tauto. }
      apply forget_prem.
      rewrite Continuous_and_lequiv.
      rewrite mkEvolution_and. charge_tauto. }
*)
Qed.

Lemma Enabled_TimeBound :
  forall d,
    (d > 0)%R ->
    |-- Enabled (next (TimeBound d)).
Proof.
  intros. enable_ex_st. exists d. solve_linear.
Qed.

Definition SysRename_rule
: forall D W d sigma sigma',
    RenameMapOk sigma ->
    sigma "T" = "T" ->
    RenameDerivOk sigma sigma' ->
    Sys (Rename sigma D)
        (fun st' : state =>
           Forall st'' : state,
                         (Forall x : Var, st'' x = sigma' st' x) -->> Rename sigma (W st''))
        d
    |-- Rename sigma (Sys D W d).
Proof.
  intros.
  unfold Sys, Discr, World.
  repeat first [ rewrite Rename_and
               | rewrite Rename_or
               | rewrite Rename_Comp by apply H ].
  simpl; restoreAbstraction. rewrite H0.
  charge_split; [ charge_assumption | ].
  charge_cases; [ charge_left | charge_right ].
  { simpl. restoreAbstraction. charge_tauto. }
  { simpl. restoreAbstraction.
    charge_split; try charge_tauto.
    rewrite <- Rename_Continuous' by eassumption.
    charge_assert (Continuous
     (mkEvolution
        (fun st' : state =>
         Forall st'' : state,
         (Forall x : Var, st'' x = sigma' st' x) -->> Rename sigma (W st'')))).
    { charge_assumption. }
    apply forget_prem.
    charge_intros.
    (** TODO: This is bad. *)
    unfold Continuous.
    repeat (apply lexistsL; intros).
    charge_exists x. charge_exists x0.
    repeat charge_split; try charge_assumption.
    breakAbstraction.
    intros.
    forward_reason.
    unfold is_solution in *.
    destruct H3. exists x1.
    unfold solves_diffeqs in *.
    intros.
    specialize (H3 _ H6).
    revert H3. simpl.
    intros. forward_reason.
    split; eauto.
    rewrite H7; clear H7.
    rewrite <- H3; clear H3.
    red in H1.
    specialize (H1 _ x1).
    destruct H1.
    specialize (H1 "T" z).
    rewrite <- H1.
    unfold deriv_stateF.
    generalize dependent (x3 "T").
    rewrite H0. simpl. intros.
    unfold Ranalysis1.derive.
    eapply Ranalysis1.pr_nu.
    auto. }
Qed.

Definition Sys_rename_formula
: forall D W d sigma sigma',
      RenameMapOk sigma ->
      st_term_renamings D ->
      (forall st', st_term_renamings (W st')) ->
    Sys (rename_formula sigma D)
        (fun st' : state =>
           Forall st'' : state,
                         (Forall x : Var, st'' x = sigma' st' x) -->> rename_formula sigma (W st''))
        d |--
    Sys (Rename sigma D)
        (fun st' : state =>
           Forall st'' : state,
                         (Forall x : Var, st'' x = sigma' st' x) -->> Rename sigma (W st''))
        d.
Proof.
  intros. unfold Sys.
  charge_split.
  { charge_assumption. }
  { charge_revert. charge_clear.
    charge_intros. apply lorL.
    { apply lorR1.
      rewrite Rename_ok; [ reflexivity | assumption | assumption ]. }
    { apply lorR2.
      apply Proper_World_lentails.
      apply Evolution_lentails_lentails.
      intros.
      apply lforall_lentails_m.
      red. intros.
      rewrite Rename_ok; [ reflexivity | auto | assumption ]. } }
Qed.

Ltac sysrename_side_cond :=
  match goal with
  | [ |- forall _ : state, is_st_formula _ ]
    => tlaIntuition; abstract is_st_term_list
  | [ |- NotRenamed _ _ ]
    => reflexivity
  | [ |- _ ] => apply deriv_term_list; reflexivity
  end.

Theorem SysNeverStuck_Sys : forall (d :R) I W D,
    (d >= 0)%R ->
    I //\\ "T" = 0 |-- Enabled (0 <= "T"! <= d //\\ D) ->
    I //\\ 0 < "T" <= d |-- Enabled (World W) ->
    |-- SysNeverStuck d I (Sys D W d).
Proof.
  intros d I W D Hd. intros. unfold SysNeverStuck.
  charge_intros.
  charge_assert ("T" = 0 \\// 0 < "T" <= d).
  { solve_linear. }
  charge_revert.
  charge_clear.
  split_n 1; charge_intros.
  { unfold Sys.
    rewrite <- Enabled_and_push by (compute; tauto).
    charge_split; [ solve_linear | ].
    rewrite <- EnabledLemmas.Enabled_or.
    charge_left. unfold Discr.
    rewrite (landC D). repeat rewrite landA.
    rewrite <- Enabled_and_push by (compute; tauto).
    charge_split; [ charge_assumption | ].
    assumption. }
  { unfold Sys.
    rewrite <- Enabled_and_push by (compute; tauto).
    charge_split;
      [ simpl; restoreAbstraction; charge_assumption | ].
    rewrite <- EnabledLemmas.Enabled_or.
    charge_right. assumption. }
Qed.

Theorem SysNeverStuck_Sys' : forall (d :R) I W D,
    is_st_formula I ->
    (d >= 0)%R ->
    |-- Enabled (I -->> "T" = 0 -->> 0 <= "T"! <= d //\\ D) ->
    |-- Enabled (I -->> 0 < "T" <= d -->> World W) ->
    |-- SysNeverStuck d I (Sys D W d).
Proof.
  intros. eapply SysNeverStuck_Sys; eauto.
  - do 2 charge_revert.
    repeat (rewrite <- Enabled_limpl_st; [ | refine _ ]).
    assumption.
  - do 2 charge_revert.
    repeat (rewrite <- Enabled_limpl_st; [ | refine _ ]).
    assumption.
Qed.

(** TODO: Move Up **)
Lemma TimedPreserves_And_simple
  : forall d I1 I2 A B,
    is_st_formula I1 -> is_st_formula I2 ->
    TimedPreserves d I1 A //\\ TimedPreserves d I2 B
                   |-- TimedPreserves d (I1 //\\ I2) (A //\\ B).
Proof.
  intros. unfold TimedPreserves.
  rewrite Preserves_And_simple.
  eapply Preserves_equiv.
  { simpl; tauto. }
  { simpl; tauto. }
  { split; charge_tauto. }
  { reflexivity. }
Qed.

Lemma TimedPreserves_And
  : forall (d : R) (I1 I2 : StateFormula) (A B : ActionFormula),
   is_st_formula I1 ->
   is_st_formula I2 ->
   TimedPreserves d I1 ((I2 //\\ TimeBound d) //\\ A) //\\
   TimedPreserves d I2 ((I1 //\\ TimeBound d) //\\ B)
   |-- TimedPreserves d (I1 //\\ I2) (A //\\ B).
Proof.
  intros. unfold TimedPreserves, TimeBound.
  rewrite Preserves_And.
  eapply Preserves_equiv.
  { simpl; tauto. }
  { simpl; tauto. }
  { split; charge_tauto. }
  { reflexivity. }
Qed.

Lemma TimedPreserves_intro
  : forall (d : R) (I P G : Formula) (A : ActionFormula),
    G //\\ P |-- TimedPreserves d I A ->
    G |-- TimedPreserves d I (P //\\ A).
Proof.
  unfold TimedPreserves. intros.
  apply Preserves_intro; assumption.
Qed.

Global Instance Proper_TimedPreserves_lentails
  : Proper (eq ==> eq ==> lentails --> lentails) TimedPreserves.
Proof.
  morphism_intro. unfold Basics.flip in *.
  unfold TimedPreserves. subst. rewrite H1. reflexivity.
Qed.

Global Instance Proper_TimedPreserves_lequiv
  : Proper (eq ==> eq ==> lequiv ==> lequiv) TimedPreserves.
Proof.
  morphism_intro. unfold Basics.flip in *.
  unfold TimedPreserves. subst. rewrite H1. reflexivity.
Qed.


Lemma TimedPreserves_Rename
  : forall d (sigma : RenameMap) I A,
    sigma "T" = "T" ->
    RenameMapOk sigma ->
    TimedPreserves d (Rename sigma I) (Rename sigma A) -|- Rename sigma (TimedPreserves d I A).
Proof.
  unfold TimedPreserves, Preserves. intros.
  simpl next. restoreAbstraction.
  autorewrite with rw_rename.
  simpl rename_formula. rewrite H. simpl next_term. restoreAbstraction. reflexivity.
Qed.


(** "Parsing" of [Sys] allows us to recover the benefits of the
 ** deep embedding.
 **)

Inductive SysParse (D : ActionFormula) (w : Evolution) (d : R)
: ActionFormula -> Prop :=
| Parsed : SysParse D w d (Sys D w d).

Existing Class SysParse.
Existing Instance Parsed.

(* Some projection functions. *)
Definition Sys_D (A : ActionFormula)
           {D w d} {SP : SysParse D w d A} : ActionFormula := D.
Arguments Sys_D _ {_ _ _ _} : clear implicits.

Definition Sys_w (A : ActionFormula)
           {D w d} {SP : SysParse D w d A} : Evolution := w.
Arguments Sys_w _ {_ _ _ _} _ : clear implicits.

Definition Sys_d (A : ActionFormula)
           {D w d} {SP : SysParse D w d A} : R := d.
Arguments Sys_d _ {_ _ _ _} : clear implicits.

Definition SysRename (sigma : RenameMap) (sigma' : RenameMapDeriv)
           (A : ActionFormula) {D w d} {SP : SysParse D w d A}
  : ActionFormula :=
    Sys (rename_formula sigma D)
        (fun st' : state =>
           Forall st'' : state,
             (Forall x : Var, st'' x = sigma' st' x) -->>
             rename_formula sigma (w st''))
        d.
Arguments SysRename _ _ _ {_ _ _ _} : clear implicits.

Definition SysCompose (A : ActionFormula) (B : ActionFormula)
           {DA DB wA wB d} {SP_A : SysParse DA wA d A}
           {SP_B : SysParse DB wB d B}
  : ActionFormula :=
  Sys (DA //\\ DB) (wA //\\ wB) d.
Arguments SysCompose _ _ {_ _ _ _ _ _ _} : clear implicits.

Definition SysDisjoin (IA : StateFormula) (A : ActionFormula)
           (IB : StateFormula) (B : ActionFormula)
           {DA DB w d} {SP_A : SysParse DA w d A}
           {SP_B : SysParse DB w d B}
  : ActionFormula :=
  Sys ((IA //\\ DA) \\// (IB //\\ DB)) w d.
Arguments SysDisjoin _ _ _ _ {_ _ _ _ _ _} : clear implicits.

Definition SysSystem (A : ActionFormula)
           {D w d} {SP : SysParse D w d A} : ActionFormula :=
  System D w d.
Arguments SysSystem _ {_ _ _ _} : clear implicits.

Lemma SysCompose_abstract :
  forall A B {DA DB wA wB d} {SP_A : SysParse DA wA d A}
         {SP_B : SysParse DB wB d B},
    SysCompose A B |-- A.
Proof.
  intros. unfold SysCompose. rewrite SysCompose_simpl.
  inversion SP_A. charge_tauto.
Qed.

Theorem SysDisjoin_SafeAndReactive :
  forall DA DB w d IA IB G,
    is_st_formula IA ->
    is_st_formula IB ->
    G |-- SafeAndReactive d IA (Sys DA w d) ->
    G |-- SafeAndReactive d IB (Sys DB w d) ->
    G |-- SafeAndReactive d (IA \\// IB)
                  (SysDisjoin IA (Sys DA w d) IB (Sys DB w d)).
Proof.
  unfold SafeAndReactive. intros. charge_split.
  { apply SysDisjoin_compose; [ rewrite H1 | rewrite H2 ];
    charge_tauto. }
  { apply NeverStuck_disjoin; try assumption;
    [ rewrite H1 | rewrite H2 ];
    charge_tauto. }
Qed.
