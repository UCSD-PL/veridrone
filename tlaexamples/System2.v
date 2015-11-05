Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.ListSet.
Require Import ChargeTactics.Lemmas.
Require Import ExtLib.Tactics.
Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import TLA.ArithFacts.
Require Import TLA.Automation.
Require Import TLA.EnabledLemmas.
Require Import TLA.Inductively.

Local Open Scope HP_scope.
Local Open Scope string_scope.

(* Adds time derivative to an Evolution.
 * - the global time is stored in [t]
 * - the time until the next discrete step is stored in [T]
 *)
Definition mkEvolution (world : Evolution) : Evolution :=
  fun st' => st' "T" = --1 //\\ world st'.

Definition World (world : Evolution) : Formula :=
  Continuous (mkEvolution world) //\\ 0 < "T" //\\ 0 <= "T"!.

Definition Discr (Prog : ActionFormula) (d : R) : ActionFormula :=
  Prog //\\ "T" = 0 //\\ 0 <= "T"! <= d.

Definition Sys (P : ActionFormula) (w : Evolution) (d : R) : ActionFormula :=
  "T" <= d //\\ (Discr P d \\// World w).

Definition System (P : ActionFormula) (w : Evolution) (d : R) : ActionFormula :=
  Sys P w d \\// (Enabled (Sys P w d) -->> lfalse).

(*
Definition System' (P : Formula) (w : Evolution) (d : R) : Formula :=
  Sys P w d \\// (Enabled (Discr P d) -->> lfalse).
*)

Definition TimedInductively (delta : R) (P : StateFormula) (A : ActionFormula) : Formula :=
  Inductively (P //\\ 0 <= "T" <= delta) A.

Definition NeverStuck (I : StateFormula) (A : ActionFormula) : Formula :=
  [] (I -->> Enabled A).


(*
Ltac morphism_intro :=
  repeat (intros; match goal with
                  | |- Proper (_ ==> _)%signature _ => red
                  | |- (_ ==> _)%signature _ _ => red
                  end; intros).
*)

Instance Proper_mkEvolution_lentails
: Proper (lentails ==> lentails) mkEvolution.
Proof.
  unfold mkEvolution. morphism_intro.
  rewrite Evolution_lentails_lentails in H.
  apply Evolution_lentails_lentails.
  simpl in *. restoreAbstraction.
  intros. rewrite H. reflexivity.
Qed.

Instance Proper_mkEvolution_lequiv
: Proper (lequiv ==> lequiv) mkEvolution.
Proof.
  unfold mkEvolution. morphism_intro.
  eapply Evolution_lequiv_lequiv.
  intro.
  eapply Evolution_lequiv_lequiv with (x:=x0) in H.
  rewrite H. reflexivity.
Qed.

Instance Proper_World_lequiv
: Proper (lequiv ==> lequiv) World.
Proof.
  unfold World; morphism_intro.
  rewrite H. reflexivity.
Qed.

Instance Proper_World_lentails
: Proper (lentails ==> lentails) World.
Proof.
  unfold World; morphism_intro.
  rewrite H. reflexivity.
Qed.

Instance Proper_Discr
: Proper (lequiv ==> eq ==> lequiv) Discr.
Proof.
  morphism_intro; unfold Discr.
  subst. rewrite H. reflexivity.
Qed.

Instance Proper_Sys_lequiv
: Proper (lequiv ==> lequiv ==> eq ==> lequiv) Sys.
Proof.
  unfold Sys, Discr, World. morphism_intro.
  subst. rewrite H; clear H. rewrite H0; clear H0. reflexivity.
Qed.

Instance Proper_Sys_lentails
: Proper (lentails ==> lentails ==> eq ==> lentails) Sys.
Proof.
  unfold Sys, Discr, World. morphism_intro.
  subst. rewrite H; clear H. rewrite H0; clear H0. reflexivity.
Qed.

Instance Proper_System_lequiv
: Proper (lequiv ==> lequiv ==> eq ==> lequiv) System.
Proof.
  unfold System, Discr, World. morphism_intro.
  subst. rewrite H; clear H. rewrite H0; clear H0. reflexivity.
Qed.

Theorem SysInductively
: forall P A Prog IndInv (w : Evolution) (d:R),
  (forall st', is_st_formula (w st')) -> (* TODO: Do we really want this? *)
  P |-- [] A ->
  A //\\ IndInv //\\ 0 <= "T"! <= "T" //\\ "T" <= d (* This could be "T"! < "T" *)
    //\\ World w |-- next IndInv ->
  A //\\ IndInv //\\ "T" = 0 //\\ 0 <= "T"! <= d
    //\\ Discr Prog d |-- next IndInv ->
  P |-- Inductively IndInv (Sys Prog w d).
Proof.
  intros P A Prog IndInv world delta.
  intros Hst_world H Hworld Hdiscr.
  rewrite H; clear H.
  unfold Inductively.
  tlaRevert. apply Always_imp.
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

(** TODO: Move this **)
Lemma land_dup : forall A : Formula, A -|- A //\\ A.
Proof. intros; split; charge_tauto. Qed.

Theorem SysSystem
: forall G I P w d,
  G |-- Inductively I (Sys P w d) ->
  G |-- NeverStuck I (Sys P w d) ->
  G |-- Inductively I (System P w d).
Proof.
  intros. unfold NeverStuck, Inductively in *.
  rewrite (land_dup G).
  rewrite H at 1.
  rewrite H0.
  rewrite Always_and.
  charge_revert.
  apply Always_imp.
  unfold System.
  charge_intros.
  decompose_hyps.
  - charge_tauto.
  - charge_exfalso. charge_tauto.
Qed.

Theorem SystemSys
: forall G I P w d,
    G |-- Inductively I (System P w d) ->
    G |-- Inductively I (Sys P w d).
Proof.
  unfold Inductively. intros.
  rewrite H.
  always_imp_tac.
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
    G |-- Inductively P (Sys D1 w d) ->
    G |-- Inductively Q (Sys D2 w d) ->
    G |-- Inductively (P \\// Q) (Sys ((P //\\ D1) \\// (Q //\\ D2)) w d).
Proof.
  intros.
  etransitivity.
  2: eapply Proper_Inductively. 3: symmetry; eapply SysDisjoin_simpl. 2: reflexivity.
  rewrite land_dup.
  rewrite H at 1; rewrite H0.
  rewrite Inductively_Or.
  unfold Inductively.
  always_imp_tac.
  charge_intros.
  charge_use.
  charge_revert.
  apply forget_prem.
  charge_intros.
  unfold Sys, Discr.
  repeat decompose_hyps; try charge_tauto.
Qed.

Theorem NeverStuck_disjoin
: forall G D1 D2 w d P Q,
    is_st_formula P ->
    is_st_formula Q ->
    G |-- NeverStuck P (Sys D1 w d) ->
    G |-- NeverStuck Q (Sys D2 w d) ->
    G |-- NeverStuck (P \\// Q) (Sys ((P //\\ D1) \\// (Q //\\ D2)) w d).
Proof.
  unfold NeverStuck.
  do 7 intro. intros Hst_P Hst_Q.
  intros.
  rewrite land_dup.
  rewrite H at 1; rewrite H0.
  rewrite Always_and.
  always_imp_tac.
  rewrite <- SysDisjoin_simpl.
  rewrite <- Enabled_or.
  charge_intros. decompose_hyps.
  - charge_left.
    charge_assert (P //\\ Enabled (Sys D1 w d)); [ charge_tauto | ].
    rewrite Enabled_and_push by assumption.
    apply forget_prem.
    charge_intro. apply Proper_Enabled_lentails.
    unfold Sys, Discr. decompose_hyps; charge_tauto.
  - charge_right.
    charge_assert (Q //\\ Enabled (Sys D2 w d)); [ charge_tauto | ].
    rewrite Enabled_and_push by assumption.
    apply forget_prem.
    charge_intro. apply Proper_Enabled_lentails.
    unfold Sys, Discr. decompose_hyps; charge_tauto.
Qed.

Lemma Continuous_and
: forall P Q, Continuous (P //\\ Q) |-- Continuous P //\\ Continuous Q.
Proof.
  unfold Continuous; intros.
  repeat (eapply lexistsL; intros).
  charge_split; do 2 eapply lexistsR;
  instantiate (1:= x); instantiate (1:=x0);
  repeat charge_split; try charge_tauto.
  - charge_assert (PropF (is_solution x0 (P //\\ Q) x)).
    + charge_assumption.
    + apply forget_prem.
      breakAbstraction. intros.
      eapply Proper_is_solution_lentails. 4: eassumption.
      reflexivity. charge_tauto. reflexivity.
  - charge_assert (PropF (is_solution x0 (P //\\ Q) x)).
    + charge_assumption.
    + apply forget_prem.
      breakAbstraction. intros.
      eapply Proper_is_solution_lentails. 4: eassumption.
      reflexivity. charge_tauto. reflexivity.
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
  { repeat decompose_hyps. charge_tauto.
    charge_right. charge_right.
    rewrite <- mkEvolution_and. rewrite Continuous_and.
    charge_tauto. }
(*
  { repeat decompose_hyps.
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
  decompose_hyps; [ charge_left | charge_right ].
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
