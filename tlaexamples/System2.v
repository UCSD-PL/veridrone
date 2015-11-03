Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import TLA.ArithFacts.
Require Import TLA.Automation.
Require Import TLA.EnabledLemmas.
Require Import TLA.Inductively.
Require Import ChargeTactics.Lemmas.
Require Import Coq.Lists.ListSet.

Local Open Scope HP_scope.
Local Open Scope string_scope.

(* Convenience functions to say that all variables in a list
 * have derivative 0.
 *)
Definition AllConstant (vars : list Var) : state->Formula :=
  fun st' => List.fold_right
               (fun x a => st' x = 0 //\\ a)
               TRUE vars.

(* Adds time derivative to an Evolution.
 * - the global time is stored in [t]
 * - the time until the next discrete step is stored in [T]
 *)
Definition mkEvolution (world : Evolution) : Evolution :=
  fun st' => st' "T" = --1 //\\ world st'.

Definition World (world : Evolution) : Formula :=
  Continuous (mkEvolution world) //\\ 0 < "T" //\\ 0 <= "T"!.

Definition Discr (Prog : Formula) (d : R) : Formula :=
  Prog //\\ "T" = 0 //\\ 0 <= "T"! <= d.

Definition Sys (P : Formula) (w : Evolution) (d : R) : Formula :=
  "T" <= d //\\ (Discr P d \\// World w).

Definition NeverStuck (I : Formula) (A : Formula) : Formula :=
  Inductively (I //\\ Enabled A) A.

Ltac morphism_intro :=
  repeat (intros; match goal with
                  | |- Proper (_ ==> _)%signature _ => red
                  | |- (_ ==> _)%signature _ _ => red
                  end; intros).

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

Theorem SysInductively
: forall P A Prog IndInv (w : Evolution) (d:R),
  is_st_formula IndInv ->
  (forall st', is_st_formula (w st')) ->
  P |-- [] A ->
  A //\\ IndInv //\\ 0 <= "T"! < "T" //\\ "T" <= d
    //\\ World w |-- next IndInv ->
  A //\\ IndInv //\\ "T" = 0 //\\ 0 <= "T"! <= d
    //\\ Discr Prog d |-- next IndInv ->
  P |-- Inductively IndInv (Sys Prog w d).
Proof.
  intros P A Prog IndInv world delta.
  intros Hst_IndInv Hst_world H Hworld Hdiscr.
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
    (** at this point, "T" is a constant. **)
    admit. }
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

(*
Instance Proper_is_solution
  : Proper (eq ==> lentails ==> Rge ==> Basics.impl) is_solution.
Proof.
  morphism_intro. red. unfold is_solution.
  subst.
  intros. destruct H. exists x.
  unfold solves_diffeqs in *.
  intros.
  assert (0 <= z <= x1)%R.
  { solve_linear. }
  eapply H in H3.
  specialize (H0 (fun x2 : Var => deriv_stateF y x x2 z)
                 (Stream.forever (y z))).
  eauto.
Qed.

About is_solution.
*)

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

Lemma is_solution_and : forall f P Q r,
    is_solution f (P //\\ Q) r <-> is_solution f P r /\ is_solution f Q r.
Proof.
  unfold is_solution.
  intros. split.
  { intros. destruct H.
    split; exists x.
    - unfold solves_diffeqs in *.
      intros. eapply H in H0.
      Transparent Charge.Logics.ILInsts.ILFun_Ops.
      simpl in *. tauto.
    - unfold solves_diffeqs in *.
      intros. eapply H in H0.
      simpl in *. tauto. }
  { intros. destruct H. destruct H. destruct H0.
    exists x.
    unfold solves_diffeqs in *.
    intros.
    specialize (H _ H1).
    specialize (H0 _ H1).
    simpl. split; auto.
    revert H0.
    match goal with
    | |- ?X -> ?Y => cutrewrite (eq X Y); auto
    end.
    f_equal. f_equal.
    apply FunctionalExtensionality.functional_extensionality.
    intros. unfold deriv_stateF.
    unfold Ranalysis1.derive.
    eapply Ranalysis1.pr_nu. }
Qed.

Instance Proper_PropF_lequiv
  : Proper (iff ==> lequiv) PropF.
Proof.
  morphism_intro. compute. tauto.
Qed.

Instance Proper_PropF_lentails
  : Proper (Basics.impl ==> lentails) PropF.
Proof.
  morphism_intro. compute. tauto.
Qed.

Lemma PropF_and : forall P Q, PropF (P /\ Q) -|- PropF P //\\ PropF Q.
Proof. compute. tauto. Qed.

(*
Lemma Continuous_and_lequiv
  : forall P Q, Continuous P //\\ Continuous Q -|- Continuous (P //\\ Q).
Proof.
  unfold Continuous; split.
  { charge_fwd.
    destruct (RIneq.Rtotal_order x x1) as [ ? | [ ? | ? ] ].
    - charge_exists x.
      charge_exists x0.
      charge_split; [ charge_assumption | ].
      rewrite is_solution_and.
      rewrite PropF_and.
      charge_split; [ | charge_assumption ].
      charge_split; try charge_assumption.
      breakAbstraction. intros.
      Require Import ExtLib.Tactics.
      unfold is_solution in *.
      forward_reason.
      exists x4. unfold solves_diffeqs in *.
      intros.
      assert (x0 z = x2 z) by admit.
      rewrite H9 in *.
      clear H5.
      assert (0 <= z <= x1)%R.
      { solve_linear. }
      eapply H3 in H5.
      revert H5.
      admit.
    - charge_exists x.
      charge_exists x0.
      subst.
      charge_split; [ charge_assumption | ].
      rewrite is_solution_and.
      rewrite PropF_and.
      charge_split; [ | charge_assumption ].
      charge_split; try charge_assumption.
      admit.
    - charge_exists x1.
      charge_exists x2.
      charge_split; [ charge_assumption | ].
      rewrite is_solution_and.
      rewrite PropF_and.
      charge_split; [ | charge_assumption ].
      charge_split; try charge_assumption.
      admit. }
  { repeat (eapply lexistsL; intros).
    charge_split; do 2 eapply lexistsR;
    instantiate (1:= x); instantiate (1:=x0);
    repeat charge_split; try charge_tauto.
    - charge_assert (PropF (is_solution x0 (P //\\ Q) x)).
      + charge_assumption.
      + apply forget_prem.
        breakAbstraction. intros.
        eapply Proper_is_solution_lentails; [ | | | eassumption ].
        * reflexivity.
        * simpl. restoreAbstraction. intros. charge_tauto.
        * reflexivity.
    - charge_assert (PropF (is_solution x0 (P //\\ Q) x)).
      + charge_assumption.
      + apply forget_prem.
        breakAbstraction. intros.
        eapply Proper_is_solution_lentails; [ | | | eassumption ].
        * reflexivity.
        * simpl. restoreAbstraction. intros. charge_tauto.
        * reflexivity. }
Qed.
*)

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

(** TODO: Move this **)
Definition RenameMapOk (sigma : RenameMap) : Prop :=
  forall x : Var, is_st_term (sigma x) = true.

Require Import ExtLib.Tactics.

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
