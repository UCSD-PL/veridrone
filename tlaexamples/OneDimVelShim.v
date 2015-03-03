Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Import LibNotations.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import TLA.ArithFacts.
Require Import TLA.Substitution.
Require Import Coq.Reals.Rdefinitions.

Open Scope HP_scope.
Open Scope string_scope.

Definition World (world : list DiffEq) (d : R) : Formula :=
  Continuous (("t"'::=--1)::world) /\ "t"! >= 0 /\ "pc" = 0.

Definition Discr (Prog : Formula) (d : R) : Formula :=
  Prog /\ "t"! = d /\ "pc" = 1.

Definition Sys (Init Prog: Formula) (world : list DiffEq)
           (d : R) : Formula :=
  Init /\ [](World world d \/ Discr Prog d).

Theorem sys_by_induction : forall Init Prog Inv IndInv w d,
  is_st_formula IndInv ->
  (|- Init --> IndInv) ->
  (|- IndInv --> Inv) ->
  (|- (IndInv /\ World w d) --> next IndInv) ->
  (|- (IndInv /\ Discr Prog d) --> next IndInv) ->
  (|- Sys Init Prog w d --> [] Inv).
Proof.
  intros Init Prog Inv IndInv w d Hst Hinit Hinv Hw Hdiscr.
  apply imp_trans with (F2:=[]IndInv).
  - apply imp_trans with (F2:=Sys IndInv Prog w d).
    + unfold Sys. apply and_right.
      * apply and_left1; assumption.
      * apply and_left2; apply imp_id.
    + apply inv_discr_ind.
      * assumption.
      * apply or_next; assumption.
  - apply always_imp; assumption.
Qed.

Section SenseCtrl.

  Variable Is : Formula.
  Variable Ic : Formula.
  Variable w : list DiffEq.
  Variable d : R.
  Variable S : Formula.
  Variable C : Formula.
  Variable P : Formula.
  Variable E : Formula.

  Theorem sense_ctrl :
    (|- Sys Is S w d --> []E) ->
    (|- Sys Ic (C /\ E) w d --> []P) ->
    (|- Sys (Is /\ Ic) (S /\ C) w d --> [](P /\ E)).
  Proof.
    Opaque World Discr.
    simpl. intros Hs Hc tr [ [HIs HIc] HN] n.
    split.
    - apply Hc. intuition.
      pose proof (HN n0). intuition.
      right. Transparent Discr. revert H0.
      unfold Discr. simpl. intuition.
      apply Hs. intuition.
      specialize (HN n1). intuition.
      right. simpl in *. intuition.
    - apply Hs. intuition.
      specialize (HN n0). intuition.
      right. simpl in *. intuition.
  Qed.

End SenseCtrl.

Section SensorWithError.

  Variable x : Var.
  Variable Xmax : Var.
  Variable Xmin : Var.
  Variable err : R.

  Definition Sense : Formula :=
    Xmax = Xmin + err /\ Xmin <= x <= Xmax.

  Definition SenseSafe : Formula :=
    "pc" = 1 --> Xmin <= x <= Xmax.

  Theorem sense_safe : forall w d,
    |- Sys SenseSafe Sense w d --> []SenseSafe.
  Proof.
    intros w d. apply and_left2.
    apply always_imp. solve_linear.
  Qed.

End SensorWithError.

Section Ctrl.

  (* Upper bound on velocity. *)
  Variable ub : R.
  (* Max time between executions of the
     controller. *)
  Variable d : R.
  Hypothesis d_gt_0 : (d > 0)%R.
  
  (* The continuous dynamics of the system *)
  Definition world : list DiffEq :=
    ["v"' ::= "a", "a"' ::= 0].

  Definition Ctrl : Formula :=
       ("A"*d + "Vmax" <= ub /\ "a"! = "A")
    \/ ("a"! <= 0).

(*
  Definition Ctrl1 : Formula :=
       ("A"*d + "v" <= ub /\ "a"! = "A")
    \/ ("a"! <= 0).

  Definition Ctrl2 : Formula :=
       "V"! = "v"
    /\   (("a" >= 0 /\ "A"*d + "V" + "a"*d <= ub /\ "a"! = "A")
       \/ ("a" < 0 /\ "A"*d + "V" <= ub /\ "a"! = "A")
       \/ "a"! <= 0).

  Definition Next (Ctrl:Formula) : Formula :=
       (Evolve /\ "t"! >= 0)
    \/ (Ctrl /\ "t"! = d /\ Unchanged (["v"])).
*)

  Definition Ic : Formula :=
    "v" <= ub /\ "v" + "a"*d <= ub /\
    0 <= "t" <= d /\ "Vmax" >= "v".

  Definition Safe : Formula :=
    "v" <= ub.

  Definition IndInv : Formula :=
       ("a" <  0 --> Safe)
    /\ ("a" >= 0 --> "a"*"t" + "v" <= ub)
    /\ 0 <= "t" <= d.

  Theorem ctrl_safe :
    |- Sys Ic (Ctrl /\ "Vmax" >= "v") world d --> []"v" <= ub.
  Proof.
    

(*
  Definition AbstractSys : Formula :=
    Init /\ [](Next AbstractCtrl).

  Definition Ctrl1Sys : Formula :=
    Init /\ [](Next Ctrl1).

  Definition Ctrl2Sys : Formula :=
    Init /\ [](Next Ctrl2).
*)

  Definition Safe : Formula :=
    "v" <= ub.

  Lemma ctrl_safe :
    |- Sys Ic (Ctrl /\ VBound) w d --> []Safe.

  Definition IndInv : Formula :=
       ("a" <  0 --> Safe)
    /\ ("a" >= 0 --> "a"*"t" + "v" <= ub)
    /\ 0 <= "t" <= d.

  Theorem abstract_safety :
    |- AbstractSys --> []Safe.

Section Ctrl.

  (* Upper bound on velocity. *)
  Variable ub : R.
  (* Max time between executions of the
     controller. *)
  Variable d : R.
  Hypothesis d_gt_0 : (d > 0)%R.

  (* The continuous dynamics of the system *)
  Definition Evolve : Formula :=
    Continuous (["v"' ::= "a",
                 "a"' ::= 0,
                 "t"' ::= --1]).

  Definition AbstractCtrl : Formula :=
       ((Exists Term (fun e => "v" <= e /\ "A"*d + e <= ub))
         /\ "a"! = "A")
    \/ ("a"! <= 0).

  Definition Ctrl1 : Formula :=
       ("A"*d + "v" <= ub /\ "a"! = "A")
    \/ ("a"! <= 0).

  Definition Ctrl2 : Formula :=
       "V"! = "v"
    /\   (("a" >= 0 /\ "A"*d + "V" + "a"*d <= ub /\ "a"! = "A")
       \/ ("a" < 0 /\ "A"*d + "V" <= ub /\ "a"! = "A")
       \/ "a"! <= 0).

  Definition Next (Ctrl:Formula) : Formula :=
       (Evolve /\ "t"! >= 0)
    \/ (Ctrl /\ "t"! = d /\ Unchanged (["v"])).

  Definition Init : Formula :=
    "v" <= ub /\ "v" + "a"*d <= ub /\ 0 <= "t" <= d.

  Definition AbstractSys : Formula :=
    Init /\ [](Next AbstractCtrl).

  Definition Ctrl1Sys : Formula :=
    Init /\ [](Next Ctrl1).

  Definition Ctrl2Sys : Formula :=
    Init /\ [](Next Ctrl2).

  Definition Safe : Formula :=
    "v" <= ub.

  Definition IndInv : Formula :=
       ("a" <  0 --> Safe)
    /\ ("a" >= 0 --> "a"*"t" + "v" <= ub)
    /\ 0 <= "t" <= d.

  Theorem abstract_safety :
    |- AbstractSys --> []Safe.
  Proof.
    apply imp_trans with (F2:=[]IndInv).
    - apply imp_trans with (F2:=IndInv /\ [](Next AbstractCtrl)).
      + simpl; intuition; solve_nonlinear.
      + apply inv_discr_ind.
        * compute; tauto.
        * apply or_next.
          { unfold Evolve. prove_inductive. }
          { solve_linear.
            - destruct H0. intuition.
              rewrite_next_st. clear - H1 H H3. solve_nonlinear.
            - destruct H0. intuition.
              rewrite_next_st. clear - H9 H10. solve_nonlinear.
            - rewrite_next_st. clear - H1 H H3. solve_nonlinear.
            - rewrite_next_st. solve_nonlinear. }
    - apply always_imp. solve_nonlinear.
  Qed.

  Theorem ctrl1_safety :
    |- Ctrl1Sys --> []Safe.
  Proof.
    apply imp_trans with (F2:=AbstractSys).
    - apply and_right.
      + apply and_left1. apply imp_id.
      + apply and_left2. apply always_imp.
        apply or_left.
        * apply or_right1. apply imp_id.
        * apply or_right2. solve_linear.
          left. split; auto. exists "v".
          solve_linear.
    - apply abstract_safety.
  Qed.

  Definition Bound1 : Formula :=
    []("a" >= 0 --> "V" + "a"*d >= "v").

  Theorem ctrl2_bound1 :
    |- Ctrl2Sys --> Bound1.
  Proof.
    admit.
  Qed.

  Definition Bound2 : Formula :=
    []("a" < 0 --> "V" >= "v").

  Theorem ctrl2_bound2 :
    |- Ctrl2Sys --> Bound2.
  Proof.
    admit.
  Qed.

Lemma always_and_left2 : forall F1 F2 F3 F4,
  (|- (([](F1 /\ F2)) /\ F4) --> F3) ->
  (|- (([]F1) /\ ([]F2) /\ F4) --> F3).
Proof. simpl; intuition. Qed.

Lemma or_left1 : forall F1 F2 F3 F4,
  (|- (F1 /\ F3) --> F4) ->
  (|- (F2 /\ F3) --> F4) ->
  (|- ((F1 \/ F2) /\ F3) --> F4).
Proof. simpl; intuition. Qed.

  Theorem ctrl2_safety :
    |- Ctrl2Sys --> []Safe.
  Proof.
    apply imp_trans with (F2:=AbstractSys).
    - apply and_right.
      + apply and_left1. apply imp_id.
      + apply imp_strengthen with (F2:=Bound1 /\ Bound2);
        try (apply and_right; (apply ctrl2_bound1 ||
                                     apply ctrl2_bound2)).
        apply and_assoc_left. apply and_left2.
        unfold Bound1, Bound2. apply always_and_left2.
        apply always_and_left. apply always_imp.
        apply and_assoc_left. apply or_left1.
        * apply or_right1. apply and_left1. apply imp_id.
        * apply or_right2. solve_linear.
          { left. split; auto. exists ("V" + "a"*d).
            solve_linear. }
          { left. split; auto. exists ("V").
            solve_linear. }
    - apply abstract_safety.
  Qed.

End Ctrl.
