Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Import LibNotations.
Require Import TLA.ArithFacts.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import TLA.BasicProofRules.
Require Import Examples.System.
(*Require Import TLA.Substitution. *)

Open Scope HP_scope.
Open Scope string_scope.

Section SenseCtrl.

  Variable Is : Formula.
  Variable Ic : Formula.
  Variable dvars : list Var.
  Variable cvars : list Var.
  Variable w : list DiffEq.
  Variable d : R.
  Variable S : Formula.
  Variable C : Formula.
  Variable P : Formula.
  Variable E : Formula.

  Theorem sense_ctrl :
    (|-- Sys dvars cvars Is S w d -->> []E) ->
    (|-- Sys dvars cvars Ic (C //\\ E) w d -->> []P) ->
    (|-- Sys dvars cvars (Is //\\ Ic) (S //\\ C) w d -->> [](P //\\ E)).
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

End SenseCtrl.

  Ltac decompose_hyps :=
    repeat rewrite land_lor_distr_R;
    repeat rewrite land_lor_distr_L;
    repeat apply lorL.

Module SensorWithDelay.

  Variable x : Var.
  Variable Xmax : Var.
  Variable Xmin : Var.
  Variable xderiv : Var.
  Variable d : R.
  Hypothesis get_deriv_Xmax :
    get_deriv Xmax
              (["t" '  ::= -- (1), x '  ::= xderiv, Xmax '  ::= 0, 
                Xmin '  ::= 0, xderiv '  ::= 0]) = Some (NatT 0).
  Hypothesis get_deriv_Xmin :
    get_deriv Xmin
              (["t" '  ::= -- (1), x '  ::= xderiv, Xmax '  ::= 0, 
                Xmin '  ::= 0, xderiv '  ::= 0]) = Some (NatT 0).
  Hypothesis get_deriv_xderiv :
    get_deriv xderiv
              (["t" '  ::= -- (1), x '  ::= xderiv, Xmax '  ::= 0, 
                Xmin '  ::= 0, xderiv '  ::= 0]) = Some (NatT 0).
  Hypothesis get_deriv_x :
    get_deriv x
              (["t" '  ::= -- (1), x '  ::= xderiv, Xmax '  ::= 0, 
                Xmin '  ::= 0, xderiv '  ::= 0]) =
    Some (VarNowT xderiv).

  Ltac rewrite_deriv_hyps :=
    breakAbstraction;
    repeat first [ rewrite get_deriv_Xmax |
                   rewrite get_deriv_Xmin |
                   rewrite get_deriv_xderiv |
                   rewrite get_deriv_x ].

  Definition Sense : Formula :=
    xderiv! = xderiv //\\
    (     (xderiv >= 0 //\\ Xmax! = x + xderiv*d //\\ Xmin! = x)
     \\// (xderiv < 0 //\\ Xmax! = x //\\ Xmin! = x + xderiv*d)).

  Definition SenseSafeInd : Formula :=
         (xderiv >= 0 -->> (Xmax >= x + xderiv*"t" //\\ Xmin <= x))
    //\\ (xderiv < 0 -->> (Xmax >= x //\\ Xmin <= x + xderiv*"t")).

  Theorem sense_safe :
    |-- Sys (Xmax::Xmin::xderiv::nil)%list (x::nil)%list
            SenseSafeInd Sense (DiffEqC x xderiv::nil)%list d -->>
            []SenseSafeInd.
  Proof.
    tlaIntro.
    eapply discr_indX.
    - tlaIntuition.
    - tlaAssume.
    - tlaAssume.
    - decompose_hyps.
      + eapply diff_ind with (Hyps:=TRUE);
        try solve [tlaIntuition | tlaAssume ];
        repeat tlaSplit;
        try solve [ rewrite_deriv_hyps; solve_linear |
                    eapply unchanged_continuous;
                      [ tlaIntro; tlaAssume |
                        solve_linear ] ].
      + solve_linear; solve_nonlinear.
      + solve_linear; solve_nonlinear.
  Qed.

End SensorWithDelay.

Module SensorWithError.

  Variable x : Var.
  Variable Xmax : Var.
  Variable Xmin : Var.
  Variable err : R.

  Definition Sense : Formula :=
    Xmax = Xmin + err //\\ Xmin <= x <= Xmax.

  Definition SenseSafe : Formula :=
    "pc" = 1 -->> Xmin <= x <= Xmax.

  Theorem sense_safe : forall w d,
    |-- Sys (Xmax::Xmin::nil)%list (x::nil)%list
           SenseSafe Sense w d -->> []SenseSafe.
  Proof.
    intros w d. tlaIntro.
    apply landL2. tlaRevert.
    rewrite Always_or.
    apply always_imp. tlaIntro.
    decompose_hyps.
    - solve_linear.
    - solve_linear.
    -


    intros w d.
    tlaIntro.
    eapply discr_indX.
    - tlaIntuition.
    - tlaAssume.
    - tlaAssume.
    - decompose_hyps.
      + eapply diff_ind with (Hyps:=TRUE);
        try solve [tlaIntuition | tlaAssume ];
        repeat tlaSplit.
        * admit.
        * solve_linear.
        * eapply unchanged_continuous.
          { tlaIntro; tlaAssume. }
          { solve_linear. rewrite_next_st. 
        try solve [ eapply unchanged_continuous;
                    [ tlaIntro; tlaAssume |
                      solve_linear ] ].
      + solve_linear; solve_nonlinear.
      + solve_linear; solve_nonlinear.
  Qed.
 tlaIntro. apply landL2.
    tlaRevert. apply always_imp. solve_linear.
  Qed.

End SensorWithError.

Section Ctrl.

  (* Upper bound on velocity. *)
  Variable ub : R.
  (* Max time between executions of the
     controller. *)
  Variable d : R.
  Hypothesis d_gt_0 : (d > 0)%R.
  Variable err : R.
  
  (* The continuous dynamics of the system *)
  Definition world : list DiffEq :=
    ["v"' ::= "a"].

  Definition Ctrl : Formula :=
       ("A"*d + "Vmax" <= ub //\\ "a"! = "A")
    \/ ("a"! <= 0).

(*
  Definition Ctrl1 : Formula :=
       ("A"*d + "v" <= ub //\\ "a"! = "A")
    \/ ("a"! <= 0).

  Definition Ctrl2 : Formula :=
       "V"! = "v"
    //\\   (("a" >= 0 //\\ "A"*d + "V" + "a"*d <= ub //\\ "a"! = "A")
       \/ ("a" < 0 //\\ "A"*d + "V" <= ub //\\ "a"! = "A")
       \/ "a"! <= 0).

  Definition Next (Ctrl:Formula) : Formula :=
       (Evolve //\\ "t"! >= 0)
    \/ (Ctrl //\\ "t"! = d //\\ Unchanged (["v"])).
*)

  Definition Ic : Formula :=
    "v" <= ub //\\ "v" + "a"*d <= ub /\
    0 <= "t" <= d //\\ "Vmax" >= "v".

  Definition Safe : Formula :=
    "v" <= ub.

  Definition IndInv : Formula :=
       ("a" <  0 --> Safe)
    //\\ ("a" >= 0 --> "a"*"t" + "v" <= ub).

  Theorem ctrl_safe :
    |- Sys ("a"::nil) ("v"::nil)
           Ic (Ctrl //\\ "Vmax" >= "v") world d --> []"v" <= ub.
  Proof.
(*    Existing Class is_st_formula.
    Hint Extern 1(is_st_formula _) => (simpl; intuition)
                                     : typeclass_instances.
    Typeclasses eauto := debug.
*)
    apply sys_by_induction with (IndInv:=IndInv).
    - simpl; intuition.
    - solve_nonlinear.
    - solve_nonlinear.
    - eapply diff_ind with (Hyps:=TRUE).
      + simpl; intuition.
      + simpl; intuition.
      + apply and_left2; apply and_left1; apply imp_id.
      + simpl; intuition.
      + apply and_left1; apply imp_id.
      + simpl; intuition.
      + simpl deriv_formula.
        repeat apply and_right; try solve [solve_linear].
        Lemma go_away_Q : forall Q P,
            (|- P) -> (|- Q --> P).
        Proof. simpl; intuition. Qed.
        * apply go_away_Q.
          eapply unchanged_continuous;
            [apply imp_id | solve_linear].
        * apply go_away_Q.
          eapply unchanged_continuous;
            [apply imp_id | solve_linear].
    - solve_nonlinear.
  Qed.

  Definition SenseCtrlSys :=
    Sys ("a"::"Vmax"::"Vmin"::nil)%list ("v"::nil)%list
        (SenseSafe "v" "Vmax" "Vmin" //\\ Ic)
        (Sense "v" "Vmax" "Vmin" err //\\ Ctrl) 
        world d.

  Require Import RelationClasses.
  Instance Reflexive_all_in {T} : Reflexive (@all_in T).
  Proof. red; red; tauto. Qed.

  Instance Reflexive_Rge : Reflexive Rge.
  Proof. Require Import RIneq.
         red. intro. apply Req_ge. reflexivity.
  Qed.

  Ltac sys_apply_with_weaken H :=
    eapply imp_trans; [ | apply H ];
    eapply weaken_sys; [ | | | | | ];
      try solve [ apply all_in_dec_ok ; reflexivity
                | apply imp_id
                | reflexivity ].
      
  Theorem SenseCtrlSys_safe :
    |- SenseCtrlSys --> [](Safe //\\ SenseSafe "v" "Vmax" "Vmin").
  Proof.
    apply sense_ctrl.
    + sys_apply_with_weaken sense_safe.
      apply go_away_Q. apply imp_id.
    + sys_apply_with_weaken ctrl_safe.
      unfold SenseSafe. solve_linear.
  Qed.

End Ctrl.


(*
  Definition AbstractSys : Formula :=
    Init //\\ [](Next AbstractCtrl).

  Definition Ctrl1Sys : Formula :=
    Init //\\ [](Next Ctrl1).

  Definition Ctrl2Sys : Formula :=
    Init //\\ [](Next Ctrl2).
*)

  Definition Safe : Formula :=
    "v" <= ub.

  Lemma ctrl_safe :
    |- Sys Ic (Ctrl //\\ VBound) w d --> []Safe.

  Definition IndInv : Formula :=
       ("a" <  0 --> Safe)
    //\\ ("a" >= 0 --> "a"*"t" + "v" <= ub)
    //\\ 0 <= "t" <= d.

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
       (Exists e : Term, "v" <= e //\\ "A"*d + e <= ub
         //\\ "a"! = "A")
    \\// ("a"! <= 0).

  (* We are going to prove that this is a refinement of AbstractCtrl *)
  Definition Ctrl1 : Formula :=
       ("A"*d + "v" <= ub //\\ "a"! = "A")
    \\// ("a"! <= 0).

  (* We are going to prove that this is a refinement of AbstractCtrl *)
  Definition Ctrl2 : Formula :=
       "V"! = "v"
    //\\   (("a" >= 0 //\\ "A"*d + "V" + "a"*d <= ub //\\ "a"! = "A")
       \\// ("a" < 0 //\\ "A"*d + "V" <= ub //\\ "a"! = "A")
       \\// "a"! <= 0).

  Definition Next (Ctrl:Formula) : Formula :=
       (Evolve //\\ "t"! >= 0)
    \\// (Ctrl //\\ "t"! = d //\\ Unchanged (["v"])).

  Definition Init : Formula :=
    "v" <= ub //\\ "v" + "a"*d <= ub //\\ 0 <= "t" <= d.

  Definition AbstractSys : Formula :=
    Init //\\ [](Next AbstractCtrl).

  Definition Ctrl1Sys : Formula :=
    Init //\\ [](Next Ctrl1).

  Definition Ctrl2Sys : Formula :=
    Init //\\ [](Next Ctrl2).

  Definition Safe : Formula :=
    "v" <= ub.

  Definition IndInv : Formula :=
       ("a" <  0 -->> Safe)
    //\\ ("a" >= 0 -->> "a"*"t" + "v" <= ub)
    //\\ 0 <= "t" <= d.

  Theorem abstract_safety :
    |-- AbstractSys -->> []Safe.
  Proof.
    apply imp_trans with (F2:=[]IndInv).
    - apply imp_trans with (F2:=IndInv //\\ [](Next AbstractCtrl)).
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

  (** TODO: move this **)
  Lemma ex_right : forall {T} P (F : T -> Formula),
      (exists (x : T), |-- P -->> F x) ->
      (|-- P -->> Exists _ F).
  Proof.
    simpl. intros. destruct H.
    exists x. eauto.
  Qed.

  Theorem ctrl1_refinement
  : |-- Ctrl1 -->> AbstractCtrl.
  Proof.
    unfold Ctrl1, AbstractCtrl.
    apply or_left.
    * apply or_right1.
      apply and_right.
      - eapply ex_right.
        exists "v".
        solve_linear.
      - apply and_left2. apply imp_id.
    * apply or_right2. apply imp_id.
  Qed.

  Theorem ctrl1_safety :
    |-- Ctrl1Sys -->> []Safe.
  Proof.
    apply imp_trans with (F2:=AbstractSys).
    - apply and_right. (** this proof should just be rewrite **)
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
    []("a" >= 0 -->> "V" + "a"*d >= "v").

  Theorem ctrl2_bound1 :
    |-- Ctrl2Sys -->> Bound1.
  Proof.
    
  Qed.

  Definition Bound2 : Formula :=
    []("a" < 0 -->> "V" >= "v").

  Theorem ctrl2_bound2 :
    |-- Ctrl2Sys -->> Bound2.
  Proof.
    admit.
  Qed.

  Lemma always_and_left2 : forall F1 F2 F3 F4,
      (|-- (([](F1 //\\ F2)) //\\ F4) -->> F3) ->
      (|-- (([]F1) //\\ ([]F2) //\\ F4) -->> F3).
  Proof. simpl; intuition. Qed.

  Lemma or_left1 : forall F1 F2 F3 F4,
      (|-- (F1 //\\ F3) -->> F4) ->
      (|-- (F2 //\\ F3) -->> F4) ->
      (|-- ((F1 \/ F2) //\\ F3) -->> F4).
  Proof. simpl; intuition. Qed.

  Lemma or_left2 : forall F1 F2 F3 F4,
      (|-- (F3 //\\ F1) -->> F4) ->
      (|-- (F3 //\\ F2) -->> F4) ->
      (|-- (F3 //\\ (F1 \/ F2)) -->> F4).
  Proof. simpl; intuition. Qed.

  Lemma ctrl2_refinement
  : |-- (Bound1 //\\ Ctrl2) -->> AbstractCtrl.
  Proof.
    unfold Ctrl2, AbstractCtrl.
    repeat apply or_left2.
    { apply or_right1.
      apply and_right.
      { apply ex_right. exists ("V" + "a" * d).
        solve_linear.
*)

  Theorem ctrl2_safety :
    |-- Ctrl2Sys -->> []Safe.
  Proof.
    apply imp_trans with (F2:=AbstractSys).
    - apply and_right.
      + apply and_left1. apply imp_id.
      + apply imp_strengthen with (F2:=Bound1 //\\ Bound2);
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
