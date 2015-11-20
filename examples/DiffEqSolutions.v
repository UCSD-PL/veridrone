Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.

Open Scope HP_scope.
Open Scope string_scope.

Definition sgl_int : Evolution :=
  fun st' => st' "y" = "v" //\\ st' "v" = 0 //\\ st' "t" = 1.

Lemma solve_sgl_int_aux1 :
  Continuous sgl_int
  |-- Exists y : R, "y" = y //\\
      Exists t : R, "t" = t //\\
                    "y"! = y + "v" * ("t"! - t) //\\
                    "t"! >= t.
Proof.
  tlaAssert (Exists y : R, "y" = y //\\
             Exists t : R, "t" = t //\\
                           "y"! = y + "v"! * ("t"! - t) //\\
                           "t"! >= t).
  { apply Exists_with_st with (t:="y"). intros.
    charge_intros. charge_split; [ charge_tauto | ].
    apply Exists_with_st with (t:="t"). intros.
    charge_intros. charge_split; [ charge_tauto | ].
    match goal with
      |- _ |-- ?GG => eapply diff_ind
                      with (Hyps:=TRUE)
                             (G:=unnext GG)
    end.
    - tlaIntuition.
    - tlaIntuition.
    - charge_tauto.
    - tlaIntuition.
    - charge_tauto.
    - solve_linear. subst. solve_linear.
    - restoreAbstraction. charge_tauto.
    - solve_linear. rewrite H1. rewrite H0.
      rewrite H3. solve_linear. }
  { eapply zero_deriv with (x:="v").
    - charge_tauto.
    - solve_linear.
    - tlaRevert. apply Lemmas.forget_prem.
      breakAbstraction. intuition.
      destruct H1. intuition. destruct H3.
      exists x. intuition. exists x0. subst.
      rewrite <- H0. solve_linear. }
Qed.

Lemma solve_sgl_int_aux2 :
  (Exists y : R, "y" = y //\\
   Exists t : R, "t" = t //\\
                 "y"! = y + "v" * ("t"! - t) //\\
                 "t"! >= t)
  |-- "y"! = "y" + "v" * ("t"! - "t") //\\ "t"! >= "t".
Proof.
  apply lexistsL. intros.
  solve_linear; destruct H1; solve_linear;
  subst; solve_linear.
Qed.

Lemma solve_sgl :
  Continuous sgl_int
  |-- "y"! = "y" + "v" * ("t"! - "t") //\\ "t"! >= "t".
Proof.
  rewrite solve_sgl_int_aux1. apply solve_sgl_int_aux2.
Qed.

Definition dbl_int : Evolution :=
  fun st' => st' "y" = "v" //\\ st' "v" = "a"
             //\\ st' "a" = 0 //\\ st' "t" = 1.

Lemma solve_dbl_int_aux1 :
  Continuous dbl_int
  |-- Exists y : R, "y" = y //\\
      Exists v : R, "v" = v //\\
      Exists t : R, "t" = t //\\
                    "y"! = y + v * ("t"! - t)
                           + (/2)%R*"a" * ("t"! - t)^^2 //\\
                    "v"! = v + "a" * ("t"! - t) //\\
                    "t"! >= t.
Proof.
  tlaAssert
    (Exists y : R, "y" = y //\\
     Exists v : R, "v" = v //\\
     Exists t : R, "t" = t //\\
                   "y"! = y + v * ("t"! - t)
                          + (/2)%R*"a"! * ("t"! - t)^^2 //\\
                   "v"! = v + "a"! * ("t"! - t) //\\
                   "t"! >= t).
  { apply Exists_with_st with (t:="y"). intros.
    charge_intros. charge_split; [ charge_tauto | ].
    apply Exists_with_st with (t:="v"). intros.
    charge_intros. charge_split; [ charge_tauto | ].
    apply Exists_with_st with (t:="t"). intros.
    charge_intros. charge_split; [ charge_tauto | ].
    charge_split.
    { match goal with
        |- _ |-- ?GG => eapply diff_ind
                        with (G:=unnext GG)
                               (Hyps:="v"=x0+"a"*("t"-x1))
      end; try solve [ tlaIntuition | charge_tauto ].
      - match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=TRUE)
                                 (G:=unnext GG)
        end; try solve [ tlaIntuition | charge_tauto ].
        solve_linear. rewrite H0. rewrite H2.
        rewrite H4. solve_linear.
      - solve_linear. subst. solve_linear.
      - solve_linear. subst. solve_linear.
      - solve_linear. rewrite H1. rewrite H.
        rewrite H2. rewrite H4. solve_linear. }
    { match goal with
        |- _ |-- ?GG => eapply diff_ind
                        with (Hyps:=TRUE)
                               (G:=unnext GG)
      end; try solve [ tlaIntuition | charge_tauto ].
      - solve_linear. subst. solve_linear.
      - solve_linear. rewrite H0. rewrite H2.
        rewrite H4. solve_linear. } }
  { eapply zero_deriv with (x:="a").
    - charge_tauto.
    - solve_linear.
    - tlaRevert. apply Lemmas.forget_prem.
      breakAbstraction. intuition.
      destruct H1. intuition. destruct H3.
      intuition. destruct H4.
      exists x. intuition. exists x0. intuition.
      exists x1. subst. rewrite <- H0. solve_linear. }
Qed.

Lemma solve_dbl_int_aux2 :
  (Exists y : R, "y" = y //\\
   Exists v : R, "v" = v //\\
   Exists t : R, "t" = t //\\
                 "y"! = y + v * ("t"! - t)
                        + (/2)%R*"a" * ("t"! - t)^^2 //\\
                 "v"! = v + "a" * ("t"! - t) //\\
                 "t"! >= t)
  |-- "y"! = "y" + "v" * ("t"! - "t")
             + (/2)%R*"a" * ("t"! - "t")^^2 //\\
      "v"! = "v" + "a" * ("t"! - "t") //\\
      "t"! >= "t".
Proof.
  apply lexistsL. intros.
  solve_linear; destruct H1; intuition;
  destruct H2; intuition; subst; solve_linear.
Qed.

Lemma solve_dbl_int :
  Continuous dbl_int
  |-- "y"! = "y" + "v" * ("t"! - "t")
             + (/2)%R*"a" * ("t"! - "t")^^2 //\\
      "v"! = "v" + "a" * ("t"! - "t") //\\
      "t"! >= "t".
Proof.
  rewrite solve_dbl_int_aux1. apply solve_dbl_int_aux2.
Qed.