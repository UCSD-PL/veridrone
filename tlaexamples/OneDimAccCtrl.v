Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import TLA.ArithFacts.
Require Import Modules.AbstractOneDimAccCtrl.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

Module Params <: CtrlParameters.

  Variable d : R.
  Hypothesis Hd : (d > 0)%R.
  Variable vt : R.
  Hypothesis Hvt : (vt > 2*d)%R.

  Definition amax : R := 1%R.
  Definition Hamax : (amax > 0)%R.
  Proof. solve_linear. Qed.

  Definition ubV : Term := d.
  Definition ubv_r : R := (vt + 2*d)%R.
  Definition ubv : Term := ubv_r.
  Definition ubH_r : R := (ubv_r*d + d*d*/2)%R.
  Definition ubH : Term := ubH_r.
  Definition ub : R := (ubH_r + ubH_r +
                        ubv_r*ubv_r*/2)%R.
 
  Definition ubH_st : is_st_term ubH = true := Logic.eq_refl _.
  Definition ubV_st : is_st_term ubV = true := Logic.eq_refl _.
  Definition ubv_st : is_st_term ubv = true := Logic.eq_refl _.

End Params.

Import Params.

Module AbstractCtrl := AbstractAccDimCtrl(Params).

Definition Read : Formula :=
  "T"! = "t" /\ "H"! = "h" /\ "V"! = "v".

Definition Evolve : Formula :=
  Continuous (["h"' ::= "v",
               "v"' ::= "a",
               "a"' ::= 0,
               "t"' ::= 1,
               "H"' ::= 0,
               "T"' ::= 0,
               "V"' ::= 0]).

Definition Ctrl : Formula :=
     ("H" < 0  /\ "V" < vt /\ "a"! = 1)
  \/ ("H" < 0  /\ "V" >= vt /\ "a"! = --1)
  \/ ("H" >= 0  /\ "V" < --vt /\ "a"! = 1)
  \/ ("H" >= 0  /\ "V" >= --vt /\ "a"! = --1).

Definition Next : Formula :=
     (Evolve /\ "t"! <= "T" + d)
  \/ (Ctrl /\ Read /\ Unchanged (["h", "v", "t"])).

Definition Init : Formula := AbstractCtrl.Ind_Inv.

Definition Safe : Formula :=
  "h" <= ub.

Lemma refinement :
  |- (Init /\ []Next)
       --> (AbstractCtrl.Init /\ []AbstractCtrl.Next).
Proof.
  pose Hd. pose Hvt.
  apply and_right.
  - apply and_left1. apply imp_id.
  - apply and_left2. apply always_imp.
    repeat apply or_left.
    + unfold Evolve. apply or_right1.
      repeat apply and_right.
      * apply and_left1. apply imp_id.
      * apply and_left2. apply imp_id.
      * match goal with
          | [ |- context [Continuous ?deqs] ] =>
            apply unchanged_continuous with (eqs:=deqs)
        end; solve_linear.
      * match goal with
          | [ |- context [Continuous ?deqs] ] =>
            apply unchanged_continuous with (eqs:=deqs)
        end; solve_linear.
      * match goal with
          | [ |- context [Continuous ?deqs] ] =>
            apply unchanged_continuous with (eqs:=deqs)
        end; solve_linear.
    + apply or_right2.
      apply and_right.
      * apply and_left1.
        { apply and_right; repeat apply or_left; try apply imp_right;
          try solve [unfold amax; solve_linear].
          - apply imp_strengthen with (F2:="h" < ubH);
            [ solve_linear | ].
            apply imp_strengthen with (F2:="v" < vt + ubV);
              [ solve_linear | ].
            solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.inv2, ub, ubV, ubv, ubv_r, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H8 in H10. clear H8 H0 H1 H5 H7 H11 H6.
              unfold amax, ubv_r in *. repeat rewrite Rplus_assoc.
              match goal with
                | [ H : Rlt ?e1 ?e2 |- Rle (Rplus ?e1 ?e3) _ ]
                  => apply Rle_trans with (r2:=Rplus e2 e3);
                    [ solve_linear | clear H ]
              end.
              Time solve_nonlinear.
            + clear H10 H11. unfold ubv_r in *. Time solve_nonlinear.
            + clear H11. unfold ubv_r in *. Time solve_nonlinear.
          - apply imp_strengthen with (F2:="h" < ubH);
            [ solve_linear | ].
            solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.inv2, ub, ubV, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H7 in H9.
              assert (0 <= hd tr "v")%R by solve_linear.
              intuition. eapply Rle_trans; eauto.
              R_simplify; solve_linear. unfold amax. simpl.
              repeat rewrite Rmult_1_r.
              R_simplify. simpl. solve_linear.
            + repeat rewrite Rplus_assoc.
              match goal with
                | [ H : Rlt ?e1 ?e2 |- Rle (Rplus ?e1 ?e3) _ ]
                  => apply Rle_trans with (r2:=Rplus e2 e3);
                    [ solve_linear | clear H ]
              end.
              rewrite H7 in H9.
              assert (hd tr "v" - x <= 0)%R by solve_linear.
              clear H8.
              unfold ubv_r in *.
              R_simplify. simpl.
              apply Rminus_le.
              R_simplify. simpl.
              rewrite Rmult_comm.
              apply Rmult_le_0; solve_linear.
              clear H10. generalize dependent (hd tr "v").
              intros. clear dependent tr.
              Time solve_nonlinear.
            + unfold ubv_r in *. Time solve_nonlinear.
          - apply imp_strengthen with (F2:="v" < --vt + ubV);
              [ solve_linear | ].
            solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.inv2, ub, ubV, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H7 in H9.
              assert (hd tr "v" + 1 * x < 0)%R by solve_linear.
              solve_linear.
            + rewrite H7 in H9. clear H10.
              unfold ubv_r in *.
              Time solve_nonlinear.
            + clear H10. unfold ubv_r in *.
              solve_linear.
            + clear H10. unfold ubv_r in *.
              Time solve_nonlinear.
          - solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.inv2, ub, ubV, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H6 in H8.
              assert (0 <= hd tr "v")%R by solve_linear.
              unfold amax, ubv_r in *. clear H9.
              Time solve_nonlinear.
            + rewrite H6 in H8. clear H9.
              destruct (Rle_dec 0 (hd tr "v"))%R.
              * unfold amax, ubv_r in *. Time solve_nonlinear.
              * assert (hd tr "v" * x + / 2 * (0 - 1) * (x * (x * 1))
                      <= 0)%R
                       by (generalize dependent (hd tr "v"); intros; clear dependent tr;
                           clear r0; solve_nonlinear).
                solve_linear.
            + unfold ubv_r in *. Time solve_nonlinear. }
      * solve_linear.
Qed.

Lemma safety :
  |- (Init /\ []Next) --> []Safe.
Proof.
  apply imp_trans
  with (F2:=AbstractCtrl.Init /\ []AbstractCtrl.Next).
  - apply refinement.
  - apply AbstractCtrl.safety.
Qed.
