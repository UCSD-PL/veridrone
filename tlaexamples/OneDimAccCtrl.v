Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Import LibNotations.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import TLA.ArithFacts.
Require Import TLA.Substitution.
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
 
  Lemma ubH_st : is_st_term ubH = true.
  Proof. reflexivity. Qed.
  Lemma ubV_st : is_st_term ubV = true.
  Proof. reflexivity. Qed.
  Lemma ubv_st : is_st_term ubv = true.
  Proof. reflexivity. Qed.

  Lemma ubH_unch : forall t1 t2,
    |- Unchanged (["a", "H", "V", "T"])
       -->
       (subst_term_term 
          (subst_term_term (next_term ubH)
                           (next_term t1) "h" true)
          (next_term t2) "v" true) =
       (subst_term_term 
          (subst_term_term ubH t1 "h" false)
          t2 "v" false).
  Proof. solve_linear. Qed.
  Lemma ubV_unch : forall t1 t2,
    |- Unchanged (["a", "H", "V", "T"])
       -->
       (subst_term_term 
          (subst_term_term (next_term ubV)
                           (next_term t1) "h" true)
          (next_term t2) "v" true) =
       (subst_term_term 
          (subst_term_term ubV t1 "h" false)
          t2 "v" false).
  Proof. solve_linear. Qed.
  Lemma ubv_unch : forall t1 t2,
    |- Unchanged (["a", "H", "V", "T"])
       -->
       (subst_term_term 
          (subst_term_term (next_term ubv)
                           (next_term t1) "h" true)
          (next_term t2) "v" true) =
       (subst_term_term 
          (subst_term_term ubv t1 "h" false)
          t2 "v" false).
  Proof. solve_linear. Qed.

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

Definition Init : Formula := AbstractCtrl.AbstractCtrl.Init.

Definition Safe : Formula :=
  "h" <= ub.

Lemma refinement :
  |- (Init /\ []Next)
       --> (AbstractCtrl.AbstractCtrl.Init /\
            []AbstractCtrl.AbstractCtrl.Next).
Proof.
  pose proof Hd. pose proof Hvt.
  apply and_right.
  - apply and_left1. apply imp_id.
  - apply and_left2. apply Always_imp.
    repeat apply or_left.
    + unfold Evolve. apply or_right1.
      repeat apply and_right.
      * apply and_left1. apply imp_id.
      * apply and_left2. apply imp_id.
(*      * match goal with
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
        end; solve_linear.*)
    + apply or_right2.
      apply and_right.
      * apply and_left1.
        { repeat apply or_left;
          try apply imp_right;
          try solve [unfold amax; solve_linear].
          - apply imp_strengthen with (F2:="h" < ubH);
            [ solve_linear | ].
            apply imp_strengthen with (F2:="v" < vt + ubV);
              [ solve_linear | ].
            solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.InvParams.d,
              ub, ubV, ubv, ubv_r, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H10 in H13.
              unfold amax, ubv_r in *.
              repeat rewrite Rplus_assoc.
              match goal with
                | [ H : Rlt ?e1 ?e2 |- Rle (Rplus ?e1 ?e3) _ ]
                  => apply Rle_trans with (r2:=Rplus e2 e3);
                    [ solve_linear | clear H ]
              end.
              repeat rewrite Rplus_assoc.
              repeat apply Rplus_le_compat_l.
              clear H2 H3 H7 H10 H8 H9 H11 H12.
              solve_nonlinear.
            + unfold ubv_r in *.
              rewrite H10 in H13.
              clear H2 H3 H7 H10 H8 H11 H12.
              solve_nonlinear.
            + unfold ubv_r in *.
              clear H2 H3 H6 H7 H11 H10 H8 H9 H12.
              solve_nonlinear.
          - apply imp_strengthen with (F2:="h" < ubH);
            [ solve_linear | ].
            solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.InvParams.d,
              ub, ubV, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H9 in H12.
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
              rewrite H9 in H12.
              assert (hd tr "v" - x <= 0)%R by solve_linear.
              clear H8.
              unfold ubv_r in *.
              R_simplify. simpl.
              apply Rminus_le.
              R_simplify. simpl.
              rewrite Rmult_comm.
              apply Rmult_le_0; solve_linear.
              generalize dependent (hd tr "v").
              intros. clear dependent tr.
              solve_nonlinear.
            + unfold ubv_r in *.
              clear H4 H3 H2 H6 H9 H7 H8 H10 H11.
              solve_nonlinear.
          - apply imp_strengthen with (F2:="v" < --vt + ubV);
              [ solve_linear | ].
            solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.InvParams.d,
              ub, ubV, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H9 in H12.
              assert (hd tr "v" + 1 * x < 0)%R
                by solve_linear.
              solve_linear.
            + rewrite H9 in H12. clear H10.
              unfold ubv_r in *.
              solve_nonlinear.
            + clear H3 H2 H6 H9 H7 H8 H10 H11.
              unfold ubv_r in *.
              solve_nonlinear.
            + unfold ubv_r in *.
              solve_nonlinear.
          - solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.InvParams.d,
              ub, ubV, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H8 in H11.
              assert (0 <= hd tr "v")%R by solve_linear.
              unfold amax, ubv_r in *. clear H9.
              solve_nonlinear.
            + rewrite H8 in H11. clear H9.
              destruct (Rle_dec 0 (hd tr "v"))%R.
              * unfold amax, ubv_r in *. solve_nonlinear.
              * assert (hd tr "v" * x + / 2 * (0 - 1) *
                                        (x * (x * 1))
                      <= 0)%R
                       by (generalize dependent (hd tr "v");
                           intros; clear dependent tr;
                           solve_nonlinear).
                solve_linear.
            + unfold ubv_r in *. solve_nonlinear. }
      * solve_linear.
Qed.

Lemma safety :
  |- (Init /\ []Next) --> []Safe.
Proof.
  apply imp_trans
  with (F2:=AbstractCtrl.AbstractCtrl.Init /\
            []AbstractCtrl.AbstractCtrl.Next).
  - apply refinement.
  - apply AbstractCtrl.safety.
Qed.
