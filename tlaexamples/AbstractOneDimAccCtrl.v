Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import TLA.ArithFacts.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

Module Type CtrlParameters.

  Parameter ub : R.
  Parameter d : R.
  Parameter Hd : (d > 0)%R.
 
  Parameter ubV : Term.
  Parameter ubH : Term.
  Parameter amax : R.
  Parameter Hamax : (amax > 0)%R.
 
  Parameter ubH_st : is_st_term ubH = true.
  Parameter ubV_st : is_st_term ubV = true. 
 
End CtrlParameters.


Module AbstractAccDimCtrl (Import Params : CtrlParameters).

  Definition inv2 : R := (/2)%R.
  Definition amaxinv : R := (/amax)%R.
 
  Definition sdist (v:Term) : Term :=
    v^^2*inv2*amaxinv.

  Definition tdist (v:Term) (a:Term) (t:Term) : Term :=
    v*t + inv2*a*t^^2.

  Definition tdiff : Term :=
    "t"-"T".

  Definition Ctrlable : Formula :=
    (0 <= "v" --> "h" + (sdist "v") <= ub) /\
    "h" <= ub /\
    "h" - "H" <= ubH /\
    "v" - "V" <= ubV.

  Definition Ctrl : Formula :=
    --amax <= "a"! /\
    (Ctrlable
      -->
      Forall R
      (fun t =>
         0 <= t <= d -->
         (0 <= "v" + "a"!*t -->
          "h" + (tdist "v" "a"! t) +
          (sdist ("v" + "a"!*t)) <= ub) /\
         ("v" + "a"!*t < 0 -->
           "h" + (tdist "v" "a"! t) <= ub) /\
         "a"!*t <= next_term ubV /\
         tdist "v" "a"! t <= next_term ubH)).

  Definition Evolve : Formula :=
    Continuous (["h"' ::= "v",
                 "v"' ::= "a",
                 "a"' ::= 0,
                 "t"' ::= 1,
                 "H"' ::= 0,
                 "T"' ::= 0,
                 "V"' ::=0
               ]).
 
  Definition Read : Formula :=
    "T"! = "t" /\ "H"! = "h" /\ "V"! = "v".
 
  Definition Next : Formula :=
       (Evolve /\ "t"! <="T" + d /\
        next_term ubH = ubH /\
        next_term ubV = ubV)
    \/ (Ctrl /\ Read /\
        Unchanged (["h","v","t"])).
 
  Definition Ind_Inv : Formula :=
    "h" - "H" = tdist "V" "a" tdiff /\
    "v" - "V" = "a"*tdiff /\
    (Forall R
            (fun t =>
               0 <= t <= d -->
               (0 <= "V" + "a"*t -->
                "H" + tdist "V" "a" t + (sdist ("V" + "a"*t)) <= ub) /\
               ("V" + "a"*t < 0 -->
                "H" + tdist "V" "a" t <= ub) /\
               "a"*t <= ubV /\
               tdist "V" "a" t <= ubH)) /\
    --amax <= "a" /\
    0 <= "t" - "T" <= d.
 
  Definition Safe : Formula :=
    "h" <= ub.
 
  Definition Init : Formula := Ind_Inv.
 
  Lemma ind_inv_init : |- Init --> Ind_Inv.
  Proof.
    apply imp_id.
  Qed.     

  Ltac rewrite_h_v :=
    match goal with
      | [ H : eq (Rminus (hd ?tr "h") (hd ?tr "H")) ?e |- _ ]
          => assert (eq (hd tr "h") (hd tr "H" + e))%R as Heq
                    by solve_linear; rewrite Heq in *; clear Heq H
    end;
    match goal with
      | [ H : eq (Rminus (hd ?tr "v") (hd ?tr "V")) ?e |- _ ]
          => assert (eq (hd tr "v") (hd tr "V" + e))%R as Heq
                    by solve_linear; rewrite Heq in *; clear Heq H
    end.


  Lemma ind_inv_safe : |- Ind_Inv --> Safe.
  Proof.
    pose proof Hd.
    pose proof Hamax.
    solve_linear.
    generalize dependent (hd tr "t" - hd tr "T")%R.
    intros. unfold inv2, amaxinv in *.
    rewrite_h_v. pose proof (H3 r).
    destruct (Rle_dec R0 (hd tr "V" + hd tr "a" * r))%R;
      solve_linear.
    eapply Rle_trans; eauto.
    rewrite Rplus_assoc at 1.
    apply Rplus_le_compat_l.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat_l.
    apply Rmult_0_le; solve_linear.
    apply Rmult_0_le; solve_linear.
    apply pow_0_le.
  Qed.

  Lemma ind_inv_ctrlable : |- Ind_Inv --> Ctrlable.
  Proof.
    pose proof Hamax.
    simpl; unfold eval_comp; simpl; unfold amaxinv, inv2; intuition;
    rewrite_h_v; generalize dependent (hd tr "t" - hd tr "T")%R;
    intros; pose proof (H2 r); solve_linear.
    destruct (Rle_dec R0 (hd tr "V" + hd tr "a" * r))%R;
      solve_linear.
    eapply Rle_trans; eauto.
    rewrite Rplus_assoc at 1.
    apply Rplus_le_compat_l.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat_l.
    apply Rmult_0_le; solve_linear.
    apply Rmult_0_le; solve_linear.
    apply pow_0_le.
  Qed.

  Lemma safety :
    |- (Init /\ []Next) --> []Safe.
  Proof.
    apply imp_trans with (F2:=Ind_Inv /\ []Next).
    - apply and_right.
      + apply and_left1. apply ind_inv_init.
      + apply and_left2. apply imp_id.
    - apply imp_trans with (F2:=[]Ind_Inv).
      + apply inv_discr_ind.
        simpl. rewrite ubH_st.
        rewrite ubV_st. simpl. tauto.
        unfold Next, Evolve. pose proof Hd.
        pose proof Hamax.
        Time prove_inductive.
        * match goal with
            | [ |- context [Continuous ?deqs] ] =>
              match goal with 
                | [ |-( |- _ --> ?g)] => 
                  eapply diff_ind
                  with (cp:=deqs) (G:=unnext g)
                                  (Hyps:="v"= "V"+ "a"*("t"-"T"))
              end
          end; try solve [simpl; intuition | solve_linear].
          match goal with
            | [ |- context [Continuous ?deqs1] ] =>
              match goal with 
                | [ |- (|- _ --> ?g1)] => 
                  eapply diff_ind
                  with (cp:=deqs1) (G:=unnext g1) (Hyps:=TRUE)
              end
          end; try solve [intuition | solve_linear].
          solve_linear. unfold inv2. solve_linear.
        * match goal with
            | [ |- context [Continuous ?deqs] ] =>
              apply unchanged_continuous with (eqs:=deqs)
          end; solve_linear;
          specialize (H10 x);
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H in *
                 end; intuition.
        * solve_linear;
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H
                 end; solve_linear.
        * solve_linear;
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H
                 end; solve_linear.
        * apply imp_strengthen with (F2:=Ctrlable).
          { apply and_left1. apply ind_inv_ctrlable. }
          { simpl; unfold eval_comp; simpl; intuition;
            repeat match goal with
                     | [ H : @eq R _ _ |- _ ] =>
                       rewrite H; try rewrite H in H10
                   end;
            specialize (H18 x); intuition. }
      + apply always_imp. apply ind_inv_safe.
Qed. 
 
End AbstractAccDimCtrl.