Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.ProofRules.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Lemma arith_fact : forall (d h:R),
  (( h >= -d) /\ ( h <= d))%R ->  (d <= (2 * d) + h)%R.
Proof.
  intros d h H. inversion H. 
  apply Rplus_ge_compat_l with d h (- d)%R in H0. 
  rewrite  Rplus_opp_r  in H0.
  apply Rplus_ge_compat_l with d (d+h)%R 0%R in H0.
  replace (d + 0)%R with d%R in H0.
  apply Rge_le in H0. 
  rewrite <- Rplus_assoc in H0.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l. 
  apply H0.
  rewrite Rplus_0_r. reflexivity.
Qed.

Open Scope HP_scope.
Open Scope string_scope.

Section HeightCtrl.

  Variable d : time.

  Definition Read : Formula :=
    "T"! = "t" /\ "H"! = "h".

  Definition Evolve : Formula :=
    Continuous (["h"' ::= "v"]) d "t".

  Definition Ctrl : Formula :=
       ("H" < 0  /\ "v"! = 1)
    \/ ("H" >= 0 /\ "v"! = --1).

  Definition Next : Formula :=
       ("pc" = 0 /\ Read /\ "pc"! = 1 /\
        Unchanged (["h", "t", "v"]))
    \/ ("pc" = 1 /\ Evolve /\
        Unchanged (["v", "H", "T"]))
    \/ ("pc" = 1 /\ Ctrl /\ "pc"! = 0 /\
        Unchanged (["h", "t", "v"])).

  Definition Init : Formula :=
    (--1 = "v" \/ "v" = 1) /\
    --d <= "h" /\ "h" <= d /\
    "t" = 0 /\ "T" = 0 /\ "pc" = 0.

  Definition Safe : Formula :=
    --2*d <="h" /\ "h" <= 2*d.

  Definition Ind_Inv : Formula :=
    ("v"=1 --> d-("t"-"T") <= 2*d-"h") /\
    ("v"=--1 --> d-("t"-"T") <= 2*d+"h") /\
    "t"-"T" <= d /\
    (--1 = "v" \/ "v" = 1).

  Lemma ind_inv_init : |- Init --> Ind_Inv.
  Proof.
    simpl. intros. decompose [and or] H;
    unfold eval_comp in *; simpl in *;
    rewrite H3; rewrite H4; repeat split; intros.
    - rewrite <- H2 in H5. contradict H5.
      (* -1 <> 1 *) admit.
    - (* -d <= h <= d -> d <= 2d + h *)
      (* need to use arith_fact lemma but
         first need to simpl (0-0) *)
      admit.
    - destruct d. simpl. rewrite Rminus_0_r. auto.
    - left; auto.
    - (* -d <= h <= d -> d <= 2d + h *) admit.
    - rewrite H2 in H5. contradict H5.
      (* 1 <> -1 *) admit.
    - destruct d. simpl. rewrite Rminus_0_r. auto.
    - right; auto.
  Qed.

  Lemma ind_inv_safe : |- Ind_Inv --> Safe.
  Proof.
    simpl. intros. decompose [and] H; clear H.
    destruct H4; unfold eval_comp in *;
    simpl in *; split.
    - symmetry in H. apply H2 in H.
      admit.
    - symmetry in H. apply H2 in H.
      admit.
    - apply H0 in H.
      admit.
    - apply H0 in H.
      admit.
  Qed.

  Lemma safety :
    |- (Init /\ []Next) --> []Safe.
  Proof.
    apply imp_trans with (F2:=Ind_Inv /\ []Next).
    - apply and_right.
      + apply and_left1. apply ind_inv_init.
      + apply and_left2. apply imp_id.
    - apply imp_trans with (F2:=[]Ind_Inv).
      + apply inv_discr_ind; auto.
        
      + apply always_imp. apply ind_inv_safe.
  Qed.

End HeightCtrl.
