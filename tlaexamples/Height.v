Require Import Coq.micromega.Psatz.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.ProofRules.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

Section HeightCtrl.

  Variable d : R.
  Hypothesis Hd : (d > 0)%R.

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
        Unchanged (["v", "H", "T", "pc"]))
    \/ ("pc" = 1 /\ Ctrl /\ "pc"! = 0 /\
        Unchanged (["h", "t", "H", "T"])).

  Definition Init : Formula :=
    (--1 = "v" \/ "v" = 1) /\
    --d <= "h" <= d /\
    "t" = 0 /\ "T" = 0 /\ "pc" = 0 /\
    "H" = "h".

  Definition Safe : Formula :=
    --2*d <="h" <= 2*d.

  Definition Ind_Inv : Formula :=
    (("pc" = 0 /\ "v" = 1) --> (--2*d <= "h" <= d)) /\
    (("pc" = 0 /\ "v" = --1) --> (--d <= "h" <= 2*d)) /\
    (("pc" = 1 /\ "v" = 1) --> (--2*d <= "H" <= d /\
                                0 <= "h"-"H" <= "t"-"T")) /\
    (("pc" = 1 /\ "v" = --1) --> (--d <= "H" <= 2*d /\
                                  0 <= "H"-"h" <= "t"-"T")) /\
    0 <= "t"-"T" <= d /\
    ("v"=--1 \/ "v" = 1) /\
    ("pc"=0 \/ "pc"=1).

(*
    (("pc"=0 /\ "v"=1) --> ("h" <= d /\ --2*d <= "h")) /\
    (("pc"=0 /\ "v"=--1) --> (--d <= "h" /\ "h" <= 2*d)) /\
    (("pc"=1 /\ "v"=1) --> (d-("t"-"T") <= 2*d-"h" /\
                            d-("t"-"T") <= 2*d+"h")) /\
    (("pc"=1 /\ "v"=--1) --> (("t"-"T")-d <= 2*d-"h" /\
                              ("t"-"T")-d <= 2*d+"h")) /\
    "t"-"T" <= d /\ 0 <= "t"-"T" /\
    ("v"=--1 \/ "v" = 1) /\
    ("pc"=0 \/ "pc"=1).
*)

  Lemma ind_inv_init : |- Init --> Ind_Inv.
  Proof.
    simpl; intros; unfold eval_comp in *;
    simpl in *; intuition; try psatzl R.
  Qed.

  Lemma ind_inv_safe : |- Ind_Inv --> Safe.
  Proof.
    simpl; intros; unfold eval_comp in *;
    simpl in *; intuition; try psatzl R.
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
        simpl; intros; intuition; unfold eval_comp in *;
        simpl in *; try psatzl R.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
      + apply always_imp. apply ind_inv_safe.
  Qed.

End HeightCtrl.
