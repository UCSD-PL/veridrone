Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

Section HeightCtrl.

  Variable d : R.
  (* The following hypothesis is not necessary
     for the safety property, but it's necessary
     for ensuring that non-Zeno behaviors are
     possible. *)
  Hypothesis Hd : (d > 0)%R.
  (* We don't have division in the language, so we
     just add a parameter, which is the inverse of
     d *)
  Variable dinv : R.
  Hypothesis Hdinv : (@eq R (d * dinv) 1)%R.

  Definition Read : Formula :=
    "T"! = "t" /\ "H"! = "h".

  Definition Evolve : Formula :=
    Continuous (["h"' ::= "v",
                 "v"' ::= 0,
                 "t"' ::= 1,
                 "H"' ::= 0,
                 "T"' ::= 0]).

  Definition Ctrl : Formula :=
    "v"! = --"H"*dinv.

  Definition Next : Formula :=
       (Evolve /\ "t"! <= "T" + d)
    \/ (Ctrl /\ Read /\ Unchanged (["h", "t"])).

  Definition Init : Formula :=
       (   ("v" >= 0 /\ --d <= "h" <= d*(1-"v"))
        \/ ("v" <= 0 /\ --d*(1+"v") <= "h" <= d))
    /\ "t" = 0 /\ "T" = 0
    /\ "H" = "h" /\ --1 <= "v" <= 1.

  Definition Safe : Formula :=
    --d <="h" <= d.

  Definition Ind_Inv : Formula :=
    ("v" >= 0 -->
              (--d <= "H" <= d*(1-"v") /\
               0 <= "h"-"H" <= "v"*("t"-"T"))) /\
    ("v" <= 0 -->
              (--d*(1+"v") <= "H" <= d /\
               0 <= "H"-"h" <= "v"*("T"-"t"))) /\
    0 <= "t"-"T" <= d /\
    --1 <= "v" <= 1.

  Lemma ind_inv_init : |- Init --> Ind_Inv.
  Proof. Time solve_linear; solve_nonlinear. Qed.

  Lemma ind_inv_safe : |- Ind_Inv --> Safe.
  Proof. Time solve_linear.
         Time solve_nonlinear.
         Time solve_nonlinear.
  Time Qed.

  Lemma safety :
    |- (Init /\ []Next) --> []Safe.
  Proof.
    apply imp_trans with (F2:=Ind_Inv /\ []Next).
    - apply and_right.
      + apply and_left1. apply ind_inv_init.
      + apply and_left2. apply imp_id.
    - apply imp_trans with (F2:=[]Ind_Inv).
      + apply inv_discr_ind; auto.
        unfold Next, Evolve.
        Time prove_inductive.
        (* Unsolved goals here. *)
      + apply always_imp. apply ind_inv_safe.
  Qed.

End HeightCtrl.