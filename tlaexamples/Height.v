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

  Definition Read : Formula :=
    "T"! = "t" /\ "H"! = "h".

  Definition Evolve : Formula :=
    Continuous (["h"' ::= "v",
                 "v"' ::= 0,
                 "t"' ::= 1,
                 "H"' ::= 0,
                 "T"' ::= 0,
                 "pc"' ::= 0]).

  Definition Ctrl : Formula :=
       ("H" < 0  /\ "v"! = 1)
    \/ ("H" >= 0 /\ "v"! = --1).

  Definition Next : Formula :=
       ("pc" = 0 /\ Read /\ "pc"! = 1 /\
        Unchanged (["h", "t", "v"]))
    \/ ("pc" = 1 /\ Evolve /\ "t"! <= "T" + d)
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

  Lemma ind_inv_init : |- Init --> Ind_Inv.
  Proof. solve_linear. Qed.

  Lemma ind_inv_safe : |- Ind_Inv --> Safe.
  Proof. solve_linear. Qed.

  Lemma safety :
    |- (Init /\ []Next) --> []Safe.
  Proof.
    apply imp_trans with (F2:=Ind_Inv /\ []Next).
    - apply and_right.
      + apply and_left1. apply ind_inv_init.
      + apply and_left2. apply imp_id.
    - apply imp_trans with (F2:=[]Ind_Inv).
      + apply inv_discr_ind; auto. unfold Next, Evolve.
        Time repeat apply or_next;
          repeat first [ apply and_right |
                         apply imp_right ];
        match goal with
          | [ |- context [Continuous ?eqs] ]
              => pose "Continuous"; extract_unchanged eqs;
                 match goal with
                   | [ |- context [next_term (TermC (VarC "pc")) =
                                   next_term (TermC (ConstC (NatC 1)))] ] =>
                     match goal with
                       | [ |- context [next_term (TermC (VarC "v")) = next_term ?e] ] =>
                         abstract (prove_diff_inv ("v" = e);
                                   match goal with
                                     | [ |- (|- (?I /\ Continuous eqs) --> next ?I) ] =>
                                       extract_unchanged eqs; solve_linear
                                     | [ |- _ ] =>
                                       solve_linear
                                   end)
                     end
                   | [ |- _ ] =>
                     try abstract solve [solve_linear |
                                         prove_diff_inv TRUE; solve_linear]
                 end
          | [ |- _ ]
              => pose "Discrete";
                 try abstract solve_linear
        end.
      + apply always_imp. apply ind_inv_safe.
  Qed.

End HeightCtrl.
