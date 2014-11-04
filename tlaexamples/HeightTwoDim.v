(*two dimensional height *)
Require Import Syntax.
Require Import Semantics.
Require Import Lib.
Require Import ProofRules.
Require Import Tactics.
Require Import Coq.Strings.String.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.
Section HeightTwoDimensionCtrl.

Variable dx : R.
Variable dy : R.
Hypothesis Hdx : (dx > 0)%R.
Hypothesis Hdy : (dy > 0)%R.
Definition Read (dimension:string): Formula :=
("T"++dimension)! = "t" /\ ("H"++dimension)! = "h"++dimension.

Definition Evolve : Formula :=
Continuous ([ "hx" ' ::= "vx",
              "hy" ' ::= "vy",
               "vx"' ::=  0,
               "vy"' ::=  0,
               "t"'  ::=1,
               "Hx"' ::=0,
               "Hy"' ::=0,
               "Tx"' ::=0,
               "Ty"' ::=0
                ]).



Definition Ctrl (dimension:string): Formula :=
("H"++dimension < 0 /\ ("v"++dimension)! = 1)
\/ (("H"++dimension) >= 0 /\ ("v"++dimension)! = --1).


Definition Next : Formula :=
(Evolve /\ "t"! <= "Tx" + dx /\ "t"! <="Ty"+dy)
\/ (Ctrl "x" /\ Read "x"  /\ Unchanged (["hx","hy","t","Ty","vy","Hy"])) \/ 
(Ctrl "y" /\ Read "y" /\ Unchanged (["hx","hy","t","Tx","vx","Hx"])).

Definition Init : Formula :=
(--1 = "vx" \/ "vx" = 1) /\ (--1 = "vy" \/ "vy" = 1) /\
(--dx <= "hx" <= dx) /\ (--dy <= "hy" <=dy) /\ "t"="Tx" /\ ("Tx" =0 /\ "Ty" =0) 
/\ (("Hx" = "hx") /\ ("Hy" = "hy")).



Definition Safe : Formula :=
(--2*dx <="hx" <= 2*dx) /\ (--2*dy <="hy" <= 2*dy).

Definition Ind_Inv : Formula :=
 ("vx" = 1 --> (--2*dx <= "Hx" <= dx /\
0 <= "hx"-"Hx" <= "t"-"Tx")) /\
("vy" = 1 --> (--2*dy <= "Hy" <= dy /\
0 <= "hy"-"Hy" <= "t"-"Ty")) /\ 
 
("vx" = --1 --> (--dx <= "Hx" <= 2*dx /\
0 <= "Hx"-"hx" <= "t"-"Tx")) /\
("vy" = --1 --> (--dy <= "Hy" <= 2*dy /\
0 <= "Hy"-"hy" <= "t"-"Ty")) /\
 0 <= "t"-"Tx" <= dx /\
 0 <= "t"-"Ty" <= dy /\
  ("vx"=--1 \/ "vx" = 1) /\
   ("vy"=--1 \/ "vy" = 1).



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
        Time prove_inductive.
      + apply always_imp. apply ind_inv_safe.
Qed.

End HeightTwoDimensionCtrl.