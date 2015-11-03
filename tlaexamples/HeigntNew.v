Require Import Coq.micromega.Psatz.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Import LibNotations.
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
"H"! = "h".
Definition Evolve : Formula :=
Continuous (["h"' ::= "v",
"v"' ::= 0,
"t"' ::= 1,
"H"' ::= 0,
"H1"' ::=0,
"TC"' ::= 0,
"TR"' ::= 0]).

Definition Ctrl : Formula :=
("H1" < 0 /\ "v"! = 1 /\ "H1"! = "H") 
\/ ("H1" >= 0 /\ "v"! = --1 /\ "H1"!="H").


Definition Next : Formula :=
(Evolve /\ "t"! <= "TC" + d /\ "t"! <= "TR" + d)
\/ (Ctrl /\ "TC"! = "t" /\ Unchanged (["h", "t", "H", "TR"]))
\/ (Read /\ "TR"! = "t" /\ Unchanged (["h", "t", "v", "TC", "H1"])).




Definition Init : Formula :=
(--1 = "v" \/ "v" = 1) /\
--d <= "h" <= d /\
"t" = "TC" /\ "t" = "TR" /\ "H" = "h" /\ "H1" = "h".



Definition Safe : Formula :=
--3*d <="h" <= 3*d.

Notation "x <= y < z" :=
(And (Comp x y Le) (Comp y z Lt)) : HP_scope.

Notation "x < y <= z" :=
(And (Comp x y Lt) (Comp y z Le)) : HP_scope.

Definition Ind_Inv : Formula :=
(("v" = 1 /\ "h" < "H1") --> ((--3*d + ("TC"-"TR"+"d")) <= "H1" < 0) /\
(--("TC"-"TR"+"d") <= "h"-"H1" < 0 )) /\
(("v" = 1 /\ "h" >= "H1") --> (( --3*d <= "H1" <= (3*d - ("TC"-"TR"+2*d))) /\
( 0 <="h"-"H1"<= ("TC"-"TR"+ 2*d)))) /\
(("v" = --1 /\ "h" > "H1") --> (( 0 < "H1" <= (3*d - ("TC"-"TR"+d))) /\
(0 <"h"-"H1" <= ("TC" - "TR" +d)))) /\
(("v"= --1 /\ "h" <= "H1") --> (( (--3*d + ("TC"-"TR"+2*d) )<= "H1" <= 3*d) /\
(--("TC"- "TR" + 2*d) <= "h"-"H1" <= 0))) /\
("v"=--1 \/ "v" = 1).




Lemma or_left : 
forall F1 F2 F3,
(|- F1 --> F3) ->
(|- F2 --> F3) ->
(|- (F1 \/ F2) --> F3).
Proof. firstorder. Qed.

Lemma or_right1 :
forall F1 F2 F3,
(|- F1 --> F2) ->
(|- F1 --> (F2 \/ F3)).
Proof. firstorder. Qed.

Lemma or_right2 :
forall F1 F2 F3,
(|- F1 --> F3) ->
(|- F1 --> (F2 \/ F3)).
Proof. firstorder. Qed.

Lemma and_some:
forall L1 L2 L3 L4 L5,
((|- L1 --> L5) /\ (|- L2 --> L5) /\ (|- L3 --> L5) /\ (|- L4 --> L5)) ->
(|- ((L1 /\ L2 /\ L3 /\ L4) --> L5)).
Proof. firstorder. Qed. 

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
| [ |- context [next_term (TermC (VarC "v")) = next_term ?e] ] =>
abstract (prove_diff_inv ("v" = e);
match goal with
| [ |- (|- (?I /\ Continuous eqs) --> next ?I) ] =>
extract_unchanged eqs; solve_linear
| [ |- _ ] =>
solve_linear
end)
| [ |- _ ] =>
try abstract solve [solve_linear |
prove_diff_inv TRUE; solve_linear]
end
| [ |- _ ]
=> pose "Discrete";
try abstract solve_linear
end.
+ apply Always_imp. apply ind_inv_safe.
Qed.
End HeightCtrl.
