Require Import Lang.Syntax.
Require Import Lang.Semantics.
Require Import Lang.ProofRules.
Require Import Rbase.

(************************************************)
(* Some examples.                               *)
(************************************************)

Open Scope HP_scope.
Open Scope string_scope.

(* Example 3.14 on page 171 of Platzer's textbook. This
   example includes the following three programs and
   their corresponding differential invariants. *)
Definition quartic1 b := [ |"x"' ::= `"x"^^4| & b].

Definition inv_quartic1 : Formula := 4 * `"x" >= 1.

Theorem inv_quartic1_ok : forall st b,
  eval_formula
    (inv_quartic1 --> [quartic1 b] inv_quartic1) st.
Proof.
  intro st; apply_proof_rules; auto; simpl in *; intros.
  (* We're essentially left with the goal
     forall x, 4 * x^4 >= 0 *)
Admitted.

Definition quartic2 b := [|"x"' ::= `"x"^^4 + `"x"^^2| & b].

Definition inv_quartic2 : Formula := 3 * 4 *`"x" >= 1.

Theorem inv_quartic2_ok : forall st b,
  eval_formula
    (inv_quartic2 --> [quartic2 b] inv_quartic2) st.
Proof.
  intro st; apply_proof_rules; auto; simpl in *; intros.
  (* We're essentially left with the goal
     forall x, 12(x^4 + x^2) >= 0 *)
Admitted.

Definition quad b := [|"x"' ::= `"x"^^2 - (4*`"x") + 6| & b].

Definition inv_quad : Formula := 3*4*`"x" >= 1.

Theorem inv_quad_ok : forall st b,
  eval_formula (inv_quad --> [quad b] inv_quad) st.
Proof.
  intro st; apply_proof_rules; auto; simpl in *; intros.
  (* We're essentially left with the goal
     forall x, 12(x^2 - 4x + 6) >= 0 *)
Admitted.

Definition cubic b := [|"x"' ::= `"x"^^3| & b].

Definition inv_cubic : Formula := 3*5*(`"x"^^2) >= 1.

Theorem inv_cubic_ok : forall st b,
  eval_formula (inv_cubic --> [cubic b] inv_cubic) st.
Proof.
  intro st; apply_proof_rules; auto; simpl in *; intros.
  (* We're essentially left with the goal
     forall x, 30x^4 >= 0 *)
Admitted.

(* Here's a more challenging example from section
   12 Assuming Invariants of Platzer's lecture notes
   http://symbolaris.com/course/fcps13/11-diffcut.pdf.
   We'll start with a formula that is not an invariant
   of the system to make sure our proof rules don't
   allow us to prove stuff that's wrong. Eventually,
   I'll implement something that does work. *)
Definition system b :=
  [|"x"' ::= `"d", "y"' ::= `"e", "d"' ::= `"e",
    "e"' ::= --`"d"| & b].

Definition bad_inv p : Formula :=
  ((`"x"-1)^^2) + (`"y"-2)^^2 >= (RealT p)^^2.

Theorem bad_inv_ok : forall st p b,
  eval_formula
    ((bad_inv p) --> [system b] (bad_inv p)) st.
Proof.
  intros st p; apply_proof_rules; auto; simpl in *; intros.
  (* We're essentially left with the goal
     forall x y d e, 2(x-1)d + 2(y-2)e >= 0
     which is unprovable, as it should be. *)
Abort.