Require Import Lang.Syntax.
Require Import Lang.Semantics.
Require Import Lang.ProofRules.
Require Import String.
Require Import Rdefinitions.
Require Import Rpow_def.
Require Import Rbase.

Open Scope HP_scope.
Open Scope string_scope.

Definition ctrl kP x :=
  "v" ::= #kP*(`"h"-#x).

Definition world b :=
  | "h"' ::=  `"v" | & b.

Definition inv1 h0 x : Formula :=
  `"h" - #x <= #h0 - #x.
Definition inv2 h0 x : Formula :=
  (`"h" - #x)^^2 <= (#h0 - #x)^^2.

Definition sys x kP b :=
  While (#0 = #0) (ctrl kP x; world b).

Theorem inv_ok : forall x kP b st h0,
  eval_formula
    (`"h" = #h0 /\ inv2 h0 x --> [sys x kP b] inv2 h0 x)
    st.
Proof.
intros; apply_proof_rules; auto; simpl in *; intros;
unfold eval_comp in *; simpl in *; field_simplify.
+ destruct H. subst h0. apply Req_le. field.
+ (* Here we're left with h^2-2hx+x^2 <= 0 *) admit.
Abort.