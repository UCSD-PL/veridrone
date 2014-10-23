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

Ltac find_zeros eqs :=
  match eqs with
    | nil => constr:(@nil Var)
    | cons (DiffEqC ?y (ConstC (NatC O))) ?eqs =>
      let rest := find_zeros eqs in
      constr:(cons y rest)
    | cons _ ?eqs =>
      let rest := find_zeros eqs in
      rest
  end.

Ltac extract_unchanged eqs :=
  let xs := find_zeros eqs in
  let rec aux l :=
      match l with
        | nil => idtac
        | cons ?y ?l => apply zero_deriv
                        with (cp:=eqs) (x:=y);
                        try (aux l)
      end in
  aux xs.

Ltac get_var_inv F x :=
  match F with
    | And ?F1 _ =>
      get_var_inv F1 x
    | And _ ?F2 =>
      get_var_inv F2 x
    | Comp (next_term x) (next_term ?e) Eq => constr:(Comp x e Eq)
  end.

Ltac get_inv eqs F :=
  let xs := find_zeros eqs in
  let rec aux l :=
      match l with
        | nil => constr:(TRUE)
        | cons ?y ?l =>
          let y := constr:(TermC y) in
          let vinv := get_var_inv F y in
          let rest := aux l in
          constr:(And vinv rest)
        | cons _ ?l =>
          let rest := aux l in
          rest
      end in
  aux xs.

  Lemma safety :
    |- (Init /\ []Next) --> []Safe.
  Proof.
    apply imp_trans with (F2:=Ind_Inv /\ []Next).
    - apply and_right.
      + apply and_left1. apply ind_inv_init.
      + apply and_left2. apply imp_id.
    - apply imp_trans with (F2:=[]Ind_Inv).
      + apply inv_discr_ind; auto. unfold Next, Evolve.
        repeat apply or_next;
        match goal with
          | [ |- context [Continuous ?eqs] ]
              => pose "Continuous"; repeat apply and_right;
                 try solve [extract_unchanged eqs; solve_linear]
          | [ |- _ ]
              => pose "Discrete";
                 repeat first [ apply and_right |
                                apply imp_right ];
                 try solve_linear
        end.

Ltac prove_diff_inv known :=
  match goal with
      |- context [ Continuous ?eqs ] =>
      match goal with
          |- (|- _ --> Comp (next_term ?t1) (next_term ?t2) ?op) =>
          apply diff_ind with
          (Hyps:=known) (G:=Comp t1 t2 op) (cp:=eqs); try solve [solve_linear]
      end
(*      => apply diff_ind with
         (Hyps:=TRUE) (G:=Comp t1 t2 op) (cp:=eqs); solve_linear*)
  end.

(*Ltac assert_base_diff_inv t1 t2 op :=
  match goal with
      |- context [ Continuous ?eqs ]
      => assert (|- (Comp t1 t2 op /\ Continuous eqs) --> Comp (next_term t1) (next_term t2) op);
         try (prove_diff_inv TRUE)(*try (apply diff_ind with
              (Hyps:=TRUE) (G:=Comp t1 t2 op) (cp:=eqs); solve_linear)*)
  end.*)
repeat first [ apply and_right |
               apply imp_right ].
prove_diff_inv TRUE.
prove_diff_inv TRUE.
match goal with
|- context [Continuous ?eqs] =>
  extract_unchanged eqs
end; solve_linear.
prove_diff_inv ("v" = 1).
match goal with
|- context [Continuous ?eqs] =>
  extract_unchanged eqs
end; solve_linear.
match goal with
|- context [Continuous ?eqs] =>
  extract_unchanged eqs
end; solve_linear.
match goal with
|- context [Continuous ?eqs] =>
  extract_unchanged eqs
end; solve_linear.
prove_diff_inv ("v" = 1).
match goal with
|- context [Continuous ?eqs] =>
  extract_unchanged eqs
end; solve_linear.
match goal with
|- context [Continuous ?eqs] =>
  extract_unchanged eqs
end; solve_linear.
repeat first [ apply and_right |
               apply imp_right ].
prove_diff_inv TRUE.
match goal with
|- context [Continuous ?eqs] =>
  extract_unchanged eqs
end; solve_linear.
prove_diff_inv TRUE.
prove_diff_inv ("v" = --1).
(* Should apply diff_ind here instead. *)
match goal with
|- context [Continuous ?eqs] =>
  extract_unchanged eqs
end; solve_linear.
match goal with
|- context [Continuous ?eqs] =>
  extract_unchanged eqs
end; solve_linear.
match goal with
|- context [Continuous ?eqs] =>
  extract_unchanged eqs
end; solve_linear.
prove_diff_inv ("v" = --1).
match goal with
|- context [Continuous ?eqs] =>
  extract_unchanged eqs
end; solve_linear.
match goal with
|- context [Continuous ?eqs] =>
  extract_unchanged eqs
end; solve_linear.
prove_diff_inv TRUE.
+ apply always_imp. apply ind_inv_safe.
Qed.

End HeightCtrl.
