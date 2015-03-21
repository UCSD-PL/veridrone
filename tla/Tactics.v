Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Psatz.
Require Import Z3.Tactic.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.ProofRules.
Require Import TLA.Automation.


(* Some useful tactics for our examples. *)

(* This solves linear real arithmetic goals.
   It should be complete. *)
Ltac solve_linear :=
  breakAbstraction; intros; unfold eval_comp in *;
  simpl in *; intuition; try psatzl R.

(* This tries to solve nonlinear real
   arithmetic goals. It is not complete
   and can be incredibly inefficient. *)
Ltac solve_nonlinear :=
  breakAbstraction; intros; unfold eval_comp in *;
  simpl in *; intuition; try psatz R.

(* This simplifies real arithmetic goals.
   It sometimes is useful to run this before
   sending things to solve_nonlinear. *)
Ltac R_simplify :=
  unfold state, Value; field_simplify;
  unfold Rdiv;
  repeat rewrite RMicromega.Rinv_1;
  repeat
    match goal with
    | H:_ |- _ =>
      unfold state, Value in H; field_simplify in H;
      unfold Rdiv in H;
      repeat rewrite RMicromega.Rinv_1 in H;
      revert H
    end; intros.

(* Doesn't change the goal but runs
   z3 on real arithmetic goals. At the
   moment, you have to look in the *coq*
   buffer for the output. *)
Ltac z3_solve :=
  intros;
  repeat match goal with
           | H : @eq R _ _ |- _ => revert H
           | H : @Rle _ _ |- _ => revert H
           | H : @Rge _ _ |- _ => revert H
           | H : @Rlt _ _ |- _ => revert H
           | H :@ Rgt _ _ |- _ => revert H
           | H : @Rge _ _ |- _ => revert H
         end;
  z3Tactic.

(* rewrites the values of variables in the next
   state into hypothesis and goals. *)
Ltac rewrite_next_st :=
  repeat match goal with
           | [ H : eq (Stream.hd (Stream.tl _) _)  _ |- _ ]
             => rewrite H in *
         end.

(* Gets rid of arithmetic expressions of the
   form 0+_, _+0, 0*_, and _*0 in the goal. *)
Ltac rewrite_real_zeros :=
  repeat first [rewrite Rmult_0_r |
                rewrite Rmult_0_l |
                rewrite Rplus_0_r |
                rewrite Rplus_0_l].

Open Scope HP_scope.

(* I'm not sure what the following three
   tactics do *)
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
    | Comp (next_term x) (next_term ?e) Eq =>
      constr:(Comp x e Eq)
  end.

(* Applies differential induction with
   a known differential invariant *)
Ltac prove_diff_inv known :=
  match goal with
      |- context [ Continuous ?eqs ] =>
      match goal with
          |- (|-- _ -->> Comp (next_term ?t1)
                   (next_term ?t2) ?op) =>
          apply diff_ind with
          (Hyps:=known) (G:=Comp t1 t2 op) (cp:=eqs)
      end
  end.

(* Removes ! from variables in a Term *)
Fixpoint unnext_term (t:Term) : Term :=
  match t with
    | VarNowT x => VarNowT x
    | VarNextT x => VarNowT x
    | RealT r => RealT r
    | NatT n => NatT n
    | PlusT t1 t2 =>
      PlusT (unnext_term t1) (unnext_term t2)
    | MinusT t1 t2 =>
      MinusT (unnext_term t1) (unnext_term t2)
    | MultT t1 t2 =>
      MultT (unnext_term t1) (unnext_term t2)
    | InvT t => InvT (unnext_term t)
    | CosT t => CosT (unnext_term t)
    | SinT t => SinT (unnext_term t)
  end.

(* Removes ! from variables in a Formula *)
Fixpoint unnext (F:Formula) : Formula :=
  match F with
    | Comp t1 t2 op =>
      Comp (unnext_term t1) (unnext_term t2) op
    | And F1 F2 => And (unnext F1) (unnext F2)
    | _ => F
  end.

(* Tries to prove (discrete) inductive goals in our examples.
   Only works for linear arithmetic. Leaves unsolved subgoals
   unchanged. *)
Ltac prove_inductive :=
  repeat apply or_next; repeat apply and_right;
  match goal with
    | [ |- context [Continuous ?deqs] ] =>
      match goal with
        | [ |- (|-- _ -->> (?HH -->> ?GG))] =>
          abstract (apply diff_ind_imp
                    with (eqs:=deqs) (H:=unnext HH)
                                     (G:=unnext GG);
                    solve [reflexivity |
                           simpl; intuition;
                           solve_linear])
        | [ |- _ ] =>
          abstract
            (apply unchanged_continuous with (eqs:=deqs);
             solve_linear)
        | [ |- (|-- _ -->> ?GG) ] =>
          abstract (eapply diff_ind
                    with (cp:=deqs) (G:=unnext GG)
                                    (Hyps:=TRUE);
                    try solve [reflexivity |
                               simpl; intuition;
                               solve_linear] )
      end
    | [ |- _ ] =>
      try abstract (solve_linear)
  end.

Close Scope HP_scope.