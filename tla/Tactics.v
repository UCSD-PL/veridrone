Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Psatz.
Require Import Z3.Tactic.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.ProofRules.
Require Import TLA.Automation.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

(* Some useful tactics for our examples. *)

Ltac destruct_ite :=
  match goal with
  | [ |- context [ if ?e then _ else _ ] ]
    => destruct e
  end.

Fixpoint get_vars_term (t : Term) : list Var :=
  match t with
  | VarNextT t | VarNowT t => t :: nil
  | NatT _ | RealT _ => nil
  | PlusT a b | MinusT a b | MultT a b | MaxT a b =>
                             get_vars_term a ++
                                           get_vars_term b
  | InvT a | CosT a | SinT a | SqrtT a | ArctanT a | ExpT a =>
                                         get_vars_term a
  end.

Definition get_image_vars (m:list (Var*Term)) :=
  List.flat_map (fun p => get_vars_term (snd p)) m.

Fixpoint get_witness (m : list (Var*Term)) : state -> state :=
  match m with
  | nil => fun st => st
  | (x,VarNowT y) :: m =>
    fun st z =>
      if String.string_dec z y
      then st x else get_witness m st z
  | _ => fun st => st
  end.

Fixpoint get_next_vars_term (t : Term) : list Var :=
  match t with
  | VarNextT t => t :: nil
  | VarNowT _ | NatT _ | RealT _ => nil
  | PlusT a b | MinusT a b | MultT a b | MaxT a b =>
                             get_next_vars_term a ++
                             get_next_vars_term b
  | InvT a | CosT a | SinT a | SqrtT a | ArctanT a | ExpT a
      => get_next_vars_term a
  end.

Fixpoint get_next_vars_formula (f : Formula) : list Var :=
  match f with
  | Always a | Eventually a | Enabled a =>
                              get_next_vars_formula a
  | And a b | Or a b | Imp a b =>
                       get_next_vars_formula a ++
                       get_next_vars_formula b
  | Rename _ a => get_next_vars_formula a
  | Comp l r _ => get_next_vars_term l ++
                                     get_next_vars_term r
  | _ => nil
  end.

Fixpoint remove_dup (ls : list Var) : list Var :=
  match ls with
  | nil => nil
  | l :: ls => let ls' := remove_dup ls in
               if in_dec string_dec l ls'
               then ls' else l :: ls'
  end.

Ltac enable_ex_st :=
  match goal with
  | |- lentails _ (Enabled ?X) =>
    let vars := eval compute in
    (remove_dup (get_next_vars_formula X)) in
        let rec foreach ls :=
            match ls with
            | @cons _ ?l ?ls => eapply (ex_state l); simpl;
                                foreach ls
            | _ => idtac
            end
        in
        eapply Enabled_action; simpl; intros;
        foreach vars
  end; try (eapply ex_state_any; (let st := fresh in
                                  intro st; clear st)).

Ltac smart_repeat_eexists :=
  repeat match goal with
           |- exists x, _ => eexists
         end.

(* The old tactic, very slow. *)
(*
Ltac enable_ex_st :=
  eapply Enabled_action; intros; eapply ex_state_flow_any;
  auto; simpl; intros;
  repeat match goal with
         | |- context [ ?X ] =>
           match type of X with
           | Var => idtac
           | String.string => idtac
           end ;
             try match goal with
                 | X := _ |- _ => unfold X
                 end;
             eapply (@ex_state X) ; simpl ;
             match goal with
             | |- exists x (y : _), (@?F x) => fail 1
             | |- _ => idtac
             end
         end;
  try (eapply ex_state_any ;
       let st := fresh in intro st ; clear st).
*)

Ltac is_st_term_list :=
  simpl; intros;
  repeat match goal with
           |- context [ String.string_dec ?e1 ?e2 ] =>
           destruct (String.string_dec e1 e2)
         end; try reflexivity; try tauto.

Lemma reason_action : forall P Q,
    (forall a b tr,
        eval_formula
          P
          (Stream.Cons a
                       (Stream.Cons b tr)) ->
        eval_formula
          Q (Stream.Cons a (Stream.Cons b tr))) ->
    (P |-- Q).
Proof.
  red. red. red. intros. destruct tr.
  destruct tr. auto.
Qed.

Ltac reason_action_tac :=
  eapply reason_action; simpl;
  let pre := fresh "pre" in
  let post := fresh "post" in
  let tr := fresh "tr" in
  intros pre post tr;
    breakAbstraction; simpl; unfold eval_comp;
    simpl; intros.

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

Ltac zero_deriv_tac v :=
  eapply ContinuousProofRules.zero_deriv
  with (x:=v); [ charge_tauto | solve_linear | ].

Ltac always_imp_tac :=
  match goal with
  | [ |- ?H |-- _ ]
    => match H with
       | context[ Always ?HH ] =>
         tlaAssert (Always HH);
           [ charge_tauto |
             apply Lemmas.forget_prem; apply always_imp ]
       end
  end.

Ltac specialize_arith_hyp H :=
  repeat match type of H with
         | ?G -> _ =>
           let HH := fresh "H" in
           assert G as HH by solve_linear;
             specialize (H HH); clear HH
         end.

Ltac specialize_arith :=
  repeat match goal with
         | [ H : ?G -> _ |- _ ] =>
           specialize_arith_hyp H
         end.

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
Ltac z3_prepare :=
  intros.

Ltac z3_solve :=
  z3_prepare; z3 solve.

Ltac z3_quick :=
  z3_prepare; z3 solve.

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
(*
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
*)

(*
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
*)

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
    | SqrtT t => SqrtT (unnext_term t)
    | ArctanT t => ArctanT (unnext_term t)
    | ExpT t => ExpT (unnext_term t)
    | MaxT t1 t2 => MaxT (unnext_term t1) (unnext_term t2)
  end.

(* Removes ! from variables in a Formula *)
Fixpoint unnext (F:Formula) : Formula :=
  match F with
    | Comp t1 t2 op =>
      Comp (unnext_term t1) (unnext_term t2) op
    | And F1 F2 => And (unnext F1) (unnext F2)
    | Or F1 F2 => Or (unnext F1) (unnext F2)
    | Imp F1 F2 => Imp (unnext F1) (unnext F2)
    | Syntax.Exists T f => Syntax.Exists T (fun t => unnext (f t))
    | Syntax.Forall T f => Syntax.Forall T (fun t => unnext (f t))
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
(*        | [ |- (|-- _ -->> (?HH -->> ?GG))] =>
          abstract (apply diff_ind_imp
                    with (eqs:=deqs) (H:=unnext HH)
                                     (G:=unnext GG);
                    solve [reflexivity |
                           simpl; intuition;
                           solve_linear])*)
(*        | [ |- _ ] =>
          abstract
            (apply unchanged_continuous with (eqs:=deqs);
             solve_linear)*)
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