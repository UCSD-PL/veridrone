Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import ChargeTactics.Lemmas.

(* Terms in the parallel language. The type parameter
   that is a list of vars captures the variables
   appearing in the term. *)
Inductive ParTerm : list Var -> Type :=
| VarPT : forall x, ParTerm (x::nil)
| NatPT : nat -> ParTerm nil
| RealPT : R -> ParTerm nil
| PlusPT : forall {xs ys},
    ParTerm xs -> ParTerm ys -> ParTerm (xs ++ ys)
| MinusPT : forall {xs ys},
    ParTerm xs -> ParTerm ys -> ParTerm (xs ++ ys)
| MultPT : forall {xs ys},
    ParTerm xs -> ParTerm ys -> ParTerm (xs ++ ys)
| InvPT : forall {xs}, ParTerm xs -> ParTerm xs
| CosPT : forall {xs}, ParTerm xs -> ParTerm xs
| SinPT : forall {xs}, ParTerm xs -> ParTerm xs
| SqrtPT : forall {xs}, ParTerm xs -> ParTerm xs
| ArctanPT : forall {xs}, ParTerm xs -> ParTerm xs
| ExpPT : forall {xs}, ParTerm xs -> ParTerm xs
| MaxPT : forall {xs ys},
    ParTerm xs -> ParTerm ys -> ParTerm (xs ++ ys)
.

(* Conditionals in the parallel language. The type parameter
   that is a list of vars captures the variables
   appearing in the conditional. *)
Inductive Cond : list Var -> Type :=
| TRUEP : Cond nil
| FALSEP : Cond nil
| CompP : forall {xs ys},
    ParTerm xs -> ParTerm ys -> CompOp -> Cond (xs ++ ys)
| AndP : forall {xs ys},
    Cond xs -> Cond ys -> Cond (xs ++ ys)
| OrP : forall {xs ys},
    Cond xs -> Cond ys -> Cond (xs ++ ys)
| NegP : forall {xs}, Cond xs -> Cond xs.

Definition sets_disjoint {T} (a b : list T) : Prop :=
    forall x,
      List.In x b -> ~List.In x a.

(* A language with parallel semantics.
   An instance of (Parallel in out) is a program
   with input variables in and output variables out. *)
Inductive Parallel : list Var -> list Var -> Type :=
| Assign : forall x ins, ParTerm ins ->
                         Parallel ins (x::nil)
| Par : forall {ins1 ins2 outs1 outs2},
    sets_disjoint outs1 outs2 ->
    Parallel ins1 outs1 -> Parallel ins2 outs2 ->
    Parallel (ins1 ++ ins2) (outs1 ++ outs2)
| Ite : forall {insc ins1 ins2 outs1 outs2},
    Cond insc -> Parallel ins1 outs1 -> Parallel ins2 outs2 ->
    Parallel (insc ++ ins1 ++ ins2) (outs1 ++ outs2).

(* Evaluation for terms in the language. *)
Fixpoint eval_ParTerm {xs} (t : ParTerm xs) (st : state)
  : Value :=
  match t with
  | VarPT x => st x
  | NatPT n => Coq.Reals.Raxioms.INR n
  | RealPT r => r
  | PlusPT _ _ t1 t2 =>
    eval_ParTerm t1 st + eval_ParTerm t2 st
  | MinusPT _ _ t1 t2 =>
    eval_ParTerm t1 st - eval_ParTerm t2 st
  | MultPT _ _ t1 t2 =>
    eval_ParTerm t1 st * eval_ParTerm t2 st
  | InvPT _ t => / (eval_ParTerm t st)
  | CosPT _ t => Rtrigo_def.cos (eval_ParTerm t st)
  | SinPT _ t => Rtrigo_def.sin (eval_ParTerm t st)
  | SqrtPT _ t => R_sqrt.sqrt (eval_ParTerm t st)
  | ArctanPT _ t => Ratan.atan (eval_ParTerm t st)
  | ExpPT _ t => Rtrigo_def.exp (eval_ParTerm t st)
  | MaxPT _ _ t1 t2 =>
    Rbasic_fun.Rmax (eval_ParTerm t1 st) (eval_ParTerm t2 st)
  end%R.

Definition eval_ParComp {xs ys} (t1:ParTerm xs)
           (t2:ParTerm ys) (op:CompOp)
           (st:state) : bool :=
  if match op as _op return
           forall r1 r2:R,
             let _op := match _op with
                        | Gt => Rgt
                        | Ge => Rge
                        | Lt => Rlt
                        | Le => Rle
                        | Eq => eq
                        end in
             {_op r1 r2} + {~_op r1 r2}
     with
     | Gt => RIneq.Rgt_dec
     | Ge => RIneq.Rge_dec
     | Lt => RIneq.Rlt_dec
     | Le => RIneq.Rle_dec
     | Eq => RiemannInt.Req_EM_T
     end (eval_ParTerm t1 st) (eval_ParTerm t2 st)
  then true else false.

Fixpoint eval_Cond {xs} (c : Cond xs) (st : state) : bool :=
  match c with
  | TRUEP => true
  | FALSEP => false
  | CompP _ _ t1 t2 op => eval_ParComp t1 t2 op st
  | AndP _ _ c1 c2 => andb (eval_Cond c1 st) (eval_Cond c2 st)
  | OrP _ _ c1 c2 => orb (eval_Cond c1 st) (eval_Cond c2 st)
  | NegP _ c => negb (eval_Cond c st)
  end.

Definition merge_states (xs1 xs2 : list Var)
           (st1 st2 : state) : state :=
  fun x =>
    if List.existsb (fun y => if String.string_dec x y
                              then true else false) xs1
    then st1 x
    else if List.existsb (fun y => if String.string_dec x y
                                   then true else false) xs2
         then st2 x else st1 x.

Fixpoint eval_Parallel {ins outs} (p : Parallel ins outs)
         (st : state) : state :=
  match p with
  | Assign x _ t => fun y => if String.string_dec x y
                           then eval_ParTerm t st
                           else st y
  | Par _ _ outs1 outs2 _ p1 p2 =>
    let st1 := eval_Parallel p1 st in
    let st2 := eval_Parallel p2 st in
    merge_states outs1 outs2 st1 st2
  | Ite _ _ _ _ _ c p1 p2 =>
    if eval_Cond c st
    then eval_Parallel p1 st
    else eval_Parallel p2 st
  end.

Definition tlaParD {ins outs} (p : Parallel ins outs) :=
  Embed (fun st1 st2 =>
           forall x, List.In x outs ->
                     eval_Parallel p st1 x = st2 x).

(* Language definition complete. *)

Fixpoint Term_to_ParTerm (t : Syntax.Term) :
  { xs : list Var & ParTerm xs } :=
  match t with
  | VarNowT x => existT _ _ (VarPT x)
  | NatT n => existT _ _ (NatPT n)
  | RealT r => existT _ _ (RealPT r)
  | PlusT t1 t2 =>
    existT _ _
           (PlusPT (projT2 (Term_to_ParTerm t1))
                   (projT2 (Term_to_ParTerm t2)))
  | MinusT t1 t2 =>
    existT _ _
           (MinusPT (projT2 (Term_to_ParTerm t1))
                   (projT2 (Term_to_ParTerm t2)))
  | MultT t1 t2 =>
    existT _ _
           (MultPT (projT2 (Term_to_ParTerm t1))
                   (projT2 (Term_to_ParTerm t2)))
  | InvT t =>
    existT _ _ (InvPT (projT2 (Term_to_ParTerm t)))
  | CosT t =>
    existT _ _ (CosPT (projT2 (Term_to_ParTerm t)))
  | SinT t =>
    existT _ _ (SinPT (projT2 (Term_to_ParTerm t)))
  | SqrtT t =>
    existT _ _ (SqrtPT (projT2 (Term_to_ParTerm t)))
  | ArctanT t =>
    existT _ _ (ArctanPT (projT2 (Term_to_ParTerm t)))
  | ExpT t =>
    existT _ _ (ExpPT (projT2 (Term_to_ParTerm t)))
  | MaxT t1 t2 =>
    existT _ _
           (MaxPT (projT2 (Term_to_ParTerm t1))
                  (projT2 (Term_to_ParTerm t2)))
  | _ => existT _ _ (NatPT 0)
  end.

Fixpoint Formula_to_Cond (F : Formula) :
  { xs : list Var & Cond xs } :=
  match F with
  | TRUE => existT _ _ TRUEP
  | FALSE => existT _ _ FALSEP
  | Comp t1 t2 op =>
    existT _ _
           (CompP (projT2 (Term_to_ParTerm t1))
                  (projT2 (Term_to_ParTerm t2)) op)
  | And F1 F2 =>
    existT _ _
           (AndP (projT2 (Formula_to_Cond F1))
                 (projT2 (Formula_to_Cond F2)))
  | Or F1 F2 =>
    existT _ _
           (OrP (projT2 (Formula_to_Cond F1))
                 (projT2 (Formula_to_Cond F2)))
  | Syntax.Imp F1 F2 =>
    existT _ _
           (OrP (NegP (projT2 (Formula_to_Cond F1)))
                (projT2 (Formula_to_Cond F2)))
  | _ => existT _ _ TRUEP
  end.

Lemma Term_to_ParTerm_sound :
  forall t tr,
    is_st_term t = true ->
    eval_ParTerm (projT2 (Term_to_ParTerm t)) (Stream.hd tr) =
    eval_term t (Stream.hd tr) (Stream.hd (Stream.tl tr)).
Proof.
  induction t; simpl;
  try solve [ reflexivity |
              discriminate |
              intros; rewrite Bool.andb_true_iff in *;
              rewrite IHt2; try tauto; rewrite IHt1;
              try tauto |
              intros; rewrite IHt; tauto ].
Qed.

(* true if the formula can be decided on the current state. *)
Fixpoint is_decidable_st_formula (F:Formula) : bool :=
  match F with
    | TRUE => true
    | FALSE => true
    | Comp t1 t2 _ =>
      andb (is_st_term t1) (is_st_term t2)
    | And F1 F2 | Or F1 F2 | Syntax.Imp F1 F2 =>
      andb (is_decidable_st_formula F1)
           (is_decidable_st_formula F2)
    | _ => false
  end.

Lemma excluded_middle :
  forall A,
    is_decidable_st_formula A = true ->
    |-- A \\// (A -->> lfalse).
Proof.
  induction A; breakAbstraction; auto; intros;
  try solve [ apply andb_prop in H; destruct H as [HA1 HA2];
              specialize (IHA1 HA1 tr I);
              specialize (IHA2 HA2 tr I);
              intuition | discriminate ].
  destruct c; solve_linear.
Qed.

Lemma Formula_to_Cond_true :
  forall A tr,
    is_decidable_st_formula A = true ->
    (eval_Cond (projT2 (Formula_to_Cond A))
               (Stream.hd tr) = true <->
     eval_formula A tr).
Proof.
  induction A;
  try solve [ simpl; intuition |
              simpl; intros;
              repeat rewrite Bool.andb_true_iff in *;
              repeat rewrite Bool.orb_true_iff in *;
              rewrite IHA1; try tauto;
              rewrite IHA2; tauto ].
  - simpl; unfold eval_comp; simpl; intros;
    rewrite Bool.andb_true_iff in H;
    destruct c; unfold eval_ParComp; simpl;
    match goal with
    | [ |- context [ if ?e then _ else _ ] ]
      => destruct e
    end; repeat rewrite <- Term_to_ParTerm_sound;
    intuition.
  - pose proof (excluded_middle A1) as Hexcluded;
    breakAbstraction.
    simpl; intros;
    repeat rewrite Bool.andb_true_iff in *;
    repeat rewrite Bool.orb_true_iff in *;
    repeat rewrite Bool.negb_true_iff in *.
    rewrite IHA2; try tauto.
    specialize (Hexcluded (proj1 H) tr I).
    intuition.
    { rewrite <- IHA1 in *; try tauto; congruence. }
    { left. rewrite <- IHA1 in *; try tauto;
            apply Bool.not_true_is_false; auto. }
Qed.

Lemma ite_refine_aux :
  forall A B C,
    is_decidable_st_formula A = true ->
    (A -->> B) //\\ ((A-->>lfalse) -->> C)  |--
    (A //\\ B) \\// C.
Proof.
  intros.
  tlaAssert (A \\// (A -->> lfalse));
    [ rewrite <- excluded_middle; auto; charge_tauto |
      charge_intros ].
  repeat rewrite land_lor_distr_L;
  repeat apply lorL; charge_tauto.
Qed.

Lemma ite_refine :
  forall A B C ins1 ins2 outs1 outs2
         (b:Parallel ins1 outs1) (c:Parallel ins2 outs2),
    is_decidable_st_formula A = true ->
    tlaParD b |-- B ->
    tlaParD c |-- C ->
    tlaParD (Ite (projT2 (Formula_to_Cond A)) b c) |--
            (A //\\ B) \\// C.
Proof.
  intros.
  rewrite <- ite_refine_aux; auto.
  rewrite <- H0. rewrite <- H1. clear H0 H1.
  breakAbstraction. intros.
  rewrite <- Formula_to_Cond_true; auto.
  split; intros; rewrite <- H0 by (apply in_or_app; tauto).
  { intros. rewrite H1; auto. }
  { intros.
    match goal with
    | [ |- context [ if ?e then _ else _ ] ]
      => destruct e
    end; intuition. }
Qed.

Lemma Assign_refine :
  forall x t,
    is_st_term t = true ->
    tlaParD (Assign x _ (projT2 (Term_to_ParTerm t))) |--
    x! = t.
Proof.
  intros; breakAbstraction; intros;
  rewrite <- Term_to_ParTerm_sound; auto;
  rewrite <- H0; destruct (String.string_dec x x);
  intuition.
Qed.

Lemma ite_refine_and_impl :
  forall A B C D ins1 ins2 outs1 outs2
         (b:Parallel ins1 outs1) (d:Parallel ins2 outs2),
    is_decidable_st_formula A = true ->
    A //\\ C |-- lfalse ->
    tlaParD b |-- B ->
    tlaParD d |-- D ->
    tlaParD (Ite (projT2 (Formula_to_Cond A)) b d) |--
            (A -->> B) //\\ (C -->> D).
Proof.
  intros. rewrite <- H1. rewrite <- H2. clear H1 H2.
  breakAbstraction. intros.
  split; intros; rewrite <- H1 by (apply in_or_app; tauto);
  clear H1; specialize (H0 tr);
  rewrite <- (Formula_to_Cond_true A) in *; auto;
  match goal with
  | [ |- context [ if ?e then _ else _ ] ]
    => destruct e eqn:?
  end; intuition.
Qed.

Lemma par_disjoint_refine :
  forall A B ins1 ins2 outs1 outs2
         (a:Parallel ins1 outs1) (b:Parallel ins2 outs2),
    tlaParD a |-- A ->
    tlaParD b |-- B ->
    forall (pf:sets_disjoint outs1 outs2),
      tlaParD (Par pf a b) |-- A //\\ B.
Proof.
  intros. breakAbstraction. intros.
  split.
  { apply H; intros;
    rewrite <- H1 by (apply List.in_or_app; tauto).
    unfold merge_states, sets_disjoint in *.
    repeat match goal with
           | [ |- context [ if ?e then _ else _ ] ]
               => destruct e eqn:?
           end; try reflexivity.
    rewrite existsb_exists in *.
    destruct Heqb1 as [y [Hy ?]].
    destruct (String.string_dec x y); try discriminate.
    subst; specialize (pf y); intuition. }
  { apply H0; intros;
    rewrite <- H1 by (apply List.in_or_app; tauto).
    unfold merge_states, sets_disjoint in *.
    repeat match goal with
           | [ |- context [ if ?e then _ else _ ] ]
               => destruct e eqn:?
           end; try reflexivity.
    { rewrite existsb_exists in *.
      destruct Heqb0 as [y [Hy ?]].
      destruct (String.string_dec x y); try discriminate.
      subst; specialize (pf y); intuition. }
    { rewrite <- Bool.not_true_iff_false in *.
      rewrite existsb_exists in *.
      contradict Heqb1. exists x.
      destruct (String.string_dec x x); auto. } }
Qed.