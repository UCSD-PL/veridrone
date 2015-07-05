Inductive ImpTerm :=
| VarIT : Var -> ImpTerm
| NatIT : nat -> ImpTerm
| RealIT : R -> ImpTerm
| PlusIT : ImpTerm -> ImpTerm -> ImpTerm
| MinusIT : ImpTerm -> ImpTerm -> ImpTerm
| MultIT : ImpTerm -> ImpTerm -> ImpTerm
| InvIT : ImpTerm -> ImpTerm 
| CosIT : ImpTerm -> ImpTerm
| SinIT : ImpTerm -> ImpTerm
| SqrtIT : ImpTerm -> ImpTerm 
| ArctanIT : ImpTerm -> ImpTerm 
.

Inductive Cond :=
| TRUEI : Cond
| FALSEI : Cond
| CompI : ImpTerm -> ImpTerm -> CompOp -> Cond
| AndI : Cond -> Cond -> Cond
| OrI : Cond -> Cond -> Cond
| NegI : Cond -> Cond.

Inductive Imp :=
| Assign : Var -> ImpTerm -> Imp
| Seq : Imp -> Imp -> Imp
| Ite : Cond -> Imp -> Imp -> Imp.

Fixpoint eval_ImpTerm (t : ImpTerm) (st : state)
  : Value :=
  match t with
  | VarIT x => st x
  | NatIT n => Coq.Reals.Raxioms.INR n
  | RealIT r => r
  | PlusIT t1 t2 =>
    eval_ImpTerm t1 st + eval_ImpTerm t2 st
  | MinusIT t1 t2 =>
    eval_ImpTerm t1 st - eval_ImpTerm t2 st
  | MultIT t1 t2 =>
    eval_ImpTerm t1 st * eval_ImpTerm t2 st
  | InvIT t => / (eval_ImpTerm t st)
  | CosIT t => Rtrigo_def.cos (eval_ImpTerm t st)
  | SinIT t => Rtrigo_def.sin (eval_ImpTerm t st)
  | SqrtIT t => R_sqrt.sqrt (eval_ImpTerm t st)
  | ArctanIT t => Ratan.atan (eval_ImpTerm t st)
  end%R.

Definition eval_ImpComp (t1 t2:ImpTerm) (op:CompOp)
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
     end (eval_ImpTerm t1 st) (eval_ImpTerm t2 st)
  then true else false.

Fixpoint eval_Cond (c : Cond) (st : state) : bool :=
  match c with
  | TRUEI => true
  | FALSEI => false
  | CompI t1 t2 op => eval_ImpComp t1 t2 op st
  | AndI c1 c2 => andb (eval_Cond c1 st) (eval_Cond c2 st)
  | OrI c1 c2 => orb (eval_Cond c1 st) (eval_Cond c2 st)
  | NegI c => negb (eval_Cond c st)
  end.

Fixpoint eval_Imp (p : Imp) (st : state) : state :=
  match p with
  | Assign x t => fun y => if String.string_dec x y
                           then eval_ImpTerm t st
                           else st y
  | Seq p1 p2 => eval_Imp p2 (eval_Imp p1 st)
  | Ite c p1 p2 =>
    if eval_Cond c st
    then eval_Imp p1 st
    else eval_Imp p2 st
  end.

Definition tlaImpD (p : Imp) :=
  Embed (fun st1 st2 =>
           eq (eval_Imp p st1) st2).

Fixpoint Term_to_ImpTerm (t : Syntax.Term) :
  ImpTerm :=
  match t with
  | VarNowT x => VarIT x
  | NatT n => NatIT n
  | RealT r => RealIT r
  | PlusT t1 t2 =>
    PlusIT (Term_to_ImpTerm t1) (Term_to_ImpTerm t2)
  | MinusT t1 t2 =>
    MinusIT (Term_to_ImpTerm t1) (Term_to_ImpTerm t2)
  | MultT t1 t2 =>
    MultIT (Term_to_ImpTerm t1) (Term_to_ImpTerm t2)
  | InvT t => InvIT (Term_to_ImpTerm t)
  | CosT t => CosIT (Term_to_ImpTerm t)
  | SinT t => SinIT (Term_to_ImpTerm t)
  | SqrtT t => SqrtIT (Term_to_ImpTerm t)
  | ArctanT t => ArctanIT (Term_to_ImpTerm t)
  | _ => NatIT 0
  end.

Fixpoint Formula_to_Cond (F : Formula) : Cond :=
  match F with
  | TRUE => TRUEI
  | FALSE => FALSEI
  | Comp t1 t2 op =>
    CompI (Term_to_ImpTerm t1) (Term_to_ImpTerm t2) op
  | And F1 F2 =>
    AndI (Formula_to_Cond F1) (Formula_to_Cond F2)
  | Or F1 F2 =>
    OrI (Formula_to_Cond F1) (Formula_to_Cond F2)
  | Syntax.Imp F1 F2 =>
    OrI (NegI (Formula_to_Cond F1)) (Formula_to_Cond F2)
  | _ => TRUEI
  end.

Lemma Term_to_ImpTerm_sound :
  forall t tr,
    is_st_term t = true ->
    eval_ImpTerm (Term_to_ImpTerm t) (Stream.hd tr) =
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

Lemma Formula_to_Cond_true :
  forall A tr,
    is_decidable_st_formula A = true ->
    (eval_Cond (Formula_to_Cond A)
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
    destruct c; unfold eval_ImpComp; simpl;
    match goal with
    | [ |- context [ if ?e then _ else _ ] ]
      => destruct e
    end; repeat rewrite <- Term_to_ImpTerm_sound;
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

Lemma ite_refine :
  forall A B C b c,
    is_decidable_st_formula A = true ->
    tlaImpD b |-- B ->
    tlaImpD c |-- C ->
    tlaImpD (Ite (Formula_to_Cond A) b c) |--
            (A //\\ B) \\// C.
Proof.
  intros.
  rewrite <- ite_refine_aux; auto.
  rewrite <- H0. rewrite <- H1. clear H0 H1.
  breakAbstraction. intros.
  rewrite <- Formula_to_Cond_true; auto.
  rewrite <- H0.
  split.
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
    tlaImpD (Assign x (Term_to_ImpTerm t)) |-- x! = t.
Proof.
  intros; breakAbstraction; intros;
  rewrite <- Term_to_ImpTerm_sound; auto;
  rewrite <- H0; destruct (String.string_dec x x);
  intuition.
Qed.

Lemma ite_refine_and_impl :
  forall A B C D b d,
    is_decidable_st_formula A = true ->
    A //\\ C |-- lfalse ->
    tlaImpD b |-- B ->
    tlaImpD d |-- D ->
    tlaImpD (Ite (Formula_to_Cond A) b d) |--
            (A -->> B) //\\ (C -->> D).
Proof.
  intros. rewrite <- H1. rewrite <- H2. clear H1 H2.
  breakAbstraction. intros.
  rewrite <- H1. clear H1. specialize (H0 tr).
  rewrite <- Formula_to_Cond_true in *; auto.
  match goal with
  | [ |- context [ if ?e then _ else _ ] ]
    => destruct e eqn:?
  end; intuition.
Qed.

(*  Lemma seq_disjoint_refine :
    forall A B a b,
      disjoint_states A B ->
      tlaImpD a |-- A ->
      tlaImpD b |-- B ->
      tlaImpD (Seq a b) |-- A //\\ B.
  Proof.
    intros. unfold disjoint_states in *.
    destruct H as [xs [ys Hdisjoint]].
    unfold disjoint_states_aux, next_state_vars in *.
    pose proof (refinements_disjoint Hdisjoint H0 H1)
      as Hdisjoint_ref.
    breakAbstraction. intros.
    destruct Hdisjoint as [Hdisjoint [HA HB]].
    destruct Hdisjoint_ref as [Hdisjoint_ref [Ha Hb]].
    destruct tr as [st tr]. simpl in *.
    split.
    { rewrite HA.
      { apply H0. simpl.
        instantiate (1:=Stream.Cons (eval_Imp a st)
                                    (Stream.tl tr)).
        reflexivity. }
      { unfold traces_agree. intros. constructor.
        { simpl. unfold state in *. rewrite <- H.
          apply sets_disjoint_equiv in Hdisjoint_ref.
          unfold sets_disjoint in *.
          specialize (Hdisjoint_ref _ H2).
          erewrite next_state_vars_imp; eauto. }
        { apply Stream.Reflexive_stream_eq.
          red. reflexivity. } } }
    { rewrite HB.
      { apply H1. simpl.
        instantiate (1:=Stream.Cons (eval_Imp b st)
                                    (Stream.tl tr)).
        reflexivity. }
      { unfold traces_agree. intros. constructor.
        { simpl. unfold state in *. rewrite <- H.
          unfold sets_disjoint in *.
          specialize (Hdisjoint_ref _ H2).
          pose proof disjoint_seq_comm as Hcomm.
          simpl in *. rewrite Hcomm.
          { erewrite next_state_vars_imp; eauto. }
          { unfold disjoint_states. exists xs. exists ys.
            unfold disjoint_states_aux. auto. } }
        { apply Stream.Reflexive_stream_eq.
          red. reflexivity. } } }
  Qed.
*)