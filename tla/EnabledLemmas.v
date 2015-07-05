Require Import TLA.TLA.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Definition traces_agree (tr1 tr2 : trace)
           (xs : list Var) : Prop :=
  forall x,
    List.In x xs ->
    Stream.stream_eq (fun st1 st2 => eq (st1 x) (st2 x))
                     tr1 tr2.

Definition next_state_vars (A : Formula)
           (xs : list Var) : Prop :=
  forall tr1 tr2 st,
    traces_agree tr1 tr2 xs ->
    (eval_formula A (Stream.Cons st tr1) <->
     eval_formula A (Stream.Cons st tr2)).

Definition sets_disjoint {T} (a b : list T) : Prop :=
  forall x,
    List.In x b -> ~List.In x a.

Lemma sets_disjoint_equiv : forall {T} (a b : list T),
    sets_disjoint a b ->
    sets_disjoint b a.
Proof. firstorder. Qed.

Definition disjoint_states_aux (A B : Formula)
           (xs ys : list Var) :=
  sets_disjoint xs ys /\
  next_state_vars A xs /\
  next_state_vars B ys.

Definition disjoint_states (A B : Formula) :=
  exists xs ys, disjoint_states_aux A B xs ys.

Definition merge_states (xs ys : list Var)
           (st1 st2 : state) : state :=
  fun x =>
    if List.existsb (fun y => if String.string_dec x y
                              then true else false) xs
    then st1 x
    else if List.existsb (fun y => if String.string_dec x y
                                   then true else false) ys
         then st2 x else st1 x.

CoFixpoint merge_traces (xs ys : list Var)
           (tr1 tr2 : trace) : trace :=
  Stream.Cons (merge_states xs ys (Stream.hd tr1)
                            (Stream.hd tr2))
              (merge_traces xs ys (Stream.tl tr1)
                            (Stream.tl tr2)).

Lemma traces_agree_sets_disjoint :
  forall tr1 tr2 xs ys,
    sets_disjoint xs ys ->
    exists tr,
      traces_agree tr1 tr xs /\
      traces_agree tr2 tr ys.
Proof.
  intros tr1 tr2 xs ys Hdisjoint.
  pose proof (@sets_disjoint_equiv _ _ _ Hdisjoint)
    as Hdisjoint2.
  unfold sets_disjoint in *.
  exists (merge_traces xs ys tr1 tr2).
  split.
  { generalize dependent tr1. generalize dependent tr2.
    cofix. unfold traces_agree. intros. constructor.
    simpl. unfold merge_states.
    { assert (existsb
                (fun y : string => if string_dec x y
                                   then true
                                   else false) xs = true).
      { apply existsb_exists. exists x.
        destruct (String.string_dec x x); auto. }
      { rewrite H0; auto. } }
    { unfold traces_agree in *. simpl. auto. } }
  { generalize dependent tr1. generalize dependent tr2.
    cofix. unfold traces_agree. intros. constructor.
    simpl. unfold merge_states.
    { assert (existsb
                (fun y : string => if string_dec x y
                                   then true
                                   else false) ys = true).
      { apply existsb_exists. exists x.
        destruct (String.string_dec x x); auto. }
      { rewrite H0; auto.
        assert (existsb
                  (fun y : string => if string_dec x y
                                     then true
                                     else false) xs = false).
        { apply Bool.not_true_is_false. intro.
          apply existsb_exists in H1. destruct H1.
          specialize (Hdisjoint _ H).
          destruct (String.string_dec x x0);
            try subst; intuition. }
        { rewrite H1. auto. } } }
    { unfold traces_agree in *. simpl. auto. } }
Qed.

Lemma disjoint_state_enabled :
  forall A B,
    disjoint_states A B ->
    Enabled A //\\ Enabled B |-- Enabled (A //\\ B).
Proof.
  intros A B Hdisjoint. breakAbstraction. intros tr Hen.
  unfold disjoint_states, disjoint_states_aux,
  next_state_vars in *.
  destruct Hen as [[trA HenA] [trB HenB]].
  destruct Hdisjoint as [xs [ys [Hdisjoint [HA HB]]]].
  pose proof (traces_agree_sets_disjoint trA trB) as Htr'.
  specialize (Htr' _ _ Hdisjoint).
  destruct Htr' as [tr' [HAtr' HBtr']].
  exists tr'. split.
  { eapply HA. 2: apply HenA.
    unfold traces_agree in *. intros.
    apply Stream.Symmetric_stream_eq; auto. }
  { eapply HB. 2: apply HenB.
    unfold traces_agree in *. intros.
    apply Stream.Symmetric_stream_eq; auto. }
Qed.

Definition not_in_dec
           {T} (f : forall x y, {x = y} + {x <> y})
           (a : list T) x : bool :=
  List.forallb (fun y => if f x y
                         then false
                         else true) a.

Definition sets_disjoint_dec
           {T} (f : forall x y, {x = y} + {x <> y})
           (a b : list T) : bool :=
  List.forallb (not_in_dec f b) a.

Lemma sets_disjoint_dec_ok :
  forall {T} f (a b : list T),
    sets_disjoint_dec f a b = true ->
    sets_disjoint a b.
Proof.
  unfold sets_disjoint, sets_disjoint_dec. intros.
  pose proof List.forallb_forall.
  specialize (H1 _ (not_in_dec f b) a).
  destruct H1. intuition.
  specialize (H4 _ H3).
  clear - H4 H0.
  unfold not_in_dec in *.
  pose proof List.forallb_forall.
  specialize
    (H _ (fun y : T => if f x y then false else true) b).
  destruct H. intuition. specialize (H2 _ H0).
  destruct (f x x); auto; discriminate.
Qed.

Ltac decide_disjoint_var_sets :=
  apply (sets_disjoint_dec_ok String.string_dec);
  reflexivity.


(*
  Fixpoint get_vars_term (t : Term) : list Var :=
    match t with
    | VarNextT t | VarNowT t => t :: nil
    | NatT _ | RealT _ => nil
    | PlusT a b | MinusT a b | MultT a b =>
         get_vars_term a ++
         get_vars_term b
    | InvT a | CosT a | SinT a | SqrtT a | ArctanT a =>
         get_vars_term a
    end.

  Fixpoint get_vars_formula (f : Formula) : list Var :=
    match f with
    | Always a | Eventually a | Enabled a =>
         get_vars_formula a
    | And a b | Or a b | Imp a b =>
         get_vars_formula a ++
         get_vars_formula b
    | Rename _ a => get_vars_formula a
    | Comp l r _ => get_vars_term l ++
         get_vars_term r
    | _ => nil
    end.
*)

Fixpoint can_get_vars_formula (f : Formula) : bool :=
  match f with
  | Always a | Eventually a | Enabled a =>
                              can_get_vars_formula a
  | And a b | Or a b | Imp a b =>
                       andb (can_get_vars_formula a)
                            (can_get_vars_formula b)
  | Comp _ _ _ => true
  | TRUE | FALSE => true
  | _ => false
  end.

Lemma get_vars_next_state_vars :
  forall A,
    can_get_vars_formula A = true ->
    next_state_vars A (get_next_vars_formula A).
Proof.
Admitted.
(*
    induction A; simpl; try discriminate;
    unfold state_vars in *; simpl; intros.
    - admit.
    - apply andb_prop in H.
      unfold traces_agree in *.
      split; intros;
      (split).
       [ eapply IHA1 | eapply IHA2 ]; try tauto).
       intros; try apply H0; intros).
      apply List.in_or_app; auto).
    - apply andb_prop in H.
      unfold traces_agree in *.
      destruct H1; [ left; eapply IHA1 | right; eapply IHA2 ];
      try tauto; intros; try apply H0; try tauto;
      apply List.in_or_app; auto.
    - apply andb_prop in H.
      unfold traces_agree in *.
      eapply IHA2; try tauto; intros; try apply H0.
      { apply List.in_or_app; auto. }
      { apply H1.
 *)

Lemma formulas_disjoint_state :
  forall A B,
    can_get_vars_formula A = true ->
    can_get_vars_formula B = true ->
    sets_disjoint_dec String.string_dec
                      (get_next_vars_formula A)
                      (get_next_vars_formula B) = true ->
    disjoint_states A B.
Proof.
  unfold disjoint_states. intros.
  exists (get_next_vars_formula A).
  exists (get_next_vars_formula B).
  apply sets_disjoint_dec_ok in H1.
  unfold disjoint_states_aux. split; auto.
  apply get_vars_next_state_vars in H.
  apply get_vars_next_state_vars in H0.
  auto.
Qed.
