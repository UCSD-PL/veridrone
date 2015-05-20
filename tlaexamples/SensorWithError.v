Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import Examples.System.

Open Scope HP_scope.

Section SensorWithError.

  Variable x : Var.
  Variable Xmax : Var.
  Variable Xmin : Var.
  Variable err : R.

  Definition Sense : Formula :=
    Xmax! <= Xmin! + err //\\ Xmin! <= x! <= Xmax!.

  Definition SenseSafe : Formula :=
    Xmin <= x <= Xmax.

  Definition I : Formula := SenseSafe.

  Variable w : list DiffEq.
  Variable d : R.

  Definition SpecR : SysRec :=
    {| dvars := nil;
       cvars := (x::Xmax::Xmin::nil)%list;
       Init := I;
       Prog := ltrue;
       world := w;
       WConstraint := Sense;
       maxTime := d |}.

  Definition Spec := SysD SpecR.

  CoFixpoint forever {T} (v : T) : Stream.stream T :=
    Stream.Cons v (forever v).

  Lemma Enabled_action : forall P,
      (* is_action_formula P *) True ->
      (forall st, exists st',
            eval_formula P (Stream.Cons st (forever st'))) ->
      |-- Enabled P.
  Proof. Admitted.

  Lemma ex_state : forall (v : Var) (P : state -> Prop),
      (exists st, (exists val, P (fun v' => if String.string_dec v v' then val else st v'))) ->
      exists st, P st.
  Proof.
    intros. destruct H. destruct H. eauto.
  Qed.

  Lemma ex_state_any : forall (P : state -> Prop),
      (forall st, P st) ->
      exists st, P st.
  Proof.
    intros. exists (fun _ => 0%R). eauto.
  Qed.

  Lemma String_dec_refl : forall s, String.string_dec s s = left eq_refl.
  Proof.
  Admitted.

  Inductive Unique : list Var -> Prop :=
  | Unique_nil : Unique nil
  | Unique_cons : forall x xs, Unique xs -> ~List.In x xs -> Unique (x :: xs).

  Require Import Coq.Lists.List.

  Fixpoint find (v : Var) (vs : list Var) (a : nat) : option nat :=
    match vs with
    | nil => None
    | v' :: vs' => if String.string_dec v v' then Some a
                   else find v vs' (S a)
    end.

  Lemma Unique_neq : forall a b xs,
      Unique xs ->
      find a xs 0 <> find b xs 0 ->
      a <> b.
  Proof. Admitted.

  Hypothesis Different : Unique ("t" :: x :: Xmax :: Xmin :: nil).

  Fixpoint all_different (xs : list Var) : Prop :=
    match xs with
    | nil => True
    | x :: xs =>
      (fix rec xs' : Prop :=
         match xs' with
         | nil => all_different xs
         | x' :: xs' => x <> x' /\ rec xs'
         end) xs
    end.

  Theorem Unique_all_different : forall xs, Unique xs -> all_different xs.
  Proof. Admitted.

  Lemma SysSafe_sense : forall P, P |-- SysSafe SpecR.
  Proof.
    intros.
    apply SysSafe_rule; apply always_tauto.
    { eapply Enabled_action; auto.
      simpl.
      intros.
      eapply (@ex_state "t").
      eapply (@ex_state Xmax).
      eapply (@ex_state Xmin).
      eapply (@ex_state x).
      eapply ex_state_any; intro.
      repeat rewrite String_dec_refl.
      eapply Unique_all_different in Different. simpl in Different.
      repeat match goal with
             | |- context [ String.string_dec ?A ?B ] =>
               (destruct (String.string_dec A B); try solve [ intuition congruence ]); [ ]
             end.
      do 4 eexists. repeat split; eauto. reflexivity. }
  Qed.

  Theorem sense_safe :
    Spec |-- []SenseSafe.
  Proof.
    eapply Sys_by_induction
      with (IndInv := SenseSafe) (A := ltrue).
    + tlaIntuition.
    + unfold Spec, SpecR. tlaAssume.
    + apply SysSafe_sense.
    + tlaAssume.
    + eapply BasicProofRules.always_tauto. charge_tauto.
    + tlaAssume.
    + red. solve_linear.
    + solve_linear.
    + solve_linear.
  Qed.

End SensorWithError.

Close Scope HP_scope.