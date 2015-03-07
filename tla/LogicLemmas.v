Require Export Charge.Logics.ILogic.

Section logic.
  Context {L : Type}.
  Context {ILO : ILogicOps L}.
  Context {IL : ILogic L}.

  Theorem lcut : forall P Q R : L,
      P |-- R ->
      P |-- R -->> Q ->
      P |-- Q.
  Proof.
    intros.
    eapply landAdj in H0.
    etransitivity; [ | eassumption ].
    eapply landR. reflexivity. assumption.
  Qed.

  Theorem limplAdj_true : forall P Q,
      P |-- Q ->
      ltrue |-- P -->> Q.
  Proof.
    intros. apply limplAdj. apply landL2. assumption.
  Qed.

  Theorem landAdj_true : forall P Q,
      ltrue |-- P -->> Q ->
      P |-- Q.
  Proof.
    intros. apply landAdj in H. rewrite <- H.
    apply landR. apply ltrueR. reflexivity.
  Qed.

  Lemma lapply : forall P Q R,
      P |-- Q -->> R ->
      P |-- Q ->
      P |-- R.
  Proof. intros; eapply lcut; eauto. Qed.
End logic.

Ltac charge_split := apply landR.

Ltac charge_search_prems found :=
  match goal with
  | |- ?X |-- ?Y =>
    solve [ found
          | apply landL1 ; charge_search_prems found
          | apply landL2 ; charge_search_prems found ]
  end.

Ltac charge_assumption :=
  charge_search_prems reflexivity.

Ltac charge_intro :=
  first [ apply lforallR; intro
        | apply limplAdj_true
        | apply limplAdj ].

Ltac charge_intros :=
  repeat match goal with
         | |- _ |-- _ -->> _ =>
           charge_intro
         end.

Ltac charge_trivial := apply ltrueR.

Ltac charge_use :=
  eapply lapply; [ charge_assumption | ].

Ltac ends_with H ABC C :=
  let rec go k ABC :=
      match ABC with
      | C => k
      | _ -->> ?BC =>
        let k' := (k; first [ apply landAdj_true in H | apply landAdj in H ]) in
        go k' BC
      end
  in
  go ltac:(idtac) ABC.

Ltac charge_apply H :=
  match type of H with
  | _ |-- ?X =>
    match goal with
    | |- _ |-- ?Y =>
      ends_with H X Y ; etransitivity ; [ | eapply H ]
    end
  end.

Ltac charge_tauto :=
  repeat charge_split ;
  solve [ charge_assumption
        | charge_trivial
        | charge_intro; repeat charge_intro; charge_tauto
        | charge_split; solve [ charge_tauto ]
        | match goal with
          | H : _ |-- _ |- _ =>
            charge_apply H ; charge_tauto
          end
        | charge_use ; charge_tauto ].

Section logic2.
  Context {L : Type}.
  Context {ILO : ILogicOps L}.
  Context {IL : ILogic L}.

  Lemma uncurry : forall P Q R,
      (P //\\ Q -->> R) -|- (P -->> Q -->> R).
  Proof.
    intros. split.
    { charge_tauto. }
    { charge_intro.
      eapply lapply. eapply lapply. charge_assumption.
      charge_tauto. charge_tauto. }
  Qed.

  Lemma forget_prem : forall P Q,
      |-- P -> Q |-- P.
  Proof. intros; charge_tauto. Qed.

  Lemma lrevert : forall P Q,
      |-- P -->> Q ->
      P |-- Q.
  Proof. intros; charge_tauto. Qed.

End logic2.