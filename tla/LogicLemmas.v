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

End logic.