Require Import Charge.Logics.ILogic.

Section any_all.
  Context {L} {LL : ILogicOps L}.

  Fixpoint AnyOf  (ls : list L) : L :=
    match ls with
    | nil => lfalse
    | cons l ls => l \\// AnyOf ls
    end.

  Fixpoint AllOf (ls : list L) : L :=
    match ls with
    | nil => ltrue
    | cons l ls => l //\\ AllOf ls
    end.
End any_all.
