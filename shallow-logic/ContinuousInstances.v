Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import Charge.Logics.ILogic.
Require Import SLogic.Continuous.

Section with_state.

  Variable state : Type.

  Let DiffVal := DiffVal state.
  Let SimpleDiffVal := SimpleDiffVal state.
  Let DiffProp := DiffProp state.
  Let SimpleDiffProp := SimpleDiffProp state.
  Let ContProp := ContProp state.

  Global Instance Applicative_Diff {V} {Dv}
    : Applicative (DiffVal V Dv) :=
    { pure := fun _ x => fun _ _ => x
      ; ap := fun _ _ f x => fun d st =>
                               (f d st) (x d st)
    }.

  Global Instance Functor_Diff {V} {Dv}
    : Functor (DiffVal V Dv) :=
    { fmap := fun _ _ f x => ap (pure f) x }.

  Global Instance Applicative_SimpleDiff {ls}
    : Applicative (SimpleDiffVal ls) :=
    { pure := fun _ x => fun _ _ => x
      ; ap := fun _ _ f x => fun d st =>
                               (f d st) (x d st)
    }.

  Global Instance Functor_SimpleDiff {ls}
    : Functor (SimpleDiffVal ls) :=
    { fmap := fun _ _ f x => ap (pure f) x }.

  Global Instance ILogicOps_DiffProp {V} {Dv}
    : ILogicOps (DiffProp V Dv) :=
    @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogicOps_ContProp : ILogicOps ContProp :=
    @ILInsts.ILFun_Ops _ _ _.

  Global Instance ILogic_DiffProp {V} {Dv}
    : ILogic (DiffProp V Dv) := _.
  Global Instance ILogic_ContProp : ILogic ContProp := _.

End with_state.