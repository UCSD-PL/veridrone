Require Import Coq.Reals.Reals.
Require Import TLA.TLA.
Require Import Examples.System2.

Set Implicit Arguments.
Set Strict Implicit.

Local Open Scope string_scope.

Section quadcopter.
  Variable D : ActionFormula.
  Variable delta : R.

  Definition roll  : Var := "theta".
  Definition pitch : Var := "phi".

  Definition max_angle : R := Rdiv PI 6.

  Local Open Scope HP_scope.

  Definition W_quadcopter : Evolution :=
    fun st' =>
           st' "x" = "vx" //\\ st' "y" = "vy" //\\ st' "z" = "vz"
      //\\ st' "vx" = "a" * cos( pitch ) * sin( roll )
      //\\ st' "vy" = "a" * sin( pitch )
      //\\ st' "vz" = "a" * cos( pitch ) * cos( roll )
      //\\ st' pitch = 0 //\\ st' roll = 0
      //\\ -- max_angle <= pitch <= max_angle
      //\\ -- max_angle <= roll <= max_angle.

  Definition quadcopter : ActionFormula :=
    Sys D W_quadcopter delta.

  Definition Quadcopter : ActionFormula :=
    System D W_quadcopter delta.
End quadcopter.