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
  Definition gravity : R := (- 98 / 10)%R.

  Definition max_angle : R := Rdiv PI 6.

  Local Open Scope HP_scope.

  Definition small_angle_constraint : StateFormula :=
           -- max_angle <= pitch <= max_angle
      //\\ -- max_angle <= roll <= max_angle.

  Definition W_quadcopter : Evolution :=
    fun st' =>
      small_angle_constraint -->>
      (     st' "x" = "vx" //\\ st' "y" = "vy" //\\ st' "z" = "vz"
       //\\ st' "vx" = "a" * cos( pitch ) * sin( roll )
       //\\ st' "vy" = "a" * sin( pitch )
       //\\ st' "vz" = "a" * cos( pitch ) * cos( roll ) + gravity
       //\\ st' pitch = 0 //\\ st' roll = 0 //\\ st' "a" = 0).

  Definition W_quadcopter' : Evolution :=
    fun st' =>
           st' "x" = "vx" //\\ st' "y" = "vy" //\\ st' "z" = "vz"
      //\\ st' "vx" = "a" * cos( pitch ) * sin( roll )
      //\\ st' "vy" = "a" * sin( pitch )
      //\\ st' "vz" = "a" * cos( pitch ) * cos( roll ) + gravity
      //\\ st' pitch = 0 //\\ st' roll = 0 //\\ st' "a" = 0.


  Definition W_quadcopter_plane : Evolution :=
    fun st' =>
           st' "x" = "vx" //\\ st' "y" = "vy"
      //\\ st' "vx" = "a" * cos( "theta" )
      //\\ st' "vy" = "a" * sin( "theta" )
      //\\ st' "theta" = 0 //\\ st' "a" = 0.

(*
  Require Import TLA.ProofRules.

  Theorem W_quadcopter_plane_refinement
  : Continuous W_quadcopter |-- Rename ({{ "a" ~> "a" * }})%rename_scope (Continuous W_quadcopter_plane).
*)

  Definition quadcopter : ActionFormula :=
    Sys D W_quadcopter delta.

  Require Import TLA.ProofRules.

  Definition quadcopter' : ActionFormula :=
    Sys (D //\\ next small_angle_constraint) W_quadcopter' delta.

  Theorem quadcopter_quadcopter'
  : quadcopter' |-- quadcopter.
  Proof.
    unfold quadcopter, quadcopter', Sys.
    intros.
    charge_split; try charge_assumption.
    charge_cases.
    { charge_left. unfold Discr. charge_tauto. }
    { charge_right.
      unfold World, W_quadcopter, W_quadcopter'.
      charge_split; [ | charge_tauto ].
      etransitivity.
      2: eapply Proper_Continuous_lentails.
      charge_assumption.
      unfold mkEvolution.
      eapply Evolution_lentails_lentails. intros.
      charge_tauto. }
  Qed.

  Definition Quadcopter : ActionFormula :=
    System D W_quadcopter delta.
End quadcopter.