Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import Examples.System.
Require Import Examples.SensorWithError.
Require Import Examples.SensorWithDelay.
Require Import Examples.FirstDerivShimCtrl.

Open Scope HP_scope.
Open Scope string_scope.

Definition CtrlSenseDelaySys ub d :=
  Sys ("Vmax"::"Vmin"::"a"::nil)%list ("v"::nil)%list
      (SensorWithDelay.Init "v" "Vmax" "Vmin" "a" //\\
                            FirstDerivShimCtrl.Init ub d)
      (SensorWithDelay.Sense "v" "Vmax" "Vmin" "a" d //\\
                             FirstDerivShimCtrl.Ctrl ub d)
      FirstDerivShimCtrl.world TRUE d.

Ltac sys_apply_with_weaken H :=
  eapply imp_trans; [ | apply H ];
  try (charge_intros; eapply Sys_weaken;
       try solve [ apply ltrueR
                 | apply all_in_dec_ok ; reflexivity
                 | apply imp_id
                 | reflexivity ]).

Theorem ctrl_sense_delay_safe : forall ub d,
  |-- CtrlSenseDelaySys ub d -->> []"v" <= ub.
Proof.
  intros ub d.
  apply imp_trans with
  (F2:=[]("v" <= ub //\\ SensorWithDelay.SenseSafe "v" "Vmax" "Vmin")).
  - apply compose_discrete.
    + sys_apply_with_weaken SensorWithDelay.sense_safe;
      reflexivity.
    + tlaIntro.
      generalize (FirstDerivShimCtrl.ctrl_safe ub d TRUE); intro H.
      charge_apply H; clear H.
      charge_split.
      { unfold SenseSafe.
        rewrite landC. tlaRevert. apply always_imp.
        solve_linear. }
      { erewrite Sys_weaken; try solve [ charge_assumption
                                       | apply all_in_dec_ok ; reflexivity
                                       | reflexivity ]. }
  - apply always_imp. charge_tauto.
Qed.

Definition CtrlSenseErrorSys ub d err :=
  Sys ("a"::nil)%list ("v"::"Vmax"::"Vmin"::nil)%list
      (SensorWithError.Init "v" "Vmax" "Vmin" //\\
                            FirstDerivShimCtrl.Init ub d)
      (FirstDerivShimCtrl.Ctrl ub d)
      FirstDerivShimCtrl.world (SensorWithError.Sense "v" "Vmax" "Vmin" err) d.

(*
      Ltac charge_apply' H :=
        match type of H with
        | _ |-- ?X =>
          match goal with
          | |- _ |-- ?Y =>
            let H' := fresh in
            generalize H; intro H' ; idtac "1" ;
            ends_with H' X Y; etransitivity; [ idtac | eapply H' ]
          end
        | ?T -> _ =>
          idtac "2" ;
          let x' := fresh in evar (x' : T) ; charge_apply' (H x')
        | forall x : ?T, _ =>
          idtac "3" ;
          let x' := fresh in evar (x' : T) ; charge_apply' (H x')
        end.
 *)

Theorem ctrl_sense_error_safe : forall ub d err,
  |-- CtrlSenseErrorSys ub d err -->> []"v" <= ub.
Proof.
  intros ub d err.
  apply imp_trans with
  (F2:=[]("v" <= ub //\\ SensorWithError.SenseSafe "v" "Vmax" "Vmin")).
  - apply compose_world.
    + charge_intro.
      generalize (SensorWithError.sense_safe "v" "Vmax" "Vmin" err world d); intro H.
      charge_apply H.
      eapply Sys_weaken; try solve [ apply all_in_dec_ok; reflexivity | reflexivity ].
    + charge_intro.
      generalize (FirstDerivShimCtrl.ctrl_safe ub d ltrue); intro H.
      charge_apply H.
      charge_split.
      { rewrite landC. tlaRevert.
        apply always_imp. solve_linear. }
      { etransitivity; [ | eapply Sys_weaken ];
        try solve [ charge_assumption | apply all_in_dec_ok; reflexivity | reflexivity ]. }
  - apply always_imp. charge_tauto.
Qed.