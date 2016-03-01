Require Import Coq.Reals.Rdefinitions.
Require Import ExtLib.Structures.Applicative.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILEmbed.
Require Import ChargeCore.Tactics.Tactics.
Require Import SLogic.Logic.
Require Import SLogic.LTLNotation.
Require Import SLogic.Instances.
Require Import SLogic.BasicProofRules.
Require Import SLogic.BoundingFunctions.

Local Open Scope LTL_scope.

Section Robustness.

  Variable state : Type.
  (* Input cost - this quantifies the disturbance. *)
  Variable IC : StateVal state R.
  (* Output cost - this quantifies the deviation
     from the nominal behavior. *)
  Variable OC : StateVal state R.
  (* The StateVal tracking time. *)
  Variable t : StateVal state R.
  (* Bounding function giving decay over time. *)
  Variable mu : R -> R -> R.
  (* Bounding function giving how much deviation
     is allowed for a given disturbance. *)
  Variable gamma : R -> R.

  (* In control theory terms, this captures
     input-to-state stability, which is defined as

       |x(t)| <= mu(|x(0)|,t) + gamma(||u||_inf)

     where ||u||_inf is the supremum norm of the
     disturbance. In our framework, OC = |x(t)| and
     IC = u. *)
  Definition robust : TraceProp state :=
    embed (KL_fun mu) //\\ embed (K_inf_fun gamma) //\\
    Exists OC_0 : R, [!(pure OC_0 `= OC)] //\\
    Exists t_0 : R,  [!(pure t_0 `= t)] //\\
    Forall sup : R,
      [][!(IC `<= pure sup)] -->>
      [][!(OC `<= `mu (pure OC_0) (t `- (pure t_0)) `+ `gamma (pure sup))].

  (* Here is the stronger definition of robustness. *)
  Definition robust2 : TraceProp state :=
    []robust.

  Lemma robust_robust2 :
    forall G,
      G |-- robust ->
      G |-- []G ->
      G |-- []robust.
  Proof.
    intros. rewrite H0. apply Proper_always_lentails.
    assumption.
  Qed.

End Robustness.
