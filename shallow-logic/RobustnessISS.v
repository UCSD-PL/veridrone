Require Import ExtLib.Structures.Applicative.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import Coq.Reals.Rdefinitions.
Require Import SLogic.Logic.
Require Import SLogic.LTLNotation.
Require Import SLogic.Instances.
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

  (* In control theory terms, this captures
     input-to-state stability, which is defined as

       |x(t)| <= mu(|x(0)|,t) + gamma(||u||_inf)

     where ||u||_inf is the supremum norm of the
     disturbance. In our framework, OC = |x(t)| and
     IC = u. *)
  Definition mu_gamma_robust
    (mu : R -> R -> R) (gamma : R -> R) :
    TraceProp state :=
    embed (KL_fun mu) //\\ embed (K_inf_fun gamma) //\\
    Exists OC_0 : R, [!(pure OC_0 `= OC)] //\\
    Forall sup : R,
      [][!(IC `<= `sup)] -->>
      [][!(OC `<= `mu `OC_0 t `+ `gamma `sup)].

  (* Here is the existential version of input-to-state
     stability. *)
  Definition robust : TraceProp state :=
    Exists mu : R -> R -> R,
    Exists gamma : R -> R,
      mu_gamma_robust mu gamma.

  (* Here is a stronger version of input-to-state
     stability that guarantees that once disturbances
     are removed, the system returns to its nominal
     behavior. *)
  Definition robust2 : TraceProp state :=
    Exists mu : R -> R -> R,
    Exists gamma : R -> R,
      [](mu_gamma_robust mu gamma).

End Robustness.