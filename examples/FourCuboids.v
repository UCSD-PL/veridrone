Require Import Logic.Logic.
Require Import Logic.ProofRules.
Require Import Examples.System.
Require Import Examples.Cuboid.
Require Import Coq.Reals.Reals.

Module FourCuboids (A : CuboidParams)
       (B C D  : CuboidParams with Definition d := A.d with Definition g := A.g).

  Module C1 := CuboidShim A.
  Module C2 := CuboidShim B.
  Module C3 := CuboidShim C.
  Module C4 := CuboidShim D.

  Definition IndInv : StateFormula :=
    (C1.IndInv \\// C2.IndInv) \\//
    (C3.IndInv \\// C4.IndInv).

  Definition Next : ActionFormula :=
    SysDisjoin (C1.IndInv \\// C2.IndInv)
               (SysDisjoin C1.IndInv C1.Next C2.IndInv C2.Next)
               (C3.IndInv \\// C4.IndInv)
               (SysDisjoin C3.IndInv C3.Next C4.IndInv C4.Next).

  Definition Safe : StateFormula :=
    (C1.Safe \\// C2.Safe) \\//
    (C3.Safe \\// C4.Safe).

  Local Open Scope HP_scope.

  Lemma FourCuboids_safe :
    |-- (IndInv //\\ TimeBound A.d) //\\ []SysSystem Next -->> []Safe.
  Proof with (refine _).
    rewrite Inductively.Preserves_Inv_simple...
    { unfold IndInv, Safe. rewrite <- C1.IndInv_impl_Safe.
      rewrite <- C2.IndInv_impl_Safe. rewrite <- C3.IndInv_impl_Safe.
      rewrite <- C4.IndInv_impl_Safe. apply Always_imp.
      unfold B.d, C.d, D.d. charge_intros. charge_cases; charge_tauto. }
    { apply SafeAndReactive_TimedPreserves.
      apply SysDisjoin_SafeAndReactive...
      { apply SysDisjoin_SafeAndReactive...
        { unfold SafeAndReactive; charge_split; [ apply C1.TimedPreserves_Next | apply C1.SysNeverStuck_Next ]. }
        { unfold SafeAndReactive; charge_split; [ apply C2.TimedPreserves_Next | apply C2.SysNeverStuck_Next ]. } }
      { apply SysDisjoin_SafeAndReactive...
        { unfold SafeAndReactive; charge_split; [ apply C3.TimedPreserves_Next | apply C3.SysNeverStuck_Next ]. }
        { unfold SafeAndReactive; charge_split; [ apply C4.TimedPreserves_Next | apply C4.SysNeverStuck_Next ]. } } }
  Qed.

End FourCuboids.
