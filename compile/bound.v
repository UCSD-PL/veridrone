Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.lib.Integers.
Require Import Coq.Reals.Rdefinitions.
Require Import List.
Import ListNotations.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import compcert.flocq.Core.Fcore_defs.
Require Import compcert.flocq.Appli.Fappli_IEEE.
Require Import compcert.flocq.Appli.Fappli_IEEE_bits.

(*
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.

Require Import ExtLib.Structures.Traversable. (* for sequence function *)
Require Import ExtLib.Data.List.
*)

Require Import source.

Require Import Coq.Reals.Raxioms.
Require Import compcert.flocq.Appli.Fappli_IEEE.
Require Import compcert.flocq.Core.Fcore_Raux.
Require Import compcert.flocq.Core.Fcore_generic_fmt.

Definition custom_fst (x:Term*Term*Formula) := match x with 
| (f,s,t) => f
end.

Definition custom_snd (x:Term*Term*Formula) := match x with 
| (f,s,t)=> s
end.

Definition custom_third (x:Term*Term*Formula) := match x with 
| (f,s,t) => t
end.

Definition e := bpow radix2 (- (53) + 1).
Local Open Scope HP_scope.
Fixpoint bound_term x := match x with
| VarNowN var => (RealT R0,RealT R0, TRUE)
| NatN n => (RealT (INR n),RealT (INR n) , TRUE)
| FloatN f =>( (RealT (B2R _ _ f), RealT (B2R _ _ f)), TRUE)
| PlusN t1 t2 => (((custom_fst (bound_term t1) + custom_fst (bound_term t2))* (RealT R1 - RealT e)) ,
((custom_snd (bound_term t1) + custom_snd (bound_term t2))* (RealT R1 + RealT e)),
RealT ((B2R _ _ (custom_eval_expr t1) + B2R _ _ (custom_eval_expr t2)))> RealT R0)
| MinusN t1 t2 => (((custom_fst (bound_term t1) - custom_snd (bound_term t2))* (RealT R1 - RealT e)) ,
((custom_snd (bound_term t1) - custom_fst (bound_term t2)) * (RealT R1 + RealT e)), RealT ((B2R _ _ (custom_eval_expr t1) - B2R _ _ (custom_eval_expr t2)))> RealT R0)
| MultN t1 t2 => (((custom_fst (bound_term t1)* custom_fst (bound_term t2)) * (RealT R1 - RealT e)) ,
((custom_snd (bound_term t1) * custom_snd (bound_term t2))* (RealT R1 + RealT e)),
((RealT ((B2R _ _ (custom_eval_expr t1) * B2R _ _ (custom_eval_expr t2)))> RealT R0) /\ RealT (B2R _ _ (custom_eval_expr t1)) > R0  /\ 
RealT (B2R _ _ (custom_eval_expr t2)) > R0)
)
end.

Local Close Scope HP_scope.

Definition boundDef expr s1 s2 tr :=
(eval_formula (custom_third (bound_term expr)) tr) -> (eval_term (custom_fst (bound_term expr)) s1 s2 <= B2R _ _ (custom_eval_expr expr) <= eval_term (custom_snd (bound_term expr)) s1 s2)%R.



Lemma new_bound_proof : (forall (tr:Semantics.trace) expr, (boundDef expr (Semantics.hd tr) (Semantics.hd (Semantics.tl tr)) tr)).
admit.
Qed.
