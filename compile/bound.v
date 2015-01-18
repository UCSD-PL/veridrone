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

Lemma stupid : bounded 53 1024 5 2 = true. 
admit. Qed.


Local Open Scope HP_scope.
Require Import Coq.Reals.Raxioms.
Definition e := 2%R. 
Fixpoint bound_term x := match x with
| VarNowN var => (RealT R0,RealT R0 ) 
| NatN n => (RealT (INR n),RealT (INR n))
| FloatN f => (RealT (B2R _ _ f), RealT (B2R _ _ f))
| PlusN t1 t2 => (((fst (bound_term t1) + fst (bound_term t2))* (RealT R1 - RealT e)) ,
((snd (bound_term t1) + snd (bound_term t2))* (RealT R1 + RealT e)))
| MinusN t1 t2 => (((fst (bound_term t1) - snd (bound_term t2))* (RealT R1 - RealT e)) ,
((snd (bound_term t1) - fst (bound_term t2)) * (RealT R1 + RealT e)))
| MultN t1 t2 => (((fst (bound_term t1)* fst (bound_term t2)) * (RealT R1 - RealT e)) ,
((snd (bound_term t1) * snd (bound_term t2))* (RealT R1 + RealT e)))
end.



Definition clightExpr expr := evalState (nowTerm_to_clight expr) nil.


Definition valToR val := match val with 
| Values.Vfloat f => B2R _ _ f
| _ => R0 (*need to implement this for other things as well*)
end.  
Local Close Scope HP_scope.
Local Close Scope SrcLang_scope.
Local Open Scope R_scope.


Fixpoint bound  expr s1 s2:= match expr with
| PlusN x1 x2 =>  (forall fx1 fx2, (((eval_term (fst (bound_term x1)) s1 s2)%R <= (B2R _ _ fx1)%R <= 
(eval_term (snd (bound_term x1)) s1 s2)%R) /\ ((eval_term (fst (bound_term x2)) s1 s2)<= B2R _ _ fx2 <= 
(eval_term (snd (bound_term x2)) s1 s2))) -> ((forall ge e te mem val, 
((eval_expr ge e te mem (clightExpr (PlusN (FloatN fx1) (FloatN fx2))) val)) ->  
((eval_term (fst (bound_term expr)) s1 s2) <= (valToR val) <= (eval_term (snd (bound_term expr)) s1 s2)))))

| MultN x1 x2 =>  (forall fx1 fx2, (((eval_term (fst (bound_term x1)) s1 s2)%R <= (B2R _ _ fx1)%R <= 
(eval_term (snd (bound_term x1)) s1 s2)%R) /\ ((eval_term (fst (bound_term x2)) s1 s2)<= B2R _ _ fx2 <= 
(eval_term (snd (bound_term x2)) s1 s2))) -> ((forall ge e te mem val, 
((eval_expr ge e te mem (clightExpr (MultN (FloatN fx1) (FloatN fx2))) val)) ->  
((eval_term (fst (bound_term expr)) s1 s2) <= (valToR val) <= (eval_term (snd (bound_term expr)) s1 s2)))))

| MinusN x1 x2 =>  (forall fx1 fx2, (((eval_term (fst (bound_term x1)) s1 s2)%R <= (B2R _ _ fx1)%R <= (eval_term (snd (bound_term x1)) s1 s2)%R) /\ ((eval_term (fst (bound_term x2)) s1 s2)<= B2R _ _ fx2 <= (eval_term (snd (bound_term x2)) s1 s2))) -> ((forall ge e te mem val, 
((eval_expr ge e te mem (clightExpr (MinusN (FloatN fx1) (FloatN fx2))) val)) ->  ((eval_term (fst (bound_term expr)) s1 s2) <= (valToR val) <= (eval_term (snd (bound_term expr)) s1 s2)))))

| NatN n => True
| FloatN f =>  True 
| VarNowN var => True (*this needs to changed*)
end.
Print eval_expr.
Print sem_binary_operation.
Print sem_add.
Print Floats.Float.add.
Print b64_plus.
Print eval_expr.


Eval compute in (Floats.Float.add (B754_finite 53 1024 true 5 2 stupid) (B754_finite 53 1024 true 5 2 stupid)).

Print B754_finite. 
Definition num:= B754_finite 53 1024 true 5 2 stupid.
Eval vm_compute in (B2R _ _ num).


Print B2R.
Print Floats.Float.add.

Print Bplus. 
Print eq_refl.
Print binary_float.
Local Open Scope HP_scope.
Lemma bound_proof : (forall (tr:Semantics.trace) expr, (bound expr (Semantics.hd tr) (Semantics.hd (Semantics.tl tr)))).

intros.
simpl in *.
unfold bound.
simpl in *. 
destruct expr.
- intuition. 
- intuition. 
- intuition.
- destruct expr1.
destruct expr2. 
+ intros.
Check eval_Ebinop.
unfold clightExpr in H0.
compute in H0.
Print eval_expr.

Check eval_Ebinop.
Check  sem_binary_operation .
Check Econst_float.
Check Floats.float.
Print Floats.float.
Print binary64.
Print binary_float.


Print Floats.Float.add.

Print binary64.
Print binary_float.
Check B754_finite.
Lemma stupid : bounded 53 1024 5 2 = true. 
admit. 
Qed.
Print Floats.Float.add.
Eval compute in (Floats.Float.add (B754_finite 53 1024 true 5 2 stupid) (B754_finite 53 1024 true 5 2 stupid)).
Print Floats.Float.add.
Print b64_plus.
Check  Floats.Float.binop_pl.
Eval typeof Econst_float 
Eval compute in  sem_binary_operation Oadd 
Check Econst_float.
Check 
Check Ebinop.
eapply eval_Ebinop in H0.
Local Close Scope HP_scope.
Local Open Scope SrcLang_scope.
Eval compute in evalState (nowTerm_to_clight (FloatN fx1 + FloatN fx2)).
unfold nowTerm_to_clight in H0.
unfold evalState in H0.

unfold runState in H0.
eapply eval_Ebinop in H0.
unfold eval_expr in H0.
Check zero_deriv_term.
Check bound.
