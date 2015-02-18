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

Require Import ExtLib.Programming.Extras.


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



Definition boundDef expr s1 s2 tr :=
(eval_formula (custom_third (bound_term expr)) tr) -> eval_term (custom_fst (bound_term expr)) s1 s2 <= B2R _ _ (custom_eval_expr expr) <= eval_term (custom_snd (bound_term expr)) s1 s2.



Lemma new_bound_proof : (forall (tr:Semantics.trace) expr, (newBound expr (Semantics.hd tr) (Semantics.hd (Semantics.tl tr)) tr)).
unfold newBound.
intros tr expr.
induction expr.
+ unfold custom_eval_expr.
unfold bound_term.
simpl.
unfold custom_float_zero.
Transparent B2R.
unfold B2R.
intuition.
+ revert n. 
unfold bound_term.
unfold fst.
unfold custom_eval_expr.
simpl in *.
intros.
admit. (*proving bound of natural numbers*)
+ simpl.
intuition.
+ unfold custom_eval_expr.
unfold bound_term.
unfold custom_third.
unfold eval_formula.
unfold eval_comp.
simpl.
remember  ((fix custom_eval_expr (t : NowTerm) :
            binary_float custom_prec custom_emax :=
            match t with
            | VarNowN _ => custom_float_zero
            | NatN n => nat_to_float n
            | FloatN f => f
            | (t1 + t2)%SL =>
                Bplus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (t1 - t2)%SL =>
                Bminus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (t1 * t2)%SL =>
                Bmult custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            end) expr1)  as eval_expr.
remember ((fix custom_eval_expr (t : NowTerm) :
            binary_float custom_prec custom_emax :=
            match t with
            | VarNowN _ => custom_float_zero
            | NatN n => nat_to_float n
            | FloatN f => f
            | (t1 + t2)%SL =>
                Bplus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (t1 - t2)%SL =>
                Bminus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (t1 * t2)%SL =>
                Bmult custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            end) expr2)  as eval_expr2.

unfold custom_eval_expr in IHexpr1.
unfold custom_eval_expr in IHexpr2.
rewrite <- Heqeval_expr2 in IHexpr2.
rewrite <- Heqeval_expr in IHexpr1.
clear Heqeval_expr2 Heqeval_expr.
pose proof Bplus_correct as bplus_correct.
specialize (bplus_correct custom_prec custom_emax eq_refl eq_refl Floats.Float.binop_pl mode_NE eval_expr eval_expr2).
destruct eval_expr eqn:eval_expr_des.
* admit. (*zero case*)
* admit. (*infinty case*)
* admit. (*nan case*)
*
destruct eval_expr2 eqn:eval_expr2_des.
- admit. (*zero case*)
- admit. (*infinty case*)
- admit. (*nan case*)
- unfold is_finite in bplus_correct.
Lemma truth : true = true.
intuition.
Qed.
specialize (bplus_correct truth).
specialize (bplus_correct truth).
remember (Rlt_bool (Rabs (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (B2R custom_prec custom_emax eval_expr + B2R custom_prec custom_emax eval_expr2))) (bpow radix2 custom_emax)) as rltBoolInfo. destruct rltBoolInfo.
subst.
rewrite <- HeqrltBoolInfo in bplus_correct.
decompose [and] bplus_correct.
rewrite H.
split.
{- unfold bound_term in *.
remember (fst ((fix bound_term (x : NowTerm) : Term * Term :=
match x with
| VarNowN _ => (RealT 0, RealT 0)
| NatN n => (RealT (INR n), RealT (INR n))
| FloatN f =>
(RealT (B2R 53 1024 f), RealT (B2R 53 1024 f))
| (t1 + t2)%SL =>
(((fst (bound_term t1) + fst (bound_term t2)) *
(RealT 1 - RealT e))%HP,
((snd (bound_term t1) + snd (bound_term t2)) *
(RealT 1 + RealT e))%HP)
| (t1 - t2)%SL =>
(((fst (bound_term t1) - snd (bound_term t2)) *
(RealT 1 - RealT e))%HP,
((snd (bound_term t1) - fst (bound_term t2)) *
(RealT 1 + RealT e))%HP)
| (t1 * t2)%SL =>
((fst (bound_term t1) * fst (bound_term t2) *
(RealT 1 - RealT e))%HP,
(snd (bound_term t1) * snd (bound_term t2) *
(RealT 1 + RealT e))%HP)
end) expr1)) as lb1.
remember (fst
((fix bound_term (x : NowTerm) : Term * Term :=
match x with
| VarNowN _ => (RealT 0, RealT 0)
| NatN n => (RealT (INR n), RealT (INR n))
| FloatN f =>
(RealT (B2R 53 1024 f), RealT (B2R 53 1024 f))
| (t1 + t2)%SL =>
(((fst (bound_term t1) + fst (bound_term t2)) *
(RealT 1 - RealT e))%HP,
((snd (bound_term t1) + snd (bound_term t2)) *
(RealT 1 + RealT e))%HP)
| (t1 - t2)%SL =>
(((fst (bound_term t1) - snd (bound_term t2)) *
(RealT 1 - RealT e))%HP,
((snd (bound_term t1) - fst (bound_term t2)) *
(RealT 1 + RealT e))%HP)
| (t1 * t2)%SL =>
((fst (bound_term t1) * fst (bound_term t2) *
(RealT 1 - RealT e))%HP,
(snd (bound_term t1) * snd (bound_term t2) *
(RealT 1 + RealT e))%HP)
end) expr2)) as lb2.
unfold fst.
clear Heqlb1 Heqlb2 bplus_correct HeqrltBoolInfo H1 H H2.
remember (B2R custom_prec custom_emax
(B754_zero custom_prec custom_emax true)) as eval_expr.
compute in Heqeval_expr.
subst.
Require Import compcert.flocq.Prop.Fprop_relative.
pose proof relative_error as Rel_Err.
remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp.
specialize (Rel_Err radix2 round_fexp).
Lemma validFexpProof : Valid_exp (FLT_exp (3 - custom_emax - custom_prec) custom_prec).
unfold Valid_exp,custom_prec,custom_emax;
intros.
split.
intros.
unfold FLT_exp in *.
Search (Z-> Z ->{_}+{_}).
lia.
intros. split. unfold FLT_exp in *.
unfold FLT_exp in *.
lia.
intros. unfold FLT_exp in *.
lia.
Qed.
pose proof validFexpProof.
subst.

specialize (Rel_Err validFexpProof).
Definition custom_emin := (-1021)%Z.
specialize (Rel_Err custom_emin custom_prec).
Lemma precThm: (forall k : Z, (custom_emin < k)%Z -> (custom_prec <= k - FLT_exp (3-custom_emax - custom_prec) custom_prec k)%Z).
intros.
unfold custom_emax in *. unfold custom_prec in *. unfold FLT_exp. unfold custom_emin in *. 
unfold Z.max.
Search (Z->Z -> {_}+{_}).
pose proof Z_lt_ge_dec ((k - 53)%Z) ((3 - 1024 - 53)%Z).
pose (k - 53 ?= 3 - 1024 - 53)%Z.
Print Datatypes.Eq.
Search (_ -> Datatypes.comparison).
Print Cge.
destruct H0 eqn:H0_des. 
destruct (k - 53 ?= 3 - 1024 - 53)%Z eqn:des.
lia.  simpl in *. 
clear des.
simpl in *.
lia. 
lia.
destruct ( k - 53 ?= 3 - 1024 - 53)%Z.
lia.
lia.
lia.
 
Qed.
Locate FLT_exp.
Print FLT_exp.
Check FLT_exp_valid.
Print relative_error.
specialize (Rel_Err precThm (round_mode mode_NE)).
Definition choiceDef := (fun x => negb (Zeven x)).
specialize (Rel_Err (valid_rnd_N choiceDef)).
remember (B754_finite custom_prec custom_emax b m e0 e1) as f.
remember (B754_finite custom_prec custom_emax b0 m0 e2 e3) as f0.
specialize (Rel_Err ((B2R custom_prec custom_emax f +
B2R custom_prec custom_emax f0))).
destruct (Rle_dec (bpow radix2 custom_emin) (Rabs (B2R custom_prec custom_emax f + B2R custom_prec custom_emax f0))) as [noUnderflow|underflow].
apply Rel_Err in noUnderflow.
unfold custom_prec, custom_emax, custom_emin in *.
Lemma three : forall x1 x2 x3, x1 <=x2 <= x3 -> x1 <= x2.
intros.
intuition.
Qed.
pose proof three as three.
apply three in IHexpr2.
apply three in IHexpr1.
destruct (Rge_dec (B2R 53 1024 f + B2R 53 1024 f0) R0) as [suml|sumg]. {+
destruct (Rge_dec (round radix2 (FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (B2R 53 1024 f + B2R 53 1024 f0) -(B2R 53 1024 f + B2R 53 1024 f0)) R0) as [roundg | roundl].
-
unfold Rabs in *.
destruct Rcase_abs in noUnderflow.
* psatz R.
* destruct Rcase_abs in noUnderflow.
{+ psatz R.
}
{
+
unfold eval_term in *.
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
match t with
| VarNowT x => s1 x
| (x) !%HP => s2 x
| NatT n => INR n
| RealT r1 => r1
| (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
| (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
| (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
end) lb1 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb1.
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
match t with
| VarNowT x => s1 x
| (x) !%HP => s2 x
| NatT n => INR n
| RealT r1 => r1
| (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
| (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
| (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
end) lb2 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb2.
revert IHexpr1. intros IHexpr1.
revert IHexpr2. intros IHexpr2.
unfold e.
remember (round radix2 (FLT_exp (3 - 1024 - 53) 53)
(round_mode mode_NE) (B2R 53 1024 f + B2R 53 1024 f0)) as roundedValue.
remember (B2R 53 1024 f) as f1.
remember (B2R 53 1024 f0) as f2.
clear Heqelb1 r0 three r Rel_Err Heqelb2 H noUnderflow expr1 expr2 lb1 Heqf2 Heqf0 Heqf Heqf1 HeqroundedValue tr f f0 lb2 .
simpl .
psatz R.
}
- unfold Rabs in noUnderflow.
destruct Rcase_abs in noUnderflow.
* destruct Rcase_abs in noUnderflow.
admit. (*the case when the sum is negative*)
unfold eval_term in *.
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
match t with
| VarNowT x => s1 x
| (x) !%HP => s2 x
| NatT n => INR n
| RealT r1 => r1
| (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
| (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
| (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
end) lb1 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb1.
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
match t with
| VarNowT x => s1 x
| (x) !%HP => s2 x
| NatT n => INR n
| RealT r1 => r1
| (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
| (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
| (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
end) lb2 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb2.
revert IHexpr1 IHexpr2.
intros IHexpr1 IHexpr2.
clear expr1 expr2 m e0 e1 lb1 Heqf Heqelb1 Heqf0 Heqelb2 e2 e3 H Rel_Err roundl lb2 tr m0 three.
unfold e in *.
simpl in *.
psatz R.
* destruct Rcase_abs in noUnderflow.
admit. (*the case when the sum is negative*)
unfold eval_term in *.
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
match t with
| VarNowT x => s1 x
| (x) !%HP => s2 x
| NatT n => INR n
| RealT r1 => r1
| (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
| (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
| (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
end) lb1 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb1.
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
match t with
| VarNowT x => s1 x
| (x) !%HP => s2 x
| NatT n => INR n
| RealT r1 => r1
| (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
| (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
| (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
end) lb2 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb2.
unfold e in *.

psatz R.
}
admit. (*the case when the sum is negative*)
admit. (*the case when there is underflow*)
} unfold bound_term in *.
remember (snd
((fix bound_term (x : NowTerm) : Term * Term :=
match x with
| VarNowN _ => (RealT 0, RealT 0)
| NatN n => (RealT (INR n), RealT (INR n))
| FloatN f =>
(RealT (B2R 53 1024 f), RealT (B2R 53 1024 f))
| (t1 + t2)%SL =>
(((fst (bound_term t1) + fst (bound_term t2)) *
(RealT 1 - RealT e))%HP,
((snd (bound_term t1) + snd (bound_term t2)) *
(RealT 1 + RealT e))%HP)
| (t1 - t2)%SL =>
(((fst (bound_term t1) - snd (bound_term t2)) *
(RealT 1 - RealT e))%HP,
((snd (bound_term t1) - fst (bound_term t2)) *
(RealT 1 + RealT e))%HP)
| (t1 * t2)%SL =>
((fst (bound_term t1) * fst (bound_term t2) *
(RealT 1 - RealT e))%HP,
(snd (bound_term t1) * snd (bound_term t2) *
(RealT 1 + RealT e))%HP)
end) expr1)) as ub1.
remember (snd
((fix bound_term (x : NowTerm) : Term * Term :=
match x with
| VarNowN _ => (RealT 0, RealT 0)
| NatN n => (RealT (INR n), RealT (INR n))
| FloatN f =>
(RealT (B2R 53 1024 f), RealT (B2R 53 1024 f))
| (t1 + t2)%SL =>
(((fst (bound_term t1) + fst (bound_term t2)) *
(RealT 1 - RealT e))%HP,
((snd (bound_term t1) + snd (bound_term t2)) *
(RealT 1 + RealT e))%HP)
| (t1 - t2)%SL =>
(((fst (bound_term t1) - snd (bound_term t2)) *
(RealT 1 - RealT e))%HP,
((snd (bound_term t1) - fst (bound_term t2)) *
(RealT 1 + RealT e))%HP)
| (t1 * t2)%SL =>
((fst (bound_term t1) * fst (bound_term t2) *
(RealT 1 - RealT e))%HP,
(snd (bound_term t1) * snd (bound_term t2) *
(RealT 1 + RealT e))%HP)
end) expr2)) as ub2.
unfold snd in *.
clear Hequb1 Hequb2 bplus_correct HeqrltBoolInfo H1 H H2.
pose proof relative_error as Rel_Err.
remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp.
specialize (Rel_Err radix2 round_fexp).
pose proof validFexpProof.
subst.
specialize (Rel_Err validFexpProof custom_emin custom_prec precThm (round_mode mode_NE) (valid_rnd_N choiceDef)).
remember (B754_finite custom_prec custom_emax b m e0 e1) as f.
remember (B754_finite custom_prec custom_emax b0 m0 e2 e3) as f0.
specialize (Rel_Err ((B2R custom_prec custom_emax f +
B2R custom_prec custom_emax f0))).
destruct (Rle_dec (bpow radix2 custom_emin) (Rabs (B2R custom_prec custom_emax f + B2R custom_prec custom_emax f0))) as [noUnderflow|underflow].
apply Rel_Err in noUnderflow.
unfold custom_prec, custom_emax in *.
Lemma three2 : forall x1 x2 x3, x1 <=x2 <= x3 -> x2 <= x3.
intros.
intuition.
Qed.
pose proof three2 as three2.
apply three2 in IHexpr2.
apply three2 in IHexpr1.
destruct (Rge_dec (B2R 53 1024 f + B2R 53 1024 f0) R0) as [suml|sumg]. {+
destruct (Rge_dec (round radix2 (FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (B2R 53 1024 f + B2R 53 1024 f0) -(B2R 53 1024 f + B2R 53 1024 f0)) R0) as [roundg | roundl].
-
unfold Rabs in *.
destruct Rcase_abs in noUnderflow.
* psatz R.
* destruct Rcase_abs in noUnderflow.
{+ psatz R.
}
{
+
unfold eval_term in *.
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
match t with
| VarNowT x => s1 x
| (x) !%HP => s2 x
| NatT n => INR n
| RealT r1 => r1
| (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
| (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
| (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
end) ub1 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as eub1.
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
match t with
| VarNowT x => s1 x
| (x) !%HP => s2 x
| NatT n => INR n
| RealT r1 => r1
| (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
| (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
| (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
end) ub2 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as eub2.
revert IHexpr1. intros IHexpr1.
revert IHexpr2. intros IHexpr2.
unfold e.
remember (round radix2 (FLT_exp (3 - 1024 - 53) 53)
(round_mode mode_NE) (B2R 53 1024 f + B2R 53 1024 f0)) as roundedValue.
remember (B2R 53 1024 f) as f1.
remember (B2R 53 1024 f0) as f2.
clear Heqeub1 r0 three2 Rel_Err Heqeub2 H expr1 expr2 ub1 Heqf2 Heqf0 e3 Heqf Heqf1 HeqroundedValue tr m e0 e1 f f0 m0 e2 ub2 .
simpl in *.
clear r.
psatz R.
}
- unfold eval_term in *. remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} :
R :=
match t with
| VarNowT x => s1 x
| (x) !%HP => s2 x
| NatT n => INR n
| RealT r => r
| (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
| (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
| (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
end) ub2 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as eub2.
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} :
R :=
match t with
| VarNowT x => s1 x
| (x) !%HP => s2 x
| NatT n => INR n
| RealT r => r
| (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
| (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
| (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
end) ub1 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as eub1.
unfold Rabs in noUnderflow.
destruct Rcase_abs in noUnderflow.
* destruct Rcase_abs in noUnderflow.
admit. (*the case when the sum is negative*)
revert IHexpr1 IHexpr2.
intros IHexpr1 IHexpr2.
clear expr1 expr2 m e0 e1 ub1 Heqf Heqeub1 Heqf0 Heqeub2 e2 e3 H Rel_Err roundl ub2 tr m0 three2.
unfold e in *. simpl in *. psatz R.
* destruct Rcase_abs in noUnderflow.
admit. (*the case when the sum is negative*)
unfold e in *.
remember (round radix2 (FLT_exp (3 - 1024 - 53) 53)
(round_mode mode_NE) (B2R 53 1024 f + B2R 53 1024 f0)) as roundedValue.
clear expr1 expr2 m e0 e1 ub1 Heqf Heqeub1 Heqf0 Heqeub2 e2 e3 H Rel_Err roundl ub2 tr m0 three2.
simpl in *.
psatz R.
}
admit. (*the case when the sum is negative*)
admit. (*the case when there is underflow*)
admit. (*the case when there is overflow*)
+   unfold custom_eval_expr in *.
remember  ((fix custom_eval_expr (t : NowTerm) :
            binary_float custom_prec custom_emax :=
            match t with
            | VarNowN _ => custom_float_zero
            | NatN n => nat_to_float n
            | FloatN f => f
            | (t1 + t2)%SL =>
                Bplus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (t1 - t2)%SL =>
                Bminus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (t1 * t2)%SL =>
                Bmult custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            end) expr1) as eval_expr.


remember   ((fix custom_eval_expr (t : NowTerm) :
            binary_float custom_prec custom_emax :=
            match t with
            | VarNowN _ => custom_float_zero
            | NatN n => nat_to_float n
            | FloatN f => f
            | (t1 + t2)%SL =>
                Bplus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (t1 - t2)%SL =>
                Bminus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (t1 * t2)%SL =>
                Bmult custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            end) expr2) as eval_expr2.

clear Heqeval_expr2 Heqeval_expr.
pose proof Bminus_correct as bminus_correct.
specialize (bminus_correct custom_prec custom_emax eq_refl eq_refl Floats.Float.binop_pl mode_NE eval_expr eval_expr2).
destruct eval_expr eqn:eval_expr_des.
* admit. (*zero case*)
* admit. (*infinty case*)
* admit. (*nan case*)
*
destruct eval_expr2 eqn:eval_expr2_des.
- admit. (*zero case*)
- admit. (*infinty case*)
- admit. (*nan case*)
- unfold is_finite in bminus_correct.
specialize (bminus_correct truth truth).
remember (Rlt_bool
                        (Rabs
                           (round radix2
                              (FLT_exp (3 - custom_emax - custom_prec)
                                 custom_prec) (round_mode mode_NE)
                              (B2R custom_prec custom_emax
                                 (B754_finite custom_prec custom_emax b m e0
                                    e1) -
                               B2R custom_prec custom_emax
                                 (B754_finite custom_prec custom_emax b0 m0
                                    e2 e3)))) (bpow radix2 custom_emax))   as rltBoolInfo. destruct rltBoolInfo.
subst.  decompose [and] bminus_correct. rewrite H.
split.
{ - unfold bound_term in *.
Local Open Scope HP_scope.
remember (fst
             ((fix bound_term (x : NowTerm) : Term * Term :=
                 match x with
                 | VarNowN _ => (RealT 0, RealT 0)
                 | NatN n => (RealT (INR n), RealT (INR n))
                 | FloatN f => (RealT (B2R 53 1024 f), RealT (B2R 53 1024 f))
                 | (t1 + t2)%SL =>
                     ((fst (bound_term t1) + fst (bound_term t2)) *
                      (RealT 1 - RealT e),
                     (snd (bound_term t1) + snd (bound_term t2)) *
                     (RealT 1 + RealT e))
                 | (t1 - t2)%SL =>
                     ((fst (bound_term t1) - snd (bound_term t2)) *
                      (RealT 1 - RealT e),
                     (snd (bound_term t1) - fst (bound_term t2)) *
                     (RealT 1 + RealT e))
                 | (t1 * t2)%SL =>
                     (fst (bound_term t1) * fst (bound_term t2) *
                      (RealT 1 - RealT e),
                     snd (bound_term t1) * snd (bound_term t2) *
                     (RealT 1 + RealT e))
                 end) expr1)) as lb1 .

remember ( snd
             ((fix bound_term (x : NowTerm) : Term * Term :=
                 match x with
                 | VarNowN _ => (RealT 0, RealT 0)
                 | NatN n => (RealT (INR n), RealT (INR n))
                 | FloatN f => (RealT (B2R 53 1024 f), RealT (B2R 53 1024 f))
                 | (t1 + t2)%SL =>
                     ((fst (bound_term t1) + fst (bound_term t2)) *
                      (RealT 1 - RealT e),
                     (snd (bound_term t1) + snd (bound_term t2)) *
                     (RealT 1 + RealT e))
                 | (t1 - t2)%SL =>
                     ((fst (bound_term t1) - snd (bound_term t2)) *
                      (RealT 1 - RealT e),
                     (snd (bound_term t1) - fst (bound_term t2)) *
                     (RealT 1 + RealT e))
                 | (t1 * t2)%SL =>
                     (fst (bound_term t1) * fst (bound_term t2) *
                      (RealT 1 - RealT e),
                     snd (bound_term t1) * snd (bound_term t2) *
                     (RealT 1 + RealT e))
                 end) expr2)) as ub2.

unfold fst.

clear Heqlb1 Hequb2 bminus_correct HeqrltBoolInfo H1 H H2.
pose proof relative_error as Rel_Err.
remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp.
specialize (Rel_Err radix2 round_fexp).
pose proof validFexpProof.
subst.
specialize (Rel_Err validFexpProof custom_emin custom_prec precThm (round_mode mode_NE) (valid_rnd_N choiceDef)).
remember (B754_finite custom_prec custom_emax b m e0 e1) as f.
remember (B754_finite custom_prec custom_emax b0 m0 e2 e3) as f0.
Local Close Scope HP_scope.

specialize (Rel_Err (B2R custom_prec custom_emax f - B2R custom_prec custom_emax f0)).
destruct (Rle_dec (bpow radix2 custom_emin) (Rabs (B2R custom_prec custom_emax f - B2R custom_prec custom_emax f0))) as [noUnderflow|underflow].

apply Rel_Err in noUnderflow.

unfold custom_prec, custom_emax in *.
pose proof three as three.
pose proof three2 as three2.
apply three2 in IHexpr2.
apply three in IHexpr1.

destruct (Rge_dec (B2R 53 1024 f - B2R 53 1024 f0) R0) as [suml|sumg]. {+
destruct (Rge_dec (round radix2 (FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (B2R 53 1024 f - B2R 53 1024 f0) -(B2R 53 1024 f - B2R 53 1024 f0)) R0) as [roundg | roundl].
-
unfold Rabs in *.
destruct Rcase_abs in noUnderflow.
* psatz R.
* destruct Rcase_abs in noUnderflow.
{+ psatz R.
}
{
+
unfold eval_term in *.
remember  ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r1 => r1
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) lb1 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb1.

remember  ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r1 => r1
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) ub2 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as eub2.
revert IHexpr1. intros IHexpr1.
revert IHexpr2. intros IHexpr2.
unfold e.
remember (round radix2 (FLT_exp (3 - 1024 - 53) 53)
(round_mode mode_NE) (B2R 53 1024 f - B2R 53 1024 f0)) as roundedValue.
remember (B2R 53 1024 f) as f1.
remember (B2R 53 1024 f0) as f2.
clear Heqeub2 r0 three2 Rel_Err Heqelb1 H expr1 expr2 ub2 Heqf2 Heqf0 e3 Heqf Heqf1 HeqroundedValue tr m e0 e1 f f0 m0 e2 lb1 .
simpl in *.
clear r noUnderflow.
psatz R.
}
- unfold eval_term in *.   
remember  ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r => r
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) lb1 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb1.

remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r => r
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) ub2 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as eub2.
unfold Rabs in noUnderflow. 
destruct Rcase_abs in noUnderflow.
* destruct Rcase_abs in noUnderflow.
admit. (*the case when the sum is negative*)
revert IHexpr1 IHexpr2.
intros IHexpr1 IHexpr2.
clear expr1 expr2 m e0 e1 lb1 Heqf Heqeub2 Heqf0 Heqelb1 e2 e3 H Rel_Err roundl ub2 tr m0 three2.

unfold e in *. clear r.  clear r0. simpl in *.
psatz R.

* destruct Rcase_abs in noUnderflow.
admit. (*the case when the sum is negative*)
unfold e in *.
remember (round radix2 (FLT_exp (3 - 1024 - 53) 53)
(round_mode mode_NE) (B2R 53 1024 f - B2R 53 1024 f0)) as roundedValue.
clear expr1 expr2 m e0 e1 ub2 Heqf Heqeub2 Heqf0 Heqelb1 e2 e3 H Rel_Err roundl lb1 tr m0 three2.
simpl in *.
psatz R. 
}
admit. (*the case when the sum is negative*)
admit. (*the case when there is underflow*)
}


unfold bound_term in *.
Local Open Scope HP_scope.
remember  ((snd
            ((fix bound_term (x : NowTerm) : Term * Term :=
                match x with
                | VarNowN _ => (RealT 0, RealT 0)
                | NatN n => (RealT (INR n), RealT (INR n))
                | FloatN f => (RealT (B2R 53 1024 f), RealT (B2R 53 1024 f))
                | (t1 + t2)%SL =>
                    ((fst (bound_term t1) + fst (bound_term t2)) *
                     (RealT 1 - RealT e),
                    (snd (bound_term t1) + snd (bound_term t2)) *
                    (RealT 1 + RealT e))
                | (t1 - t2)%SL =>
                    ((fst (bound_term t1) - snd (bound_term t2)) *
                     (RealT 1 - RealT e),
                    (snd (bound_term t1) - fst (bound_term t2)) *
                    (RealT 1 + RealT e))
                | (t1 * t2)%SL =>
                    (fst (bound_term t1) * fst (bound_term t2) *
                     (RealT 1 - RealT e),
                    snd (bound_term t1) * snd (bound_term t2) *
                    (RealT 1 + RealT e))
                end) expr1))) as ub1. 

remember ((fst
             ((fix bound_term (x : NowTerm) : Term * Term :=
                 match x with
                 | VarNowN _ => (RealT 0, RealT 0)
                 | NatN n => (RealT (INR n), RealT (INR n))
                 | FloatN f => (RealT (B2R 53 1024 f), RealT (B2R 53 1024 f))
                 | (t1 + t2)%SL =>
                     ((fst (bound_term t1) + fst (bound_term t2)) *
                      (RealT 1 - RealT e),
                     (snd (bound_term t1) + snd (bound_term t2)) *
                     (RealT 1 + RealT e))
                 | (t1 - t2)%SL =>
                     ((fst (bound_term t1) - snd (bound_term t2)) *
                      (RealT 1 - RealT e),
                     (snd (bound_term t1) - fst (bound_term t2)) *
                     (RealT 1 + RealT e))
                 | (t1 * t2)%SL =>
                     (fst (bound_term t1) * fst (bound_term t2) *
                      (RealT 1 - RealT e),
                     snd (bound_term t1) * snd (bound_term t2) *
                     (RealT 1 + RealT e))
                 end) expr2))) as lb2.

unfold snd in *.
Local Close Scope HP_scope.
unfold eval_term in *.



clear Hequb1 Heqlb2 bminus_correct HeqrltBoolInfo H1 H H2.
pose proof relative_error as Rel_Err.
remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp.
specialize (Rel_Err radix2 round_fexp).
pose proof validFexpProof.
subst.

unfold eval_term in *.

remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r => r
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) ub1 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as eub1.

remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r => r
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) lb2 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb2.
specialize (Rel_Err validFexpProof (custom_emin)%Z custom_prec precThm (round_mode mode_NE) (valid_rnd_N choiceDef)).
remember (B754_finite custom_prec custom_emax b m e0 e1) as f.
remember (B754_finite custom_prec custom_emax b0 m0 e2 e3) as f0.
Local Close Scope HP_scope.
specialize (Rel_Err ((B2R custom_prec custom_emax f -
B2R custom_prec custom_emax f0))).
destruct (Rle_dec (bpow radix2 custom_emin) (Rabs (B2R custom_prec custom_emax f - B2R custom_prec custom_emax f0))) as [noUnderflow|underflow].
apply Rel_Err in noUnderflow.
unfold custom_prec, custom_emax in *.
pose proof three2 as three2.
pose proof three as three.
apply three in IHexpr2.
apply three2 in IHexpr1.

destruct (Rge_dec (B2R 53 1024 f - B2R 53 1024 f0) R0) as [suml|sumg]. {+
destruct (Rge_dec (round radix2 (FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (B2R 53 1024 f - B2R 53 1024 f0) -(B2R 53 1024 f - B2R 53 1024 f0)) R0) as [roundg | roundl].
-
unfold Rabs in *.
destruct Rcase_abs in noUnderflow.
* psatz R.
* destruct Rcase_abs in noUnderflow.
{+ psatz R.
}
revert IHexpr1. intros IHexpr1.
revert IHexpr2. intros IHexpr2.
unfold e.
remember (round radix2 (FLT_exp (3 - 1024 - 53) 53)
(round_mode mode_NE) (B2R 53 1024 f - B2R 53 1024 f0)) as roundedValue.
remember (B2R 53 1024 f) as f1.
remember (B2R 53 1024 f0) as f2.
clear Heqeub1 r0 three r Rel_Err Heqelb2 H expr1 expr2 ub1 Heqf2 Heqf0 Heqf Heqf1 HeqroundedValue tr f f0 lb2 .
simpl in *. 
psatz R.
- unfold Rabs in noUnderflow.
destruct Rcase_abs in noUnderflow.
* destruct Rcase_abs in noUnderflow.
admit. (*the case when the sum is negative*)
revert IHexpr1 IHexpr2.
intros IHexpr1 IHexpr2.
clear expr1 expr2 m e0 e1 ub1 Heqf Heqeub1 Heqf0 Heqelb2 e2 e3 H Rel_Err roundl lb2 tr m0 three three2.
unfold e in *.
simpl in *.
psatz R.
* destruct Rcase_abs in noUnderflow.
admit. (*the case when the sum is negative*)
unfold e in *.
remember  (round radix2 (FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE)
     (B2R 53 1024 f - B2R 53 1024 f0)) as rounded_value.
psatz R.

}
admit. (*the case when the sum is negative*)
admit. (*the case when there is underflow*)
admit. (*the case when there is overflow*)

+ (*multiplication*)
  unfold custom_eval_expr in *.  
remember  ((fix custom_eval_expr (t : NowTerm) :
            binary_float custom_prec custom_emax :=
            match t with
            | VarNowN _ => custom_float_zero
            | NatN n => nat_to_float n
            | FloatN f => f
            | (t1 + t2)%SL =>
                Bplus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (t1 - t2)%SL =>
                Bminus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (t1 * t2)%SL =>
                Bmult custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            end) expr1) as eval_expr.

remember ((fix custom_eval_expr (t : NowTerm) :
            binary_float custom_prec custom_emax :=
            match t with
            | VarNowN _ => custom_float_zero
            | NatN n => nat_to_float n
            | FloatN f => f
            | (t1 + t2)%SL =>
                Bplus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (t1 - t2)%SL =>
                Bminus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (t1 * t2)%SL =>
                Bmult custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            end) expr2) as eval_expr2.
clear Heqeval_expr2 Heqeval_expr.
pose proof Bmult_correct as bmult_correct.
specialize (bmult_correct custom_prec custom_emax eq_refl eq_refl Floats.Float.binop_pl mode_NE eval_expr eval_expr2).
destruct eval_expr eqn:eval_expr_des.
* admit. (*zero case*)
* admit. (*infinty case*)
* admit. (*nan case*)
*
destruct eval_expr2 eqn:eval_expr2_des.
- admit. (*zero case*)
- admit. (*infinty case*)
- admit. (*nan case*)
- unfold is_finite in bmult_correct.

remember (Rlt_bool
                       (Rabs
                          (round radix2
                             (FLT_exp (3 - custom_emax - custom_prec)
                                custom_prec) (round_mode mode_NE)
                             (B2R custom_prec custom_emax
                                (B754_finite custom_prec custom_emax b m e0
                                   e1) *
                              B2R custom_prec custom_emax
                                (B754_finite custom_prec custom_emax b0 m0 e2
                                   e3)))) (bpow radix2 custom_emax)) as rltBoolInfo.

destruct rltBoolInfo.
subst.  decompose [and] bmult_correct. rewrite H.
split.
{ - unfold bound_term in *.

Local Open Scope HP_scope.
remember (fst
            ((fix bound_term (x : NowTerm) : Term * Term :=
                match x with
                | VarNowN _ => (RealT 0, RealT 0)
                | NatN n => (RealT (INR n), RealT (INR n))
                | FloatN f => (RealT (B2R 53 1024 f), RealT (B2R 53 1024 f))
                | (t1 + t2)%SL =>
                    ((fst (bound_term t1) + fst (bound_term t2)) *
                     (RealT 1 - RealT e),
                    (snd (bound_term t1) + snd (bound_term t2)) *
                    (RealT 1 + RealT e))
                | (t1 - t2)%SL =>
                    ((fst (bound_term t1) - snd (bound_term t2)) *
                     (RealT 1 - RealT e),
                    (snd (bound_term t1) - fst (bound_term t2)) *
                    (RealT 1 + RealT e))
                | (t1 * t2)%SL =>
                    (fst (bound_term t1) * fst (bound_term t2) *
                     (RealT 1 - RealT e),
                    snd (bound_term t1) * snd (bound_term t2) *
                    (RealT 1 + RealT e))
                end) expr1)) as lb1.

remember (fst
             ((fix bound_term (x : NowTerm) : Term * Term :=
                 match x with
                 | VarNowN _ => (RealT 0, RealT 0)
                 | NatN n => (RealT (INR n), RealT (INR n))
                 | FloatN f => (RealT (B2R 53 1024 f), RealT (B2R 53 1024 f))
                 | (t1 + t2)%SL =>
                     ((fst (bound_term t1) + fst (bound_term t2)) *
                      (RealT 1 - RealT e),
                     (snd (bound_term t1) + snd (bound_term t2)) *
                     (RealT 1 + RealT e))
                 | (t1 - t2)%SL =>
                     ((fst (bound_term t1) - snd (bound_term t2)) *
                      (RealT 1 - RealT e),
                     (snd (bound_term t1) - fst (bound_term t2)) *
                     (RealT 1 + RealT e))
                 | (t1 * t2)%SL =>
                     (fst (bound_term t1) * fst (bound_term t2) *
                      (RealT 1 - RealT e),
                     snd (bound_term t1) * snd (bound_term t2) *
                     (RealT 1 + RealT e))
                 end) expr2)) as lb2.
Local Open Scope HP_scope.
unfold fst.
clear Heqlb1 Heqlb2 bmult_correct HeqrltBoolInfo H1 H H2.
pose proof relative_error as Rel_Err.
remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp.
specialize (Rel_Err radix2 round_fexp).
pose proof validFexpProof.
subst.
specialize (Rel_Err validFexpProof custom_emin custom_prec precThm (round_mode mode_NE) (valid_rnd_N choiceDef)).
remember (B754_finite custom_prec custom_emax b m e0 e1) as f.
remember (B754_finite custom_prec custom_emax b0 m0 e2 e3) as f0.
Local Close Scope HP_scope.
specialize (Rel_Err (B2R custom_prec custom_emax f * B2R custom_prec custom_emax f0)).
destruct (Rle_dec (bpow radix2 () (Rabs (B2R custom_prec custom_emax f * B2R custom_prec custom_emax f0))) as [noUnderflow|underflow].
apply Rel_Err in noUnderflow.
unfold custom_prec, custom_emax in *.
pose proof three as three.
apply three in IHexpr2.
apply three in IHexpr1.
revert IHexpr1 IHexpr2. 
intros IHexpr1 IHexpr2.

destruct (Rge_dec (B2R 53 1024 f * B2R 53 1024 f0) R0) as [suml|sumg]. {+
destruct (Rge_dec (round radix2 (FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (B2R 53 1024 f * B2R 53 1024 f0) -(B2R 53 1024 f * B2R 53 1024 f0)) R0) as [roundg | roundl].
-
unfold Rabs in *.
destruct Rcase_abs in noUnderflow.
*psatz R.
* destruct Rcase_abs in noUnderflow.
{+ psatz R.
}
{
+
unfold eval_term in *.
remember  ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r1 => r1
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) lb1 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb1.

remember  ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r1 => r1
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) lb2 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb2.


revert IHexpr1. intros IHexpr1.
revert IHexpr2. intros IHexpr2.
unfold e.
remember (round radix2 (FLT_exp (3 - 1024 - 53) 53)
(round_mode mode_NE) (B2R 53 1024 f * B2R 53 1024 f0)) as roundedValue.
remember (B2R 53 1024 f) as f1.
remember (B2R 53 1024 f0) as f2.
clear Heqelb2 r0 three Rel_Err Heqelb1 H expr1 expr2 lb2 Heqf2 Heqf0 e3 Heqf Heqf1 HeqroundedValue tr m e0 e1 f f0 m0 e2 lb1 .
simpl in *.
clear r noUnderflow.

Require Import TLA.Tactics.
unfold Rdiv in *.

z3_solve.
z3Tactic.
z3_solve.
revert suml roundg IHexpr1 IHexpr2.
z3
clear r noUnderflow.

psatz R.

admit.
     (B2R 53 1024 f - B2R 53 1024 f0) 
simpl in *.
clear Rel_Err.

psatz R.

 revert IHexpr2 IHexpr1. intros  IHexpr1 IHexpr2.
clear r Rel_Err Heqf0 Heqf e3 e2 e1 e0 three2 three.
unfold e in *. simpl.
remember  (round radix2 (FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE)
     (B2R 53 1024 f - B2R 53 1024 f0)) as roundedValue.



psatz R.


admit. (*the case when there is overflow*)

unfold e in *. simpl in *. psatz R.


remember (round radix2 (FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (B2R 53 1024 f + B2R 53 1024 f0)) as roundedValue.
remember ((B2R 53 1024 f + B2R 53 1024 f0)) as trueValue.
remember (bpow radix2 (- (53) + as 1)) as error.
apply three in IHexpr2.
unfold round. unfold scaled_mantissa.
unfold canonic_exp. unfold F2R. unfold Z2R.
simpl.
vm_compute.
apply three in IHexpr2.
eapply bplus_correct in HeqrltBoolInfo.
Print binary_float.
simpl in bplus_correct.
remember (Rlt_bool (Rabs (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (B2R custom_prec custom_emax fx1 + B2R custom_prec custom_emax fx2))) (bpow radix2 custom_emax)) as rltBoolInfo.
unfold round in bplus_correct.
specialize (bplus_correct X).
specialize (bplus_correct (is_finite custom_prec custom_emax eval_expr)).
* admit. (*VarNowN*)
* admit. (*NatN later*)
* intros val HClight.
compute in HClight.
inversion HClight.
intuition.
admit. (*inversion of HClight for (clightExpr (FloatN f)) results in two goals - one containing a floating value and another containing a pointer containing a floating value*)
* intros val HClight.
unfold clightExpr, nowTerm_to_clight,evalState,runState in HClight. simpl in HClight.
inversion HClight.
clear HClight.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit. admit.
* admit.
* admit.
Qed.
(*
inversion HClight.
Print eval_expr.
unfold clightExpr, nowTerm_to_clight,evalState,runState in HClight.
inversion HClight.
Print eval_expr.
unfold clightExpr in *.
unfold nowTerm_to_clight in *.
compute in H0.
inversion H0.
* unfold bound_term.
unfold clightExpr in *.
unfold valToR.
intuition.
admit. (*inversion of HClight for (clightExpr (FloatN f)) results in two goals - one containing a floating value and another containing a pointer containing a floating value*)
inversion HClight.
Print eval_expr.
Print eval_expr.
Print Econst_int.
Print clightExpr.
simpl in *.
Print eval_expr.
unfold clightExpr in H0.
unfold nowTerm_to_clight in H0.
inversion H0.
admit.
admit.
admit.
admit.
unfold clightExpr in H0.
unfold nowTerm_to_clight in H0.
Print Econst_int.
Print Econst_int.
induction expr1.
induction expr2.
admit. (*addition of two VarNowNs*)
admit. (*addition of VarNowN and NatN*)
admit. (*addition of VarNowN and FloatN*)
admit.
admit. (**)
inversion HClight.
Admitted.
*)
Lemma bound_proof : (forall (tr:Semantics.trace) expr, (bound expr (Semantics.hd tr) (Semantics.hd (Semantics.tl tr)))).
intros.
simpl in *.
unfold bound.
simpl in *.
destruct expr eqn:val.
- intuition.
- intuition.
- intuition.
- destruct n1 eqn:expr1. (*this is for the case n1+n2*)
admit. (* admitting the case when n1 is VarNowN*)
admit. (* admitting the case when n2 is NatN*)
(*solving the case when n1 is FloatN f*)
destruct n2 eqn:expr2.
admit. (*admitting the case when n2 is VarNowN*)
admit. (*admitting the case when n2 is NatN*)
+ intros fx1 fx2 H H0 ge e0 te mem val0 H1.
Print eval_expr.
Print Values.val.
inversion H1.
Print Values.val.
unfold sem_binary_operation in H9. unfold typeof in H9.
Print Values.val.
inversion H7. inversion H8.
* subst;simpl.
unfold c_float in *.
unfold sem_add in H9.
unfold classify_add in H9.
unfold typeconv in H9.
unfold remove_attributes in H9.
unfold change_attributes in H9.
unfold sem_binarith in H9.
unfold sem_cast in H9.
unfold classify_cast in H9.
unfold binarith_type in H9.
unfold classify_binarith in H9.
Transparent Floats.Float.add.
unfold Floats.Float.add in H9.
unfold b64_plus in H9.
Print Bplus_correct.
Print is_finite.
pose (is_finite 53 1024 fx1).
unfold is_finite in b.
decompose [and] H0.
pose proof Bplus_correct.
Check Bplus.
Print Fcore_FLT.FLT_exp.
Locate emin.
Print Bplus.
Print Floats.Float.binop_pl.
Print Archi.default_pl_64.
Print nan_pl.
Print Z_of_nat'.
eapply H10 in H3.
Print B2R.
Print Bsign.
Print B2R.
instantiate (1:=fx1) in H3.
instantiate (2:=mode_NE) in H3.
instantiate (3:=eq_refl) in H3.
instantiate (4:=eq_refl) in H3.
instantiate (1:=Floats.Float.binop_pl) in H3. decompose [and] H0.
remember (Rlt_bool (Rabs (round radix2 (Fcore_FLT.FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (B2R 53 1024 fx1 + B2R 53 1024 fx2))) (bpow radix2 1024)) as rltBoolInfo. destruct rltBoolInfo.
decompose [and] H3.
revert H18. intros H18.
inversion H9. unfold valToR.
Lemma three : forall x1 x2 x3,x1 <=x2 <= x3 -> x1 <= x2 /\ x2 <= x3.
intros.
intuition.
Qed.
split.
Transparent Floats.Float.binop_pl.
Check eq_trans.
pose (Bplus 53 1024 eq_refl eq_refl Floats.Float.binop_pl mode_NE fx1 fx2) as samp.
Transparent Bplus.
Transparent B2R.
rewrite H18 at 1.
Require Import compcert.flocq.Prop.Fprop_relative.
Print relative_error.
pose proof relative_error as Rel_Err.
Print round.
Print Valid_exp.
Check Rel_Err.
Print round.
pose (FLT_exp (3 - 1024 - 53) 53) as round_fexp.
pose round_fexp as round_fexpCopy.
specialize (Rel_Err radix2 round_fexp).
Check Valid_exp.
Print Valid_exp.
Lemma validFexpProof : Valid_exp (FLT_exp (3 - 1024 - 53) 53).
unfold Valid_exp;
intros.
split.
intros.
unfold FLT_exp in *.
Search (Z-> Z ->{_}+{_}).
lia.
intros. split. unfold FLT_exp in *.
unfold FLT_exp in *.
lia.
intros. unfold FLT_exp in *.
lia.
Qed.
revert H.
intros H.
specialize (Rel_Err validFexpProof).
Print round.
Locate Valid_exp.
Print Valid_exp.
Definition precVal :=53%Z.
Print round.
Print FLT_exp.
Definition eminVal:= (3-1024-53)%Z.
Print binary_float.
Check binary_float.
specialize (Rel_Err eminVal precVal).
Check round_fexp.
unfold round_fexp in Rel_Err.
unfold eminVal in Rel_Err.
unfold precVal in Rel_Err.
Lemma precThm: (forall k : Z, (eminVal < k)%Z -> (precVal <= k - FLT_exp (eminVal) precVal k)%Z).
intros.
unfold eminVal in *. unfold precVal in *. unfold FLT_exp.
unfold Z.max.
Search (Z->Z -> {_}+{_}).
pose proof Z_lt_ge_dec ((k - 53)%Z) ((3 - 1024 - 53)%Z).
pose (k - 53 ?= 3 - 1024 - 53)%Z.
Print Datatypes.Eq.
Search (_ -> Datatypes.comparison).
Print Cge.
destruct H0. simpl in *.
Search (_->Datatypes.Eq).
Search (_->Datatypes.comparison).
admit. admit
Qed.
Check precThm.
revert H24. intros H24.
specialize (Rel_Err precThm).
specialize (Rel_Err (round_mode mode_NE)).
Definition choiceDef := (fun x => negb (Zeven x)).
specialize (Rel_Err (valid_rnd_N choiceDef)).
Print Bplus_correct.
simpl in H6.
simpl in H11.
simpl in H5.
simpl in H12.
Lemma combine: forall x1 x2, x1 <= x2 -> x2 <= x1 -> x1 = x2.
intros. psatz R.
Qed.
revert H. intros H.
apply combine in H6.
rewrite H6.
rewrite H6 in H.
apply combine in H5.
rewrite H5.
rewrite H5 in H.
specialize (Rel_Err (B2R 53 1024 f + B2R 53 1024 f0)).
pose (bpow radix2 (3 - 1024 - 53) <= Rabs (B2R 53 1024 f + B2R 53 1024 f0)) as noOverflow.
Lemma noOverflowProof: forall f f0, bpow radix2 (3 - 1024 - 53) <= Rabs (B2R 53 1024 f + B2R 53 1024 f0).
intros. admit. Qed.
pose proof noOverflowProof as noOverflowProof.
specialize (noOverflowProof f f0).
specialize (Rel_Err noOverflowProof).
revert Rel_Err. intros Rel_Err.
clear H0 H1 H8 H7 H9. clear H4 H6 H11 H5 H12 H10 H2 H3 H24 H18 H24 samp H23 H16 H22. clear H20 H19 H17 H14 H15. clear H13. clear HeqrltBoolInfo. clear b. Print Rabs.
unfold e in *.
remember (round radix2 (FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (B2R 53 1024 f + B2R 53 1024 f0)) as roundedValue.
remember ((B2R 53 1024 f + B2R 53 1024 f0)) as trueValue.
remember (bpow radix2 (- (53) + 1)) as error.
destruct (Rge_dec trueValue R0).
intuition.
destruct (Rgt_dec (roundedValue - trueValue) R0).
unfold Rabs in *.
destruct Rcase_abs in Rel_Err.
psatz R.
destruct Rcase_abs in Rel_Err.
psatz R.
clear round_fexp round_fexpCopy H HeqtrueValue noOverflow noOverflow noOverflowProof HeqroundedValue Heqerror.
psatz R.
unfold Rabs in *.
destruct Rcase_abs in Rel_Err.
destruct Rcase_abs in Rel_Err.
psatz R.
psatz R.
destruct Rcase_abs in Rel_Err.
psatz R.
psatz R.
unfold Rabs in *.
destruct Rcase_abs in Rel_Err.
destruct Rcase_abs in Rel_Err.
psatz R.
psatz R.
psatz R.
intuition.
intuition.
admit.
simpl in HeqrltBoolInfo.
clear H15 H14 H17 H19 H16 H20 H3. clear H1 H2 H8 H7 H9 H1 H8 H7 H9.
clear H4 H6 H11 H5 H12 H10. clear H0. clear b.
simpl in *.
Print Rabs.
Print Rcase_abs.
Print is_finite.
simpl in Rel_Err.
simpl.
psatz R.
revert H6. revert H11.
eapply combine.
simpl in *.
Print is_finite.
Lemma ValidRnd: Valid_rnd (round_mode mode_NE).
Print Valid_rnd.
Locate Valid_rnd.
Check round_le.
Check Valid_rnd.
Print round_le.
Check (round_mode mode_NE).
Lemma Zrnd_leProof: forall x y : R, x <= y -> ((round_mode mode_NE) x <= (round_mode mode_NE) y)%Z.
intros.
unfold round_mode.
Check valid_rnd_N.
Print Znearest.
Print Build_Valid_rnd {Z}
unfold Valid_rnd in *.
apply three.
eapply three.
rewrite H18.
admit.
revert H2. intros H2.
unfold valToR.
revert H12. intros H12.
Print e.
rewrite H12.
simpl in *.
subst.
clear tr H0 H. clear H3 H9. clear H11 H4 H10 H5 H2 H8.
clear b H7 H6. admit.(*not sure why intuition is not working here*)
rewrite <-Rlt_bool (Rabs (round radix2 (Fcore_FLT.FLT_exp (-1074) 53)ZnearestE (B2R 53 1024 fx2 + B2R 53 1024 fx1))) 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 in HeqrltBoolInfo.
rewrite H in HeqrltBoolInfo.
admit.
eapply H3 in H1.
apply H1 in Bplus_correct.
Check is_finite.
pose (is_finite fx1).
apply Bplus_correct in H8.
subst;simpl.
Print eval_expr.
destruct v1 eqn:v1Des.
destruct v2 eqn:v2Des.
admit. (*admitting the case when v1 and v2 are undefined*)
admit. (*admitting the case when v1 is undefined and v2 is int*)
admit. (*admitting the case when v1 is undefined and v2 is long*)
admit. (*admitting the case when v1 is undefined and v2 is float*)
Print Values.
admit. (*admitting the case when v1 is undefined and v2 is Vsingle*)
admit (* admitting the case when v1 is undefined and v2 is pointer*).
destruct v2 eqn:v2Des.
admit (*admitting the case when v1 is int and v2 is undefined*).
admit.
admit.
admit.
admit.
admit.
destruct v2 eqn:v2Des.
admit.
admit.
admit.
admit.
admit.
admit.
destruct v2 eqn:v2Des.
admit.
admit.
admit.
(*solving the part when v1 is float and v2 is float*)
Print Values.
*
inversion H6.
{+
unfold c_float in H8.
unfold sem_add in H8.
unfold classify_add in H8.
unfold typeconv in H8.
unfold remove_attributes in H8.
unfold change_attributes in H8.
unfold sem_binarith in H8.
unfold sem_cast in H8.
unfold classify_cast in H8.
unfold binarith_type in H8.
unfold classify_binarith in H8.
Print Floats.Float.add.
Print b64_plus.
Transparent Floats.Float.add.
Locate Floats.Float.add.
unfold Floats.Float.add in *.
unfold a in H8.
+ unfold typeof in H8.
}
Print eval_expr.
inversion H6.
unfold c_float in H8.
unfold sem_add in H8.
unfold classify_add in H8.
unfold typeconv in H8.
unfold remove_attributes in H8.
unfold change_attributes in H8.
unfold sem_binarith in H8.
unfold sem_cast in H8.
unfold classify_cast in H8.
unfold binarith_type in H8.
unfold classify_binarith in H8.
Print sem_add.
Print classify_add.
Print c_float.
Print typeconv.
unfold sem_add in H8.
+ unfold typeof in H8.
Print eval_expr.
+ Print eval_expr.
Print eval_expr.
Print sem_binary_operation.
- destruct expr1.
destruct expr2.
Print eval_expr.
Print Values.val.
intros.
Check eval_Ebinop.
vm_compute in H0.
Print Ebinop.
(*need to write a function that takes the inductive definition of an expression and converts it to an computable one*)
Print eval_expr.
Print Econst_float.
Eval compute in typeof (Econst_float fx2
(Tfloat F64 {| attr_volatile := false; attr_alignas := None |})).
Check eval_Ebinop.
Check sem_binary_operation .
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
Check Floats.Float.binop_pl.
Eval typeof Econst_float
Eval compute in sem_binary_operation Oadd
Check Econst_float.
Check
Check Ebinop.
eval_Ebinop in H0.
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
Definition bound_state s1 s2 : forall ge e te mem expr val, (eval_expr ge e te mem (clightExpr expr) val) -> (eval_term (fst (bound_term expr) s1 s2) <= val <= eval_term (snd (bound_term expr) s1 s2)).
Definition bound_st forall f expr, (fst (bound_term expr))
Lemma bound_proof : forall s1 s2, s1 <= eval_term( fst )

