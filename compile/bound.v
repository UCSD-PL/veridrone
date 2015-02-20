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
Require Import compcert.flocq.Core.Fcore_Raux.
Require Import source.
Require Import Coq.Reals.Raxioms.


Local Open Scope HP_scope.


Require Import compcert.flocq.Core.Fcore_Raux.
Definition error := bpow radix2 (- (53) + 1).

Record singleBoundTerm : Type := mkSBT {lb : Term; 
                                 ub : Term ; 
                                 premise : Formula}. 


(*used for addition when the result is positive and multiplication when both the arguments are positive*)

Definition bd := mkSBT (RealT R0) (RealT R0) (RealT R0 > RealT R0) .

Definition simpleBound 
           (triple1 triple2:singleBoundTerm) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple1) (lb triple2)) * (RealT R1 - RealT error)) 
        ((combFunc (ub triple1) (ub triple2)) * (RealT R1 + RealT error)) 
        fla. 

(*used for subtraction when the result is positive*)
Definition simpleBound2 
           (triple1 triple2:singleBoundTerm) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple2)  (ub triple1)) * (RealT R1- RealT error)) 
        ((combFunc (ub triple2) (lb triple1)) * (RealT R1 + RealT error)) 
        fla. 

(*used for multiplication - when both the arguments is negative*)
Definition simpleBound3 
           (triple1 triple2:singleBoundTerm) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple1)  (ub triple2)) * (RealT R1 - RealT error)) 
        ((combFunc (ub triple1) (lb triple2)) * (RealT R1 + RealT error)) 
        fla.


(*used for addition - negative result*)
Definition simpleBound4 
           (triple1 triple2:singleBoundTerm) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple1)  (lb triple2)) * (RealT R1+ RealT error)) 
        ((combFunc (ub triple1) (ub triple2)) * (RealT R1 - RealT error)) 
        fla.


(*used for subtraction when the result is negative*)
Definition simpleBound5 
           (triple1 triple2:singleBoundTerm) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple2)  (ub triple1)) * (RealT R1+ RealT error)) 
        ((combFunc (ub triple2) (lb triple1)) * (RealT R1 - RealT error)) 
        fla.

(*used for multiplication - when one of the arguments is negative*)
Definition simpleBound6 
           (triple1 triple2:singleBoundTerm) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  singleBoundTerm := 
  mkSBT ((combFunc (ub triple1)  (lb triple2)) * (RealT R1+ RealT error)) 
        ((combFunc (lb triple1) (ub triple2)) * (RealT R1 - RealT error)) 
        fla.


Definition mapBoundListWithTriple 
           (list:list singleBoundTerm) 
           (triple: singleBoundTerm) 
           (combFunc:Term->Term->Term) 
           (fla:Formula) 
           (simpleBoundFunc : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm ) := 

  map (fun triple2  =>  simpleBoundFunc triple triple2 combFunc fla) list. 


Definition foldListwithList 
           (list1 list2: list singleBoundTerm) 
           (combFunc:Term->Term->Term) 
           (fla:Formula) 
           (simpleBoundFunc : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm ):=
 
  fold_left (fun list triple => list ++ (mapBoundListWithTriple list1 triple combFunc fla simpleBoundFunc)) list2 List.nil.

Definition plusBound 
           (list1 list2: list singleBoundTerm) 
           (t1 t2:NowTerm): 
  list singleBoundTerm:= 

  (foldListwithList list1 list2 PlusT (denowify t1 + denowify t2 >= RealT R0) simpleBound) ++ 
(foldListwithList list1 list2 PlusT (denowify t1 + denowify t2 < RealT R0) simpleBound4).

Definition minusBound 
           (list1 list2: list singleBoundTerm) 
           (t1 t2:NowTerm): 
  list singleBoundTerm:=
  
  (foldListwithList list1 list2 MinusT (denowify t1 - denowify t2 >= RealT R0) simpleBound2) ++ 
(foldListwithList list1 list2 MinusT (denowify t1 + denowify t2 < RealT R0) simpleBound5).

Definition multBound 
           (list1 list2: list singleBoundTerm) 
           (t1 t2:NowTerm): 
  list singleBoundTerm:=
  (foldListwithList list1 list2 MultT (denowify t1 >= RealT R0 /\ denowify t2 >= RealT R0) simpleBound) ++
(foldListwithList list1 list2 MultT (denowify t1 < RealT R0 /\ 
denowify t2 < RealT R0) simpleBound3) ++
 (foldListwithList list1 list2 MultT (denowify t1 > RealT R0 /\ denowify t2 < RealT R0) simpleBound6) ++ 
 (foldListwithList list2 list1 MultT (denowify t1 < RealT R0 /\ denowify t2 > RealT R0) simpleBound6).

Definition lift4 {T U V W X: Type} 
                 (f : T -> U -> V -> W -> X) 
                 (a : option T) 
                 (b : option U) 
                 (c : option V) 
                 (d : option W): option X :=

  match a , b , c , d with
    | Some a , Some b , Some c , Some d => Some (f a b c d)
    | _ , _ , _ , _ => None
  end.

Definition getBound (t1 t2:NowTerm) 
                     (boundFunc: list singleBoundTerm -> 
                                 list singleBoundTerm -> 
                                 NowTerm -> 
                                 NowTerm ->
                                 list singleBoundTerm) 
                     (bound_term_func : NowTerm ->
                                        list singleBoundTerm) :=  
  boundFunc (bound_term_func t1) (bound_term_func t2) t1 t2.

Fixpoint bound_term (x:NowTerm)  : (list singleBoundTerm):= 
  match x with
    | VarNowN var =>  [mkSBT (VarNowT var) (VarNowT var) TRUE]
    | NatN n =>  [mkSBT (RealT (INR n)) (RealT (INR n)) TRUE]
    | FloatN f => [mkSBT (RealT (B2R _ _ f)) (RealT (B2R _ _ f)) TRUE]
    | PlusN t1 t2 => getBound t1 t2 plusBound bound_term
    | MinusN t1 t2 => getBound t1 t2 minusBound bound_term
    | MultN t1 t2 =>  getBound t1 t2 minusBound bound_term
  end.


Local Close Scope HP_scope.

Definition floatToReal (f:Floats.float) : option R :=
  match f with 
    | B754_zero _ =>  Some (B2R _ _ f)
    | B754_infinity _ => None
    | B754_nan _ _ => None
    | _ => Some (B2R _ _ f)
    end.

Definition foldBoundProp (evalExpr:option Floats.float) (s1:state) (s2:state) (tr:trace) := 
(fun (prop:Prop) (triple:singleBoundTerm) =>
   match evalExpr with 
     | Some evalExpr =>  
       match floatToReal evalExpr with 
         | Some realEvalExpr => (prop /\ 
                      eval_formula (premise triple) tr 
                      -> eval_term (lb triple) s1 s2 <= 
                          realEvalExpr <= 
                         eval_term (ub triple) s1 s2)%R 
         | _ => prop
       end
     | None => prop
   end).
                                                                   

Definition boundDef (expr:NowTerm) (tr:trace) (fState: fstate):Prop:=
  fold_left (foldBoundProp (eval_NowTerm fState expr) (Semantics.hd tr) (Semantics.hd (Semantics.tl tr)) tr) (bound_term expr) True.



Lemma bound_proof : 
forall (tr:Semantics.trace) (expr:NowTerm) (fState:fstate),
    (forall x y, fstate_lookup fState x = Some y ->
               Some ((Semantics.hd tr) x) = floatToReal y) -> 
boundDef expr tr fState.

intros tr expr fState f2RPremise.
unfold boundDef.
induction expr.
- unfold bound_term. 
  unfold foldBoundProp.
  unfold fold_left.
  destruct (eval_NowTerm fState (VarNowN v)) eqn:eval_expr.
  + unfold floatToReal.
    destruct f eqn:f_des.
    * simpl in *.
      specialize (f2RPremise v f).
      rewrite f_des in f2RPremise.
      simpl in *.
      apply f2RPremise in eval_expr.
      inversion eval_expr.
      intuition.
    * intuition.    
    * intuition.
    * simpl in *.
      specialize (f2RPremise v f).
      rewrite f_des in f2RPremise.
      apply f2RPremise in eval_expr.
      unfold floatToReal in *.
      inversion eval_expr.
      intuition.
  +   intuition.
- admit. (*natural numbers*)
- simpl in *.
  unfold floatToReal.
  destruct f.
  + intuition.
  + intuition.
  + intuition. 
  + intuition.
-  unfold eval_NowTerm in *. (*copying should start from this line*)
  remember ((fix eval_NowTerm (t : NowTerm) : option Floats.float :=
               match t with
               | VarNowN var => fstate_lookup fState var
               | NatN n => Some (nat_to_float n)
               | FloatN f => Some f
               | (t1 + t2)%SL =>
                   lift2
                     (Bplus custom_prec custom_emax eq_refl eq_refl
                        Floats.Float.binop_pl mode_NE) 
                     (eval_NowTerm t1) (eval_NowTerm t2)
               | (t1 - t2)%SL =>
                   lift2
                     (Bminus custom_prec custom_emax eq_refl eq_refl
                        Floats.Float.binop_pl mode_NE) 
                     (eval_NowTerm t1) (eval_NowTerm t2)
               | (t1 * t2)%SL =>
                   lift2
                     (Bmult custom_prec custom_emax eq_refl eq_refl
                        Floats.Float.binop_pl mode_NE) 
                     (eval_NowTerm t1) (eval_NowTerm t2)
               end) expr1) as eval_expr1.


  remember ((fix eval_NowTerm (t : NowTerm) : option Floats.float :=
               match t with
               | VarNowN var => fstate_lookup fState var
               | NatN n => Some (nat_to_float n)
               | FloatN f => Some f
               | (t1 + t2)%SL =>
                   lift2
                     (Bplus custom_prec custom_emax eq_refl eq_refl
                        Floats.Float.binop_pl mode_NE) 
                     (eval_NowTerm t1) (eval_NowTerm t2)
               | (t1 - t2)%SL =>
                   lift2
                     (Bminus custom_prec custom_emax eq_refl eq_refl
                        Floats.Float.binop_pl mode_NE) 
                     (eval_NowTerm t1) (eval_NowTerm t2)
               | (t1 * t2)%SL =>
                   lift2
                     (Bmult custom_prec custom_emax eq_refl eq_refl
                        Floats.Float.binop_pl mode_NE) 
                     (eval_NowTerm t1) (eval_NowTerm t2)
               end) expr2) as eval_expr2.
  revert IHexpr1 IHexpr2. intros IHexpr1 IHexpr2.
  clear Heqeval_expr1.
  clear Heqeval_expr2.
  unfold bound_term in *.
  unfold getBound in *.
  remember ((fix bound_term (x : NowTerm) : list singleBoundTerm :=
            match x with
            | VarNowN var =>
                [{| lb := VarNowT var; ub := VarNowT var; premise := TRUE |}]
            | NatN n =>
                [{|
                 lb := RealT (INR n);
                 ub := RealT (INR n);
                 premise := TRUE |}]
            | FloatN f =>
                [{|
                 lb := RealT (B2R 53 1024 f);
                 ub := RealT (B2R 53 1024 f);
                 premise := TRUE |}]
            | (t1 + t2)%SL => plusBound (bound_term t1) (bound_term t2) t1 t2
            | (t1 - t2)%SL =>
                minusBound (bound_term t1) (bound_term t2) t1 t2
            | (t1 * t2)%SL =>
                minusBound (bound_term t1) (bound_term t2) t1 t2
            end) expr1) as expr1_boundList.
  remember ((fix bound_term (x : NowTerm) : list singleBoundTerm :=
            match x with
            | VarNowN var =>
                [{| lb := VarNowT var; ub := VarNowT var; premise := TRUE |}]
            | NatN n =>
                [{|
                 lb := RealT (INR n);
                 ub := RealT (INR n);
                 premise := TRUE |}]
            | FloatN f =>
                [{|
                 lb := RealT (B2R 53 1024 f);
                 ub := RealT (B2R 53 1024 f);
                 premise := TRUE |}]
            | (t1 + t2)%SL => plusBound (bound_term t1) (bound_term t2) t1 t2
            | (t1 - t2)%SL =>
                minusBound (bound_term t1) (bound_term t2) t1 t2
            | (t1 * t2)%SL =>
                minusBound (bound_term t1) (bound_term t2) t1 t2
            end) expr2) as expr2_boundList.
revert IHexpr1 IHexpr2. intros IHexpr1 IHexpr2.
clear Heqexpr1_boundList Heqexpr2_boundList.
induction expr1_boundList as [ | Iexpr1_boundList].
  + induction expr2_boundList as [| Iexpr2_boundList].
    * simpl in *.
      intuition.
    * 
      simpl in *.
      admit.
  + admit.
- admit.
- admit.
Qed.
