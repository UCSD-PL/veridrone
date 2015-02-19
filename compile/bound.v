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
 
  fold_left (fun list triple => List.rev_append list (mapBoundListWithTriple list1 triple combFunc fla simpleBoundFunc)) list2 List.nil.

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
Definition foldBoundProp     (evalExpr:option Floats.float) (s1:state) (s2:state) (tr:trace) := (fun (prop:Prop) (triple:singleBoundTerm) =>
             match evalExpr with 
                 | Some evalExpr => 
                   (prop /\ 
                    eval_formula (premise triple) tr -> 
                    eval_term (lb triple) s1 s2 <= 
                    B2R _ _ evalExpr <= 
                    eval_term (ub triple) s1 s2)%R         
                 | _ => prop
             end).
                                                                   

Definition boundDef (expr:NowTerm) (s1:state) (s2:state) (tr:trace) (fState: fstate):Prop:=
  fold_left (foldBoundProp (eval_NowTerm fState expr) s1 s2 tr) (bound_term expr) True.


Lemma bound_proof : 
  (forall (tr:Semantics.trace) (expr:NowTerm) (fState:fstate), 
      (boundDef expr (Semantics.hd tr) (Semantics.hd (Semantics.tl tr)) tr fState)).

intros tr expr fState.
unfold boundDef.
induction expr.
+ 
destruct (bound_term (VarNowN v)) eqn:bound_term_des.
 
admit.
intuition.
admit.
Qed.
