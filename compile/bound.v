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

Definition custom_fst (x:Term*Term*Formula) := match x with 
| (f,s,t) => f
end.

Definition custom_snd (x:Term*Term*Formula) := match x with 
| (f,s,t)=> s
end.

Definition custom_third (x:Term*Term*Formula) := match x with 
| (f,s,t) => t
end.

Local Open Scope HP_scope.


Require Import compcert.flocq.Core.Fcore_Raux.
Definition error := bpow radix2 (- (53) + 1).



(*used for addition when the result is positive and multiplication when both the arguments are positive*)
Definition simpleBound 
           (triple1 triple2:Term*Term*Formula) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  (Term*Term*Formula) := 
  ((combFunc (custom_fst triple1)  (custom_fst triple2)) * (RealT R1 - RealT error), 
   (combFunc (custom_snd triple2) (custom_snd triple2)) * (RealT R1 + RealT error), 
   fla). 

(*used for subtraction when the result is positive*)
Definition simpleBound2 
           (triple1 triple2:Term*Term*Formula) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  (Term*Term*Formula) := 
  ((combFunc (custom_fst triple2)  (custom_snd triple1)) * (RealT R1- RealT error), 
   (combFunc (custom_snd triple2) (custom_fst triple1)) * (RealT R1 + RealT error), 
   fla). 

(*used for multiplication - when both the arguments is negative*)
Definition simpleBound3 
           (triple1 triple2:Term*Term*Formula) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  (Term*Term*Formula) := 
  ((combFunc (custom_snd triple1)  (custom_snd triple2)) * (RealT R1 - RealT error), 
   (combFunc (custom_fst triple1) (custom_fst triple2)) * (RealT R1 + RealT error), 
 fla).


(*used for addition - negative result*)
Definition simpleBound4 
           (triple1 triple2:Term*Term*Formula) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  (Term*Term*Formula) := 
  ((combFunc (custom_fst triple1)  (custom_fst triple2)) * (RealT R1+ RealT error), 
   (combFunc (custom_snd triple1) (custom_snd triple2)) * (RealT R1 - RealT error), 
   fla).


(*used for subtraction when the result is negative*)
Definition simpleBound5 
           (triple1 triple2:Term*Term*Formula) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  (Term*Term*Formula) := 
  ((combFunc (custom_fst triple2)  (custom_snd triple1)) * (RealT R1+ RealT error), 
   (combFunc (custom_snd triple2) (custom_fst triple1)) * (RealT R1 - RealT error), 
   fla).

(*used for multiplication - when one of the arguments is negative*)
Definition simpleBound6 
           (triple1 triple2:Term*Term*Formula) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  (Term*Term*Formula) := 
  ((combFunc (custom_snd triple1)  (custom_fst triple2)) * (RealT R1+ RealT error), 
   (combFunc (custom_fst triple1) (custom_snd triple2)) * (RealT R1 - RealT error), 
   fla).


Definition mapBoundListWithTriple 
           (list:list (Term*Term*Formula)) 
           (triple: (Term*Term*Formula)) 
           (combFunc:Term->Term->Term) 
           (fla:Formula) 
           (simpleBoundFunc : Term*Term*Formula -> 
                              Term*Term*Formula -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              Term*Term*Formula ) := 

  map (fun triple2  =>  simpleBoundFunc triple triple2 combFunc fla) list. 


Definition foldListwithList 
           (list1 list2: list (Term*Term*Formula)) 
           (combFunc:Term->Term->Term) 
           (fla:Formula) 
           (simpleBoundFunc : Term*Term*Formula -> 
                              Term*Term*Formula -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              Term*Term*Formula ):=
 
  fold_left (fun list triple => List.rev_append list (mapBoundListWithTriple list1 triple combFunc fla simpleBoundFunc)) list2 List.nil.

Definition plusBound 
           (list1 list2: list (Term*Term*Formula)) 
           (t1 t2:NowTerm) 
           (evalt1 evalt2 : Floats.float): 
  list (Term*Term*Formula):= 

  (foldListwithList list1 list2 PlusT (B2R _ _ evalt1 + B2R _ _ evalt2 >= RealT R0) simpleBound) ++ 
(foldListwithList list1 list2 PlusT ((B2R _ _ evalt1) + (B2R _ _ evalt2) < RealT R0) simpleBound4).

Definition minusBound 
           (list1 list2: list (Term*Term*Formula)) 
           (t1 t2:NowTerm) 
           (evalt1 evalt2 : Floats.float): 
  list (Term*Term*Formula):=
  
  (foldListwithList list1 list2 MinusT ((B2R _ _ evalt1) - (B2R _ _ evalt2) >= RealT R0) simpleBound2) ++ 
(foldListwithList list1 list2 MinusT ((B2R _ _ evalt1) - (B2R _ _ evalt2) < RealT R0) simpleBound5).

Definition multBound 
           (list1 list2: list (Term*Term*Formula)) 
           (t1 t2:NowTerm) 
           (evalt1 evalt2 : Floats.float): 
  list (Term*Term*Formula):=
  (foldListwithList list1 list2 MultT (B2R _ _ evalt1 >= RealT R0 /\B2R _ _ evalt2 >= RealT R0) simpleBound) ++
(foldListwithList list1 list2 MultT (B2R _ _ evalt1 < RealT R0 /\ 
B2R _ _ evalt2 < RealT R0) simpleBound3) ++
 (foldListwithList list1 list2 MultT (B2R _ _ evalt1 > RealT R0 /\ B2R _ _ evalt2 < RealT R0) simpleBound6) ++ 
 (foldListwithList list2 list1 MultT (B2R _ _ evalt1 < RealT R0 /\ B2R _ _ evalt2 > RealT R0) simpleBound6).

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
                     (fState:fstate) 
                     (boundFunc: list (Term*Term*Formula) -> 
                                 list (Term*Term*Formula) -> 
                                 NowTerm -> 
                                 NowTerm -> Floats.float -> 
                                 Floats.float -> 
                                 list (Term*Term*Formula)) 
                     (bound_term_func : NowTerm -> 
                                        fstate -> 
                                        option (list (Term*Term*Formula))) := 
  
  lift4 (fun list1 list2 evalt1 evalt2 => 
           boundFunc list1 list2 t1 t2 evalt1 evalt2) 
        (bound_term_func t1 fState) (bound_term_func t2 fState)             (eval_NowTerm fState t1) (eval_NowTerm fState t2).

Fixpoint bound_term x fState : option (list (Term*Term*Formula)):= 
  match x with
    | VarNowN var => Some [(RealT R0,RealT R0, TRUE)]
    | NatN n => Some [(RealT (INR n),RealT (INR n) , TRUE)]
    | FloatN f => Some [( (RealT (B2R _ _ f), RealT (B2R _ _ f)), TRUE)]
    | PlusN t1 t2 => getBound t1 t2 fState plusBound bound_term
    | MinusN t1 t2 => getBound t1 t2 fState minusBound bound_term
    | MultN t1 t2 =>  getBound t1 t2 fState minusBound bound_term
  end.


Local Close Scope HP_scope.
Definition foldBoundProp     (evalExpr:option Floats.float) (s1:state) (s2:state) (tr:trace) := (fun (prop:Prop) (triple:(Term*Term*Formula)) =>
             match evalExpr with 
                 | Some evalExpr => 
                   (prop /\ 
                    eval_formula (custom_third triple) tr -> 
                    eval_term (custom_fst triple) s1 s2 <= 
                    B2R _ _ evalExpr <= 
                    eval_term (custom_snd triple) s1 s2)%R         
                 | _ => prop
             end).
                                                                   

Definition boundDef (expr:NowTerm) (s1:state) (s2:state) (tr:trace) (fState:fstate):Prop:=
  match (bound_term expr fState) with
      | Some bound => fold_left (foldBoundProp (eval_NowTerm fState expr) s1 s2 tr) bound True
      | _ => True
  end.


Lemma bound_proof : 
  (forall (tr:Semantics.trace) expr fState, 
      (boundDef expr (Semantics.hd tr) (Semantics.hd (Semantics.tl tr)) tr fState)).
admit.
Qed.
