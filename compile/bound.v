Require Import Coq.micromega.Psatz.
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
Require Import Coq.micromega.Psatz.



Local Open Scope HP_scope.


Require Import compcert.flocq.Core.Fcore_Raux.
Definition error := bpow radix2 (- (53) + 1).
Print Formula.

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

Definition floatMax:= bpow radix2 custom_emax.
Definition floatMin := bpow radix2 (-1021)%Z.


Definition plusMinusfoldBoundListWithTriple 
           (list:list singleBoundTerm) 
           (triple: singleBoundTerm) 
           (combFunc:Term->Term->Term) 
           (simpleBoundFunc1 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm) 
           (simpleBoundFunc2 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm) 
  := 

  fold_right (fun triple2 curList => ((simpleBoundFunc1 triple triple2 combFunc 
                                                      (premise triple /\ 
                                                       premise triple2 /\ 
                                                       ((floatMin <= lb triple + lb triple2) \/ (floatMin <= ((0 - lb triple) + (0 - lb triple2))) \/ ((lb triple + lb triple =0) /\ (ub triple + ub triple =0))) /\ 
                                                       (ub triple + ub triple2 < floatMax) /\
                                                             ((0- ub triple) + (0 - ub triple2) < floatMax) /\ 
                                                       (lb triple + lb triple2 >= R0)))
                                       :: ((simpleBoundFunc2 triple triple2 combFunc 
                                                            (premise triple /\ 
                                                             premise triple2 /\ 
                                                            ((floatMin <= lb triple + lb triple2) \/ (floatMin <= ((0 - lb triple) + (0 - lb triple2))) \/ ((lb triple + lb triple =0) /\ (ub triple + ub triple =0))) /\ 
                                                             (ub triple + ub triple2 < floatMax) /\
                                                             ((0 - ub triple) + (0 - ub triple2) < floatMax) /\ 
                                                             (ub triple + ub triple2 < R0))) ::
                                             curList))) List.nil list. 

Definition multfoldBoundListWithTriple 
           (list:list singleBoundTerm) 
           (triple: singleBoundTerm) 
           (combFunc:Term->Term->Term) 
           (simpleBoundFunc1 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm) 
           (simpleBoundFunc2 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm) 
           (simpleBoundFunc3 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm) 
           (simpleBoundFunc4 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm) 
  := 

  fold_right (fun triple2 curList => (simpleBoundFunc1 triple triple2 combFunc 
                                                      (premise triple /\ 
                                                       premise triple2 /\ 
                                                       ((floatMin <= lb triple + lb triple2) \/ (floatMin <= ((0 - lb triple) + (0 - lb triple2))) \/ ((lb triple + lb triple =0) /\ (ub triple + ub triple =0)))/\
                                                       (ub triple + ub triple2 < floatMax) /\  
                                                         ((0 - ub triple) + (0 - ub triple2) < floatMax) /\
                                                       (lb triple >= R0) /\ (lb triple2 >= R0)))
                                       :: ((simpleBoundFunc2 triple triple2 combFunc 
                                                            (premise triple /\ 
                                                             premise triple2 /\ 
                                                             ((floatMin <= lb triple + lb triple2) \/ (floatMin <= ((0 - lb triple) + (0 - lb triple2))) \/ ((lb triple + lb triple =0) /\ (ub triple + ub triple =0))) /\ 
                                                             
                                                             (ub triple + ub triple2 < floatMax) /\
                                                             ((0 - ub triple) + (0 - ub triple2) < floatMax) /\
                                                             (ub triple < R0) /\ (ub triple2 < R0)))
                                             :: ((simpleBoundFunc3 triple triple2 combFunc 
                                                            (premise triple /\ 
                                                             premise triple2 /\ 
                                                             ((floatMin <= lb triple + lb triple2) \/ (floatMin <= ((0 - lb triple) + (0 - lb triple2))) \/ ((lb triple + lb triple =0) /\ (ub triple + ub triple =0))) /\ 
                                                             (ub triple + ub triple2 < floatMax) /\
                                                             ((0 - ub triple) + (0 - ub triple2) < floatMax) /\
                                                             (lb triple >= R0) /\ (ub triple2 < R0)))
                                                   :: ((simpleBoundFunc4 triple triple2 combFunc 
                                                            (premise triple /\ 
                                                             premise triple2 /\ 
                                                             ((floatMin <= lb triple + lb triple2) \/ (floatMin <= ((0 - lb triple) + (0 - lb triple2))) \/ ((lb triple + lb triple =0) /\ (ub triple + ub triple =0))) /\ 
                                                             ((ub triple + ub triple2 < floatMax) /\
                                                             ((0 - ub triple) + (0 - ub triple2) < floatMax)) /\ 
                                                             (ub triple < R0) /\ (lb triple2 >= R0)))
                                                   ::   
                                                   curList)))) List.nil list. 


Definition plusMinusfoldListwithList 
           (list1 list2: list singleBoundTerm) 
           (combFunc:Term->Term->Term) 
           (simpleBoundFunc1 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm )
           (simpleBoundFunc2 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm )
           
  : list singleBoundTerm :=
 
  fold_right (fun triple list => list ++ (plusMinusfoldBoundListWithTriple list1 triple combFunc simpleBoundFunc1 simpleBoundFunc2)) List.nil list2.

Definition multfoldListwithList 
           (list1 list2: list singleBoundTerm) 
           (combFunc:Term->Term->Term) 
           (simpleBoundFunc1 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm )
           (simpleBoundFunc2 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm )
           (simpleBoundFunc3 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm )
           (simpleBoundFunc4 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm )
           
  : list singleBoundTerm :=
 
  fold_right (fun triple list => list ++ (multfoldBoundListWithTriple list1 triple combFunc simpleBoundFunc1 simpleBoundFunc2 simpleBoundFunc3 simpleBoundFunc4)) List.nil list2.



Definition plusBound 
           (list1 list2: list singleBoundTerm) 
           (t1 t2:NowTerm): 
  list singleBoundTerm:= 
  (plusMinusfoldListwithList list1 list2 PlusT simpleBound simpleBound4).

Definition minusBound 
           (list1 list2: list singleBoundTerm) 
           (t1 t2:NowTerm): 
  list singleBoundTerm:=
  (plusMinusfoldListwithList list1 list2 MinusT simpleBound2 simpleBound5).

Definition multBound 
           (list1 list2: list singleBoundTerm) 
           (t1 t2:NowTerm): 
  list singleBoundTerm:=
  multfoldListwithList list1 list2 MultT simpleBound simpleBound3 simpleBound6 simpleBound6.
  

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



Definition floatToReal (f:Floats.float) : option R :=
  match f with 
    | B754_zero _ =>  Some (B2R _ _ f)
    | B754_infinity _ => None
    | B754_nan _ _ => None
    | _ => Some (B2R _ _ f)
    end.

Local Close Scope HP_scope.
Definition foldBoundProp (evalExpr:option Floats.float) (s1:state) (s2:state) (tr:trace) := 
(fun (triple:singleBoundTerm) (prop:Prop) =>
   match evalExpr with 
     | Some evalExpr =>  
       match floatToReal evalExpr with 
         | Some realEvalExpr => (prop /\ 
                      (eval_formula (premise triple) tr 
                      -> eval_term (lb triple) s1 s2 <= 
                          realEvalExpr <= 
                         eval_term (ub triple) s1 s2)%R) 
         | _ => prop
       end
     | None => prop
   end).
                                                                   

Lemma fold_right_truth: forall lst, fold_right (fun (_ : singleBoundTerm) (prop : Prop) => prop) True lst = True. 
intros.
induction lst.  
* simpl.
  reflexivity.
* simpl.
  apply IHlst.
Qed.

Definition boundDef (expr:NowTerm) (tr:trace) (fState: fstate):Prop:=
  fold_right (foldBoundProp (eval_NowTerm fState expr) (Semantics.hd tr) (Semantics.hd (Semantics.tl tr)) tr) True (bound_term expr).


Lemma emptyListappend : forall (A:Type) (lst:list A), lst ++ (List.nil) = lst. 
intros.
simpl in *.
induction lst.
simpl.
reflexivity.
simpl.
rewrite IHlst.
reflexivity.
Qed.


Theorem fold_right_acc_empty :forall boundlist, (fold_right (fun (_ : singleBoundTerm) (list : list singleBoundTerm) => list ++ List.nil) List.nil boundlist) = List.nil.
intros.
simpl in *.
induction boundlist.      
simpl.
reflexivity.
simpl.
pose proof emptyListappend as emptyListappend.
rewrite emptyListappend.
intuition.
Qed.


Theorem list_proof: forall (A:Type) (x:A) (xs:list A), x::xs = [x] ++ xs.
intros.
simpl.
intuition.
Qed.

Lemma and_proof : forall x1 x2, x1 /\ x2 -> x1.
intros.
intuition.
Qed.

Lemma fold_right_inferring_sublist_truth_from_list_truth : forall x xs tr expr, fold_right (foldBoundProp expr (hd tr) (hd (tl tr)) tr) 
                                                  True (x :: xs) ->
                                       fold_right (foldBoundProp expr (hd tr) (hd (tl tr)) tr)
                                                  True xs.
intros.
simpl in *.
unfold foldBoundProp in *.
destruct expr eqn:expr_des.
- unfold floatToReal in *.
  destruct f eqn:f_des.
  * apply and_proof in H.
    apply H.
  * apply H.
  * apply H.
  * apply and_proof in H.
    apply H.
-   apply H.
Qed.

Lemma firstappend : forall (A:Type) (a:A) lst1 lst2, (a::lst1) ++ lst2 = (a :: (lst1 ++ lst2)).
                      intros.
                      simpl.
                      reflexivity.
                      Qed.

Lemma fold_right_subList_inferring: forall a x lst tr, fold_right (fun (triple : singleBoundTerm) (prop : Prop) =>
         prop /\
         (eval_formula (premise triple) tr ->
          (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
           eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True (a::lst) -> fold_right (fun (triple : singleBoundTerm) (prop : Prop) =>
         prop /\
         (eval_formula (premise triple) tr ->
          (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
           eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True lst   /\  (eval_formula (premise a) tr ->
       (eval_term (lb a) (hd tr) (hd (tl tr)) <= x <=
        eval_term (ub a) (hd tr) (hd (tl tr)))%R).
intros.
simpl in *.
intuition.
Qed.
        
  

Lemma fold_right_combine : forall tr lst a x,   fold_right
         (fun (triple : singleBoundTerm) (prop : Prop) =>
          prop /\
          (eval_formula (premise triple) tr ->
           (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
            eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True lst /\ 
             (eval_formula (premise a) tr ->
       (eval_term (lb a) (hd tr) (hd (tl tr)) <= x <=
        eval_term (ub a) (hd tr) (hd (tl tr)))%R) ->   fold_right (fun (triple : singleBoundTerm) (prop : Prop) =>
          prop /\
          (eval_formula (premise triple) tr ->
           (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
            eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True (a::lst).

intros.
simpl in *.
intuition.
Qed.

Lemma fold_right_combine_opp :   forall tr lst a x,  fold_right (fun (triple : singleBoundTerm) (prop : Prop) =>
          prop /\
          (eval_formula (premise triple) tr ->
           (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
            eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True (a::lst) -> fold_right
         (fun (triple : singleBoundTerm) (prop : Prop) =>
          prop /\
          (eval_formula (premise triple) tr ->
           (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
            eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True lst /\ 
             (eval_formula (premise a) tr ->
       (eval_term (lb a) (hd tr) (hd (tl tr)) <= x <=
        eval_term (ub a) (hd tr) (hd (tl tr)))%R).
intros.
simpl in *.
intuition.
Qed.


Lemma fold_right_inferr_sublist : forall lst1 lst2 tr x, fold_right
        (fun (triple : singleBoundTerm) (prop : Prop) =>
         prop /\
         (eval_formula (premise triple) tr ->
          (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
           eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True
        (lst1 ++ lst2) -> fold_right
     (fun (triple : singleBoundTerm) (prop : Prop) =>
      prop /\
      (eval_formula (premise triple) tr ->
       (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
        eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True lst2 /\ fold_right
     (fun (triple : singleBoundTerm) (prop : Prop) =>
      prop /\
      (eval_formula (premise triple) tr ->
       (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
        eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True lst1.
  intros.
split.
induction lst1.
simpl in *.
intuition.
rewrite firstappend in H.
apply fold_right_subList_inferring in H.
decompose [and] H.
apply IHlst1 in H0.
intuition.
induction lst1.
simpl.
intuition.
rewrite firstappend in H.
apply fold_right_subList_inferring in H.
apply fold_right_combine.
decompose [and] H.
intuition.
Qed.



 


Lemma fold_right_two_list :forall lst1 lst2 x tr, 
                      fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop /\
                (eval_formula (premise triple) tr ->
                 (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
                  eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True
               (lst1 ++ lst2) ->   (fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop /\
                (eval_formula (premise triple) tr ->
                 (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
                  eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True
               lst1) /\ (fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop /\
                (eval_formula (premise triple) tr ->
                 (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
                  eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True
               lst2) .
                    intros.
                    split.
                    simpl in *.
                    induction lst1.
                    simpl in *.
                    intuition.
                    remember ((a :: lst1) ++ lst2) as lst.
                    pose proof firstappend as firstappend.
                    rewrite firstappend in Heqlst.
                    rewrite Heqlst in H.
                    apply fold_right_subList_inferring in H.
                    decompose [and] H.
                    apply IHlst1 in H0.
                    simpl.
                    intuition.
                    apply fold_right_inferr_sublist in H.
                    intuition.
                    Qed.


  Lemma list3Commutative: forall (a:singleBoundTerm) lst1 lst2, ((a :: lst1) ++ lst2) = a :: (lst1 ++ lst2).
    intros.
    simpl.
    reflexivity.
    Qed.

Lemma fold_right_two_list_opp :forall lst1 lst2 x tr, 
                       (fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop /\
                (eval_formula (premise triple) tr ->
                 (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
                  eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True
               lst1) /\ (fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop /\
                (eval_formula (premise triple) tr ->
                 (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
                  eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True
               lst2) -> fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop /\
                (eval_formula (premise triple) tr ->
                 (eval_term (lb triple) (hd tr) (hd (tl tr)) <= x <=
                  eval_term (ub triple) (hd tr) (hd (tl tr)))%R)) True
               (lst1 ++ lst2).
  intros.
  decompose [and] H.
  induction lst1.
  simpl in *.
  intuition.
  rewrite  list3Commutative.
  apply fold_right_combine.
  apply fold_right_subList_inferring in H0.
  decompose [and] H0.
  apply IHlst1 in H2.
  split.
  apply H2.
  apply H3.
  split.
  intuition.
  intuition.
  Qed.
  
 Local Open Scope HP_scope.

Lemma deNowifyPlus : forall t1 t2, denowify t1 + denowify t2 = denowify (PlusN t1 t2).
intros.
induction t1;
induction t2;
repeat simpl; reflexivity.
Qed.

Local Close Scope HP_scope.


Lemma resultImplicationOnArguments: forall fState expr1 expr2 f, eval_NowTerm fState (expr1 + expr2)%SL = Some f -> exists f1 f2, (eval_NowTerm fState expr1 = Some f1 ) /\ (eval_NowTerm fState expr2 = Some f2). 
         intros.
         unfold eval_NowTerm in *.
         remember ((fix eval_NowTerm (t : NowTerm) : option Floats.float :=
            match t with
            | VarNowN var => fstate_lookup fState var
            | NatN n => Some (nat_to_float n)
            | FloatN f0 => Some f0
            | (t1 + t2)%SL =>
                lift2
                  (Bplus custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax))
                     Floats.Float.binop_pl mode_NE) 
                  (eval_NowTerm t1) (eval_NowTerm t2)
            | (t1 - t2)%SL =>
                lift2
                  (Bminus custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) 
                     Floats.Float.binop_pl mode_NE) 
                  (eval_NowTerm t1) (eval_NowTerm t2)
            | (t1 * t2)%SL =>
                lift2
                  (Bmult custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) 
                     Floats.Float.binop_pl mode_NE) 
                  (eval_NowTerm t1) (eval_NowTerm t2)
            end) expr1) as eval_expr1.
         remember ((fix eval_NowTerm (t : NowTerm) : option Floats.float :=
      match t with
      | VarNowN var => fstate_lookup fState var
      | NatN n => Some (nat_to_float n)
      | FloatN f0 => Some f0
      | (t1 + t2)%SL =>
          lift2
            (Bplus custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) 
               Floats.Float.binop_pl mode_NE) (eval_NowTerm t1)
            (eval_NowTerm t2)
      | (t1 - t2)%SL =>
          lift2
            (Bminus custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) 
               Floats.Float.binop_pl mode_NE) (eval_NowTerm t1)
            (eval_NowTerm t2)
      | (t1 * t2)%SL =>
          lift2
            (Bmult custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) 
               Floats.Float.binop_pl mode_NE) (eval_NowTerm t1)
            (eval_NowTerm t2)
      end) expr2) as eval_expr2.
       unfold lift2 in H.
       destruct eval_expr1 eqn:eval_expr1_des.
         - destruct eval_expr2 eqn:eval_expr2_des.
           + exists f0. exists f1.
             intuition.
           +  exists f0.
              exists f.
              intuition.
         -   destruct eval_expr2 eqn:eval_expr2_des.
             + exists f. exists f0.
               intuition.
             + exists f. exists f.            
               intuition.
       Qed.

Lemma simpleTruth : true = true.
intuition.
Qed.             Lemma truth : true = true.
intuition.
Qed.

Local Open Scope HP_scope.
 Lemma tlaToRealRelation:
   forall (tlaExpr:NowTerm) fState (tr:stream state) , 
     (forall x y, fstate_lookup fState x = Some y -> Some ((Semantics.hd tr) x) = floatToReal y) ->  
    ( eval_formula ((denowify tlaExpr) >= R0) tr ->
     (match eval_NowTerm fState (tlaExpr) with 
        | Some f => match (floatToReal f) with
                      | Some num => (num >= 0)%R
                      | None => True
                    end
        | None => True
      end)) 
     /\ 
     (eval_formula ((denowify tlaExpr) < R0) tr ->
     (match eval_NowTerm fState (tlaExpr) with 
        | Some f => match (floatToReal f) with
                      | Some num => (num < 0)%R
                      | None => True
                    end
        | None => True
      end)).

                                         

   intros.
   split.
   intros.
   induction tlaExpr.
   destruct (eval_NowTerm fState (VarNowN v)) eqn:fstate_lookUp_des.
   - destruct f eqn:f_des.
     + simpl in *.
       apply H in fstate_lookUp_des.
       unfold eval_comp in H0.
       simpl in *.
       inversion fstate_lookUp_des.
       psatz R.
     + simpl in *.
       intuition.
     + simpl in *.
       intuition.
     + simpl in *.
       apply H in fstate_lookUp_des.
       unfold eval_comp in H0.
       simpl in *.
       inversion fstate_lookUp_des.
       apply H0.
   -  intuition.
   -  simpl in *.
      (*natural numbers*)
      admit.
   - simpl in *.
     destruct f eqn:f_des.
     + simpl in *.
       psatz R.
     + simpl in *.
       intuition.
     + simpl in *.
       intuition.
     + simpl in *.
       intuition.
   - unfold eval_formula in *.
     unfold eval_comp in *.
     pose proof deNowifyPlus as deNowifyPlus.
     rewrite <- deNowifyPlus in H0.
     simpl in IHtlaExpr2. 
     simpl in IHtlaExpr1.
     pose proof Rge_dec as Rge_dec1.
     pose proof Rge_dec as Rge_dec2.
     remember (eval_term (denowify tlaExpr1) (hd tr) (hd (tl tr)))%R as expr1.
     remember (eval_term (denowify tlaExpr2) (hd tr) (hd (tl tr)))%R as expr2.
     specialize (Rge_dec1 expr1 R0).
     specialize (Rge_dec2 expr2 R0).
     destruct Rge_dec1 eqn:Rge_dec1_des.
     +
       destruct Rge_dec2 eqn:Rge_dec2_des.
       *     
         assert (r':=r).
         apply IHtlaExpr1 in r'.
         assert (r0':=r0).
         apply IHtlaExpr2 in r0'.
         simpl in *.
         destruct (eval_NowTerm fState tlaExpr1)  eqn:evalExpr1_des.
         {
           destruct f eqn:f_des.
           -
             destruct (eval_NowTerm fState tlaExpr2) eqn:evalExpr2_des;
             try (destruct f0 eqn:f0_des);
               solve [
               solve [simpl in *;
               destruct Bool.eqb;
               simpl in *;
               intuition| simpl in *;intuition]| simpl in *;intuition].  
           - 
             destruct (eval_NowTerm fState tlaExpr2) eqn:evalExpr2_des;
              try (destruct f0 eqn:f0_des);
               solve [
               solve [simpl in *;
               destruct Bool.eqb;
               simpl in *;
               intuition| simpl in *;intuition]| simpl in *;intuition]. 
           - destruct (eval_NowTerm fState tlaExpr2) eqn:evalExpr2_des;
              try (destruct f0 eqn:f0_des);
               solve [
               solve [simpl in *;
               destruct Bool.eqb;
               simpl in *;
               intuition| simpl in *;intuition]| simpl in *;intuition].
           - destruct (eval_NowTerm fState tlaExpr2) eqn:evalExpr2_des.
             + 
               destruct f0 eqn:f0_des.
                 simpl in *.
                 intuition.
                 simpl in *.
                 intuition.
                 simpl in *.
                 intuition.
                 
                 
                 simpl in r'.
                 simpl in r0'.
                 pose proof Bplus_correct as Bplus_correct.
                 specialize (Bplus_correct custom_prec custom_emax eq_refl eq_refl Floats.Float.binop_pl mode_NE f f0). rewrite f0_des in Bplus_correct. 
                 rewrite f_des in Bplus_correct.
                 unfold is_finite in Bplus_correct.
                 specialize (Bplus_correct simpleTruth simpleTruth).
                 
                 intuition.
                 admit.
                 +
                admit.        
                } 
         admit.
         *
             admit.
             +
               admit.
              - admit.
                - admit.
                - admit.
 Qed.


 Lemma rltProof : forall r1 r2, (false = Rlt_bool r1 r2) -> (r1 >= r2)%R. 
                         intros.
                         unfold Rlt_bool in *.
                         Transparent Rcompare.
                         unfold Rcompare in *.
                         Transparent total_order_T.
                         destruct (total_order_T r1 r2).
                         destruct s.
                         intuition.
                         intuition.
                         intuition
                         intuition.
                         Qed.


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
  unfold fold_right.
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
                     (Bplus custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax))
                        Floats.Float.binop_pl mode_NE) 
                     (eval_NowTerm t1) (eval_NowTerm t2)
               | (t1 - t2)%SL =>
                   lift2
                     (Bminus custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax))
                        Floats.Float.binop_pl mode_NE) 
                     (eval_NowTerm t1) (eval_NowTerm t2)
               | (t1 * t2)%SL =>
                   lift2
                     (Bmult custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax))
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
                     (Bplus custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax))
                        Floats.Float.binop_pl mode_NE) 
                     (eval_NowTerm t1) (eval_NowTerm t2)
               | (t1 - t2)%SL =>
                   lift2
                     (Bminus custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax))
                        Floats.Float.binop_pl mode_NE) 
                     (eval_NowTerm t1) (eval_NowTerm t2)
               | (t1 * t2)%SL =>
                   lift2
                     (Bmult custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax))
                        Floats.Float.binop_pl mode_NE) 
                     (eval_NowTerm t1) (eval_NowTerm t2)
               end) expr2) as eval_expr2.
  revert IHexpr1 IHexpr2. intros IHexpr1 IHexpr2.

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
induction expr1_boundList as [ | Iexpr1_bound].
  + induction expr2_boundList as [| Iexpr2_bound].
    * simpl in *.
      intuition.
    * simpl in *.
      unfold plusBound.
      unfold plusMinusfoldListwithList.
      unfold plusMinusfoldBoundListWithTriple.
      simpl in *.
      pose proof fold_right_acc_empty as fold_right_acc_empty.
      specialize (fold_right_acc_empty expr2_boundList).
      rewrite -> fold_right_acc_empty.
      simpl.
      intuition.
  +  induction expr2_boundList as [| Iexpr2_bound].   
     * simpl in *.
       intuition.
     * pose proof fold_right_inferring_sublist_truth_from_list_truth as fold_right_inferring_sublist_truth_from_list_truth.
       assert (IHexpr1' := IHexpr1). assert (IHexpr2' := IHexpr2).
       apply fold_right_inferring_sublist_truth_from_list_truth in IHexpr1'.
       apply fold_right_inferring_sublist_truth_from_list_truth in IHexpr2'.
       apply IHexpr2_boundList in IHexpr2'.
       {  apply IHexpr1_boundList in IHexpr1'.
         revert IHexpr1 IHexpr2. intros IHexpr1 IHexpr2.
         unfold plusBound in *. 
         unfold plusMinusfoldListwithList in *.
         unfold plusMinusfoldBoundListWithTriple in *.
         simpl in *.
         remember ( fold_right
         (fun (triple : singleBoundTerm) (list : list singleBoundTerm) =>
          list ++
          simpleBound triple Iexpr1_bound PlusT
            (denowify expr1 + denowify expr2 >= RealT 0)%HP
          :: map
               (fun triple2 : singleBoundTerm =>
                simpleBound triple triple2 PlusT
                  (denowify expr1 + denowify expr2 >= RealT 0)%HP)
               expr1_boundList) List.nil expr2_boundList) as Iexpr1Andexpr1Withexpr2Gt0.
         remember (map
            (fun triple2 : singleBoundTerm =>
             simpleBound Iexpr2_bound triple2 PlusT
               (denowify expr1 + denowify expr2 >= RealT 0)%HP)
            expr1_boundList) as Iexpr2Withexpr1Gt0.
         remember (fold_right
        (fun (triple : singleBoundTerm) (list : list singleBoundTerm) =>
         list ++
         simpleBound4 triple Iexpr1_bound PlusT
           (denowify expr1 + denowify expr2 < RealT 0)%HP
         :: map
              (fun triple2 : singleBoundTerm =>
               simpleBound4 triple triple2 PlusT
                 (denowify expr1 + denowify expr2 < RealT 0)%HP)
              expr1_boundList) List.nil expr2_boundList) as Iexpr1Andexp1Withexpr2Lt0.
         remember (map
           (fun triple2 : singleBoundTerm =>
            simpleBound4 Iexpr2_bound triple2 PlusT
              (denowify expr1 + denowify expr2 < RealT 0)%HP) expr1_boundList) as Iexpr2Withexpr1Lt0.
         remember (fold_right
                   (fun (triple : singleBoundTerm)
                      (list : list singleBoundTerm) =>
                    list ++
                    map
                      (fun triple2 : singleBoundTerm =>
                       simpleBound triple triple2 PlusT
                         (denowify expr1 + denowify expr2 >= RealT 0)%HP)
                      expr1_boundList) List.nil expr2_boundList) as expr1Withexpr2Gt0.
         remember (fold_right
                  (fun (triple : singleBoundTerm)
                     (list : list singleBoundTerm) =>
                   list ++
                   map
                     (fun triple2 : singleBoundTerm =>
                      simpleBound4 triple triple2 PlusT
                        (denowify expr1 + denowify expr2 < RealT 0)%HP)
                     expr1_boundList) List.nil expr2_boundList) as expr1WithExpr2Lt0.
         revert IHexpr1'. intros IHexpr1'.
         unfold foldBoundProp in *.

         pose proof Bplus_correct as bplusCorrect. (*plus specific*)
         assert (Heqeval_expr1':=Heqeval_expr1).
         assert (Heqeval_expr2':=Heqeval_expr2).
         destruct eval_expr1 eqn: eval_expr1_des.
         -  destruct eval_expr2 eqn: eval_expr2_des.
            + specialize (bplusCorrect custom_prec custom_emax eq_refl eq_refl Floats.Float.binop_pl mode_NE f f0).  (*proving it for the round to nearest case*) 
              unfold floatToReal in *.
              unfold lift2.
              unfold lift2 in IHexpr1'.
              unfold lift2 in IHexpr2'.
              revert IHexpr2' IHexpr1'.
              intros IHexpr2' IHexpr1'.
              
              destruct f eqn:f_des.
              * destruct f0 eqn:f0_des;



 solve [ unfold Bplus in *;
                        destruct Bool.eqb ;        
                        simpl in IHexpr1';
                        simpl in IHexpr2';
                        apply fold_right_two_list_opp;
                        apply fold_right_two_list in IHexpr1';
                        split;
                        solve [apply IHexpr2'|
                                apply  fold_right_combine;
                                  decompose [and] IHexpr1';
                                  repeat split;
                                  solve [ apply H0 |
                                          simpl;
                                            revert IHexpr1 IHexpr2;
                                            intros IHexpr1 IHexpr2;
                                            decompose [and] IHexpr1;
                                            decompose [and] IHexpr2;
                                            simpl in H3;
                                            simpl in H5;
                                            assert (premGt0:= H1);
                                            simpl in premGt0;
                                            decompose [and] premGt0;
                                            apply H3 in H8;
                                            apply H5 in H6;
                                            unfold eval_comp in H10;
                                            simpl in H10;
                                            unfold eval_comp in H12;
                                            simpl in H12;
                                            destruct H7;
                                            remember (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1;
                                            remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1;
                                            remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2;
                                            remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2;
                                            destruct H8;
                                            destruct H6;
                                            clear H3 H7 H9 H10  IHexpr1_boundList IHexpr2_boundList Heqeval_expr1 Heqeval_expr2 HeqIexpr1Andexpr1Withexpr2Gt0 Iexpr1Andexpr1Withexpr2Gt0 Iexpr2Withexpr1Gt0 HeqIexpr2Withexpr1Gt0 Iexpr1Andexp1Withexpr2Lt0 HeqIexpr1Andexp1Withexpr2Lt0 Iexpr2Withexpr1Lt0 HeqIexpr2Withexpr1Lt0 Heqexpr1Withexpr2Gt0 Heqexpr1WithExpr2Lt0 bplusCorrect IHexpr2' IHexpr1' Heqlb2 Hequb2 IHexpr1 Heqlb1 Hequb1 Hequb1 H H0 H1 H2 H4 H5 IHexpr2 expr1WithExpr2Lt0 expr1Withexpr2Gt0 expr1Withexpr2Gt0 expr1_boundList expr2_boundList f0_des f_des f f0 Heqeval_expr1' Heqeval_expr2' fold_right_inferring_sublist_truth_from_list_truth premGt0 f2RPremise;
                                            unfold error;
                                            simpl;
                                            repeat match goal with
                                                     | H : @eq R _ _ |- _ => revert H
                                                     | H : @Rle _ _ |- _ => revert H
                                                     | H : @Rge _ _ |- _ => revert H
                                                     | H : @Rlt _ _ |- _ => revert H
                                                     | H :@ Rgt _ _ |- _ => revert H
                                                     | H : @Rge _ _ |- _ => revert H
                                                   end;
                                            psatz R]]
              | simpl;
                rewrite fold_right_truth;
                intuition
              | solve [ 
                      simpl;
                      simpl in IHexpr1';
                      simpl in IHexpr2';
                      apply fold_right_two_list_opp;
                      apply fold_right_two_list in IHexpr1';
                      split;
                      solve [ apply IHexpr2'|
                              apply  fold_right_combine;
                                decompose [and] IHexpr1';
                                repeat split;
                                solve [ apply H0 |
                                        simpl;
                                          revert IHexpr1 IHexpr2;
                                          intros IHexpr1 IHexpr2;
                                          decompose [and] IHexpr1;
                                          decompose [and] IHexpr2;
                                          simpl in H3;
                                          simpl in H5;
                                          assert (premGt0:= H1);
                                          simpl in premGt0;
                                          decompose [and] premGt0;
                                          apply H3 in H8;
                                          apply H5 in H6;
                                          unfold eval_comp in H10;
                                          simpl in H10;
                                          unfold eval_comp in H12;
                                          simpl in H12;
                                          remember (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1;
                                          remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1;
                                          remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2;
                                          remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2;
                                          destruct H8;
                                          destruct H6;
                                          clear H3 H7 H9 H10 IHexpr1_boundList IHexpr2_boundList Heqeval_expr1 Heqeval_expr2 HeqIexpr1Andexpr1Withexpr2Gt0 Iexpr1Andexpr1Withexpr2Gt0 Iexpr2Withexpr1Gt0 HeqIexpr2Withexpr1Gt0 Iexpr1Andexp1Withexpr2Lt0 HeqIexpr1Andexp1Withexpr2Lt0 Iexpr2Withexpr1Lt0 HeqIexpr2Withexpr1Lt0 Heqexpr1Withexpr2Gt0 Heqexpr1WithExpr2Lt0 bplusCorrect IHexpr2' IHexpr1' Heqlb2 Hequb2 IHexpr1 Heqlb1 Hequb1 Hequb1 H H0 H1 H2 H4 H5 IHexpr2 expr1WithExpr2Lt0 expr1Withexpr2Gt0 expr1Withexpr2Gt0 expr1_boundList expr2_boundList f0_des f_des f f0 Heqeval_expr1' Heqeval_expr2' fold_right_inferring_sublist_truth_from_list_truth premGt0 f2RPremise;
                                          unfold error;
                                          simpl;
                                          repeat match goal with
                                                   | H : @eq R _ _ |- _ => revert H
                                                   | H : @Rle _ _ |- _ => revert H
                                                   | H : @Rge _ _ |- _ => revert H
                                                   | H : @Rlt _ _ |- _ => revert H
                                                   | H :@ Rgt _ _ |- _ => revert H
                                                   | H : @Rge _ _ |- _ => revert H
                                                 end;
                                          psatz R]]]].
                  

 (*f is zero and the rest*)

              *     
                destruct f0 eqn:f0_des;
                solve [simpl;
                        rewrite fold_right_truth;
                        intuition |  unfold Bplus;
                                    destruct Bool.eqb;
                                    rewrite fold_right_truth;
                                    intuition].
              *   (*f is infinity and the rest*)  

                destruct f0 eqn:f0_des;
                solve [simpl;
                        rewrite fold_right_truth;
                        intuition |  unfold Bplus;
                                    destruct Bool.eqb;
                                    rewrite fold_right_truth;
                                    intuition].
              (*f is nan and the rest*)
              *
                destruct f0 eqn:f0_des.

                 
                  solve [ 
                      simpl;
                      simpl in IHexpr1';
                      simpl in IHexpr2';
                      apply fold_right_two_list_opp;
                      apply fold_right_two_list in IHexpr1';
                      split;
                      solve [ apply IHexpr2'|
                              apply  fold_right_combine;
                                decompose [and] IHexpr1';
                                repeat split;
                                solve [ apply H0 |
                                        simpl;
                                          revert IHexpr1 IHexpr2;
                                          intros IHexpr1 IHexpr2;
                                          decompose [and] IHexpr1;
                                          decompose [and] IHexpr2;
                                          simpl in H3;
                                          simpl in H5;
                                          assert (premGt0:= H1);
                                          simpl in premGt0;
                                          decompose [and] premGt0;
                                          apply H3 in H8;
                                          apply H5 in H6;
                                          unfold eval_comp in H12;
                                          simpl in H12;
                                          unfold eval_comp in H10;
                                          simpl in H10;
                                          remember (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1;
                                          remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1;
                                          remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2;
                                          remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2;
                                          destruct H8;
                                          destruct H6;
      
                                          clear H3 H7 H9 H10 IHexpr1_boundList IHexpr2_boundList Heqeval_expr1 Heqeval_expr2 HeqIexpr1Andexpr1Withexpr2Gt0 Iexpr1Andexpr1Withexpr2Gt0 Iexpr2Withexpr1Gt0 HeqIexpr2Withexpr1Gt0 Iexpr1Andexp1Withexpr2Lt0 HeqIexpr1Andexp1Withexpr2Lt0 Iexpr2Withexpr1Lt0 HeqIexpr2Withexpr1Lt0 Heqexpr1Withexpr2Gt0 Heqexpr1WithExpr2Lt0 bplusCorrect IHexpr2' IHexpr1' Heqlb2 Hequb2 IHexpr1 Heqlb1 Hequb1 Hequb1 H H0 H1 H2 H4 H5 IHexpr2 expr1WithExpr2Lt0 expr1Withexpr2Gt0 expr1Withexpr2Gt0 expr1_boundList expr2_boundList f0_des f_des f f0 Heqeval_expr1' Heqeval_expr2' fold_right_inferring_sublist_truth_from_list_truth premGt0 f2RPremise;
                                          unfold error;
                                          simpl;
                                          repeat match goal with
                                                   | H : @eq R _ _ |- _ => revert H
                                                   | H : @Rle _ _ |- _ => revert H
                                                   | H : @Rge _ _ |- _ => revert H
                                                   | H : @Rlt _ _ |- _ => revert H
                                                   | H :@ Rgt _ _ |- _ => revert H
                                                   | H : @Rge _ _ |- _ => revert H
                                                 end;
                                          psatz R]]].

            

                simpl;
                  rewrite fold_right_truth;
                  intuition. (*one is infinity and other is finite*)

                simpl;
                  rewrite fold_right_truth;
                  intuition.

                
                match goal with 
                  | |- fold_right (fun x y => match match ?plusResult with _ => _ end with _ => _ end) _ _ => 
                    remember plusResult
                end.
                
                
                match goal with 
                  | |- fold_right (fun x y => match ?result with _ => _ end) _ _ => 
                    remember result
                end.

                destruct o eqn:o_des.
                {
                  apply fold_right_two_list_opp.
                  repeat split.
                  -
                    apply IHexpr2'.
                  - 
                    apply fold_right_two_list in IHexpr1'.
                    decompose [and] IHexpr1'.
                    apply H0.
                  -
                     inversion Heqo.
                     inversion H1.
                     simpl.
                     revert IHexpr1 IHexpr2.
                     intros IHexpr1 IHexpr2.
                     decompose [and] IHexpr1.
                     decompose [and] IHexpr2.
                     simpl in H1.
                     simpl in H3.
                     assert (premGt0:= H).
                     simpl in premGt0.
                     decompose [and] premGt0. 
                     apply H5 in H6.
                     apply H3 in H8.
                     unfold eval_comp in H10.
                     unfold eval_comp in H12.
                     unfold eval_comp in H7.
                     unfold eval_comp in H9.
                     simpl in H10.
                     simpl in H12.
                     simpl in H7.
                     simpl in H9.
                     remember (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1;
                       remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1;
                       remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2;
                       remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2.
                     destruct H6.
                     destruct H8.
                     destruct b1 eqn: b1_des. 
                     + 
                       simpl in Heqo.
                       inversion Heqo.
                       
                      
                      clear o_des  Heqo H3 H4 H5 IHexpr1_boundList IHexpr2_boundList Heqeval_expr1 Heqeval_expr2 HeqIexpr1Andexpr1Withexpr2Gt0 Iexpr1Andexpr1Withexpr2Gt0 Iexpr2Withexpr1Gt0 HeqIexpr2Withexpr1Gt0 Iexpr1Andexp1Withexpr2Lt0 HeqIexpr1Andexp1Withexpr2Lt0 Iexpr2Withexpr1Lt0 HeqIexpr2Withexpr1Lt0 Heqexpr1Withexpr2Gt0 Heqexpr1WithExpr2Lt0 bplusCorrect IHexpr2' IHexpr1' Heqlb2 Hequb2 IHexpr1 Heqlb1 Hequb1 Hequb1 H H0 H1 H2 IHexpr2 expr1WithExpr2Lt0 expr1Withexpr2Gt0 expr1Withexpr2Gt0 expr1_boundList expr2_boundList f0_des f_des f f0 Heqeval_expr1' Heqeval_expr2' fold_right_inferring_sublist_truth_from_list_truth premGt0 f2RPremise.
                      
                      repeat match goal with
                             | H : @eq R _ _ |- _ => revert H
                             | H : @Rle _ _ |- _ => revert H
                             | H : @Rge _ _ |- _ => revert H
                             | H : @Rlt _ _ |- _ => revert H
                             | H :@ Rgt _ _ |- _ => revert H
                             | H : @Rge _ _ |- _ => revert H
                           end.
                      Declare ML Module "z3Tactic".
                      unfold error.
                      simpl.
                      z3Tactic.
                      
                      psatz R.
                     + 
                       inversion H1.
                     +
                       inversion H1.
                     + 
                       inversion H1.


                         Require Import compcert.flocq.Prop.Fprop_relative.
                         
                         pose proof relative_error as Rel_Err.
                         Require Import compcert.flocq.Core.Fcore_FLT.
                         remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp.
                         specialize (Rel_Err radix2 round_fexp).
                         Require Import compcert.flocq.Core.Fcore_generic_fmt.
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
                         specialize (Rel_Err (custom_emin)%Z custom_prec).

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
                         
                         specialize (Rel_Err precThm (round_mode mode_NE)).
                         Definition choiceDef := (fun x => negb (Zeven x)).
                         specialize (Rel_Err (valid_rnd_N choiceDef)).
                         revert Rel_Err. intros Rel_Err.


                       pose proof Bplus_correct as bplus_correct.
                       specialize (bplus_correct custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) Floats.Float.binop_pl mode_NE (B754_finite 53 1024 b m e e0) (B754_finite 53 1024 b0 m0 e1 e2)).
                       unfold is_finite in bplus_correct.
                       specialize (bplus_correct simpleTruth simpleTruth).
                       remember (Rlt_bool
                       (Rabs
                          (Fcore_generic_fmt.round radix2
                             (Fcore_FLT.FLT_exp
                                (3 - custom_emax - custom_prec) custom_prec)
                             (round_mode mode_NE)
                             (B2R custom_prec custom_emax
                                (B754_finite 53 1024 b m e e0) +
                              B2R custom_prec custom_emax
                                (B754_finite 53 1024 b0 m0 e1 e2))))
                       (bpow radix2 custom_emax)) as rltBoolInfo. 
                       destruct rltBoolInfo eqn:rltBoolInfo_des.
                       *
                         decompose [and] bplus_correct.
                         revert Heqb1 H15. intros Heqb1 H15.
                         
                         simpl in H15.
                         simpl in Heqb1.
                         rewrite <- Heqb1 in H15.
                         
                         simpl in H15.
                         rewrite H15.
                         
                         
                       
                         
                         revert H10 H12 H8 H13 H11 H6 H7 H9. intros  H10 H12 H8 H13 H11 H6 H7 H9. 
                         simpl in H11. simpl in H6.
                         remember (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1;
                           remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1;
                           remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2;
                           remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2.
                         
                         remember (F2R {| Fnum := cond_Zopp b (Z.pos m); Fexp := e |}) as res1.
                         remember (F2R {| Fnum := cond_Zopp b0 (Z.pos m0); Fexp := e1 |}) as res2.
                         specialize (Rel_Err (res1+res2)%R).
                         clear Heqeval_expr1 IHexpr1_boundList IHexpr2_boundList fold_right_inferring_sublist_truth_from_list_truth  Heqeval_expr1'  HeqrltBoolInfo Hequb2  Hequb1 H1 H2 H5 Heqlb2 IHexpr1 bplus_correct H3 IHexpr2 Heqlb1 IHexpr1' IHexpr2' Heqo H14  Heqres2  bplusCorrect H18 Heqres1 Heqb1 H17 H4 H0 H Heqeval_expr2' Heqeval_expr2 premGt0 e4 f2RPremise  e2 Iexpr1_bound expr2_boundList e2 Iexpr1_bound expr2_boundList Iexpr2_bound expr1_boundList e0.
                         
                         destruct (Rle_dec (bpow radix2 custom_emin)  (Rabs (res1 + res2))).
                       {
                         apply Rel_Err in r.
                         unfold Rabs in *.
                         destruct Rcase_abs in r. 
                         
                         -
                           clear Rel_Err.
                           destruct Rcase_abs in r.
                           +
                             
                             simpl in *.

                             match goal with 
                               | |- Rle _ ?Y => remember Y 
                             end.
                             clear Heqr2.
                             clear H10 H9.

                             repeat match goal with
                                      | H : @eq R _ _ |- _ => revert H
                                      | H : @Rle _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                      | H : @Rlt _ _ |- _ => revert H
                                      | H :@ Rgt _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                    end.
                             unfold error.
                             simpl. 
                             z3Tactic.
                             psatz R.                         
                             
                           +
                              simpl in *.

                             match goal with 
                               | |- Rle _ ?Y => remember Y 
                             end.
                             clear Heqr2.
                             clear H10 H9.

                             repeat match goal with
                                      | H : @eq R _ _ |- _ => revert H
                                      | H : @Rle _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                      | H : @Rlt _ _ |- _ => revert H
                                      | H :@ Rgt _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                    end.
                             unfold error.
                             simpl. 
                             z3Tactic.
                             psatz R.     
                           
                         -
                           clear Rel_Err.
                           destruct Rcase_abs in r.
                           +
                             simpl in *.
                             match goal with 
                               | |- Rle _ ?Y => remember Y 
                             end.
                             clear Heqr2.
                             clear H10 H9.
                             
                             repeat match goal with
                                      | H : @eq R _ _ |- _ => revert H
                                      | H : @Rle _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                      | H : @Rlt _ _ |- _ => revert H
                                      | H :@ Rgt _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                    end.
                             unfold error.
                             simpl. 
                             z3Tactic.
                             clear H7.
                             (* psatz R.*) admit.
                             
                           +
                             simpl in *.
                             match goal with 
                               | |- Rle _ ?Y => remember Y 
                             end.
                             clear Heqr2.
                             clear H10 H9.
                             
                             repeat match goal with
                                      | H : @eq R _ _ |- _ => revert H
                                      | H : @Rle _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                      | H : @Rlt _ _ |- _ => revert H
                                      | H :@ Rgt _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                    end.
                             unfold error.
                             simpl. 
                             z3Tactic.
                             clear H7.
                             psatz R.   
                             
                       }                         
                       {
                         unfold floatMin in *.
                         unfold floatMax in *.
                         match goal with 
                           | |- Rle _ ?Y => remember Y 
                         end.
                         unfold Rabs in n.
                         clear Heqr Rel_Err H10.
                         unfold error.
                         apply Rnot_le_lt in n.
                         
                         simpl in *.
                         destruct Rcase_abs in n.
                         -
                           destruct H7.
                           +
                             clear  H9.
                             repeat match goal with
                                      | H : @eq R _ _ |- _ => revert H
                                      | H : @Rle _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                      | H : @Rlt _ _ |- _ => revert H
                                      | H :@ Rgt _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                    end.
                             (* z3Tactic.*)
                             (* psatz R.*)
                             admit.
                           +  
                             destruct H.
                             *
                               clear H12 H9.
                               repeat match goal with
                                        | H : @eq R _ _ |- _ => revert H
                                        | H : @Rle _ _ |- _ => revert H
                                        | H : @Rge _ _ |- _ => revert H
                                        | H : @Rlt _ _ |- _ => revert H
                                        | H :@ Rgt _ _ |- _ => revert H
                                        | H : @Rge _ _ |- _ => revert H
                                      end.
                               (* z3Tactic.*) (*did not work*) 
                               (*psatz R*)
                               admit.
                             *
                               decompose [and] H.
                               clear H.
                               clear H8 H9 H13 r0 n H11 H0 H6.
                             
                             repeat match goal with
                                        | H : @eq R _ _ |- _ => revert H
                                        | H : @Rle _ _ |- _ => revert H
                                        | H : @Rge _ _ |- _ => revert H
                                        | H : @Rlt _ _ |- _ => revert H
                                        | H :@ Rgt _ _ |- _ => revert H
                                        | H : @Rge _ _ |- _ => revert H
                                    end.
                            
                             z3Tactic. (*this is also wrong*)
                             admit.
                         -
                           simpl in *.
                           admit.
                       }
                       *
                         
                         apply rltProof in HeqrltBoolInfo.
                         revert HeqrltBoolInfo.
                         intros HeqrltBoolInfo.
                         unfold Rabs in HeqrltBoolInfo.
                         destruct Rcase_abs in HeqrltBoolInfo.
                         {
                           revert H6 H5 H13 H9 H10 H12 H8 H7 H3. intros H6 H5 H13 H9 H10 H12 H8 H7 H3.
                           clear bplus_correct.
                           simpl in *.
                           
                           remember (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1;
                             remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1;
                             remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2;
                             remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2.
                           
                           remember (F2R {| Fnum := cond_Zopp b0 (Z.pos m0); Fexp := e1 |}) as res2.
                           remember (F2R {| Fnum := cond_Zopp b (Z.pos m); Fexp := e |}) as res1.


                           specialize (Rel_Err (res1+res2)%R).

                           remember (round radix2 (FLT_exp (-1074) custom_prec)
                                           (Znearest (fun x : Z => negb (Zeven x))) 
                                           (res1 + res2)) as roundedValue.

                           admit.

                         }
                         {
                           admit.
                         }
                  -
                     

                     inversion Heqo.
                     inversion H1.
                     simpl.
                     revert IHexpr1 IHexpr2.
                     intros IHexpr1 IHexpr2.
                     decompose [and] IHexpr1.
                     decompose [and] IHexpr2.
                     simpl in H1.
                     simpl in H3.
                     assert (premGt0:= H).
                     simpl in premGt0.
                     decompose [and] premGt0. 
                     apply H5 in H6.
                     apply H3 in H8.
                     unfold eval_comp in H10.
                     unfold eval_comp in H12.
                     unfold eval_comp in H7.
                     unfold eval_comp in H9.
                     simpl in H10.
                     simpl in H12.
                     simpl in H7.
                     simpl in H9.
                     remember (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1;
                       remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1;
                       remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2;
                       remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2.
                     destruct H6.
                     destruct H8.
                     simpl in *.
                     destruct b1 eqn: b1_des. 
                     + 
                       simpl in Heqo.
                       inversion Heqo.
                       
                      
                      clear o_des  Heqo H3 H4 H5 IHexpr1_boundList IHexpr2_boundList Heqeval_expr1 Heqeval_expr2 HeqIexpr1Andexpr1Withexpr2Gt0 Iexpr1Andexpr1Withexpr2Gt0 Iexpr2Withexpr1Gt0 HeqIexpr2Withexpr1Gt0 Iexpr1Andexp1Withexpr2Lt0 HeqIexpr1Andexp1Withexpr2Lt0 Iexpr2Withexpr1Lt0 HeqIexpr2Withexpr1Lt0 Heqexpr1Withexpr2Gt0 Heqexpr1WithExpr2Lt0 bplusCorrect IHexpr2' IHexpr1' Heqlb2 Hequb2 IHexpr1 Heqlb1 Hequb1 Hequb1 H H0 H1 H2 IHexpr2 expr1WithExpr2Lt0 expr1Withexpr2Gt0 expr1Withexpr2Gt0 expr1_boundList expr2_boundList f0_des f_des f f0 Heqeval_expr1' Heqeval_expr2' fold_right_inferring_sublist_truth_from_list_truth premGt0 f2RPremise.
                      
                      repeat match goal with
                             | H : @eq R _ _ |- _ => revert H
                             | H : @Rle _ _ |- _ => revert H
                             | H : @Rge _ _ |- _ => revert H
                             | H : @Rlt _ _ |- _ => revert H
                             | H :@ Rgt _ _ |- _ => revert H
                             | H : @Rge _ _ |- _ => revert H
                           end.
                      Declare ML Module "z3Tactic".
                      unfold error.
                      simpl.
                      remember ( F2R {| Fnum := cond_Zopp b0 (Z.pos m0); Fexp := e1 |}) as res2.
                      remember ( F2R {| Fnum := cond_Zopp b (Z.pos m); Fexp := e |}) as res1.
                      unfold floatMax.
                      z3Tactic.
                      
                      psatz R.
                     + 
                       inversion H1.
                     +
                       inversion H1.
                     + 
                       inversion H1.


                         Require Import compcert.flocq.Prop.Fprop_relative.
                         
                         pose proof relative_error as Rel_Err.
                         Require Import compcert.flocq.Core.Fcore_FLT.
                         remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp.
                         specialize (Rel_Err radix2 round_fexp).
                         Require Import compcert.flocq.Core.Fcore_generic_fmt.
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
                         specialize (Rel_Err (custom_emin)%Z custom_prec).

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
                         
                         specialize (Rel_Err precThm (round_mode mode_NE)).
                         Definition choiceDef := (fun x => negb (Zeven x)).
                         specialize (Rel_Err (valid_rnd_N choiceDef)).
                         revert Rel_Err. intros Rel_Err.


                       pose proof Bplus_correct as bplus_correct.
                       specialize (bplus_correct custom_prec custom_emax (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) (@eq_refl Datatypes.comparison
                   (Z.compare custom_prec custom_emax)) Floats.Float.binop_pl mode_NE (B754_finite 53 1024 b m e e0) (B754_finite 53 1024 b0 m0 e1 e2)).
                       unfold is_finite in bplus_correct.
                       specialize (bplus_correct simpleTruth simpleTruth).
                       remember (Rlt_bool
                       (Rabs
                          (Fcore_generic_fmt.round radix2
                             (Fcore_FLT.FLT_exp
                                (3 - custom_emax - custom_prec) custom_prec)
                             (round_mode mode_NE)
                             (B2R custom_prec custom_emax
                                (B754_finite 53 1024 b m e e0) +
                              B2R custom_prec custom_emax
                                (B754_finite 53 1024 b0 m0 e1 e2))))
                       (bpow radix2 custom_emax)) as rltBoolInfo. 
                       destruct rltBoolInfo eqn:rltBoolInfo_des.
                       *
                         decompose [and] bplus_correct.
                         revert Heqb1 H15. intros Heqb1 H15.
                         
                         simpl in H15.
                         simpl in Heqb1.
                         rewrite <- Heqb1 in H15.
                         
                         simpl in H15.
                         rewrite H15.
                         
                         
                       
                         
                         revert H10 H12 H8 H13 H11 H6 H7 H9. intros  H10 H12 H8 H13 H11 H6 H7 H9. 
                         simpl in H11. simpl in H6.
                         remember (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1;
                           remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1;
                           remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2;
                           remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2.
                         
                         remember (F2R {| Fnum := cond_Zopp b (Z.pos m); Fexp := e |}) as res1.
                         remember (F2R {| Fnum := cond_Zopp b0 (Z.pos m0); Fexp := e1 |}) as res2.
                         specialize (Rel_Err (res1+res2)%R).
                         clear Heqeval_expr1 IHexpr1_boundList IHexpr2_boundList fold_right_inferring_sublist_truth_from_list_truth  Heqeval_expr1'  HeqrltBoolInfo Hequb2  Hequb1 H1 H2 H5 Heqlb2 IHexpr1 bplus_correct H3 IHexpr2 Heqlb1 IHexpr1' IHexpr2' Heqo H14  Heqres2  bplusCorrect H18 Heqres1 Heqb1 H17 H4 H0 H Heqeval_expr2' Heqeval_expr2 premGt0 e4 f2RPremise  e2 Iexpr1_bound expr2_boundList e2 Iexpr1_bound expr2_boundList Iexpr2_bound expr1_boundList e0.
                         
                         destruct (Rle_dec (bpow radix2 custom_emin)  (Rabs (res1 + res2))).
                       {
                         apply Rel_Err in r.
                         unfold Rabs in *.
                         destruct Rcase_abs in r. 
                         
                         -
                           clear Rel_Err.
                           destruct Rcase_abs in r.
                           +
                             
                             simpl in *.

                             match goal with 
                               | |- Rle _ ?Y => remember Y 
                             end.
                             clear Heqr2.
                             clear H10 H9.

                             repeat match goal with
                                      | H : @eq R _ _ |- _ => revert H
                                      | H : @Rle _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                      | H : @Rlt _ _ |- _ => revert H
                                      | H :@ Rgt _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                    end.
                             unfold error.
                             simpl. 
                             z3Tactic.
                             psatz R.                         
                             
                           +
                              simpl in *.

                             match goal with 
                               | |- Rle _ ?Y => remember Y 
                             end.
                             clear Heqr2.
                             clear H10 H9.

                             repeat match goal with
                                      | H : @eq R _ _ |- _ => revert H
                                      | H : @Rle _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                      | H : @Rlt _ _ |- _ => revert H
                                      | H :@ Rgt _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                    end.
                             unfold error.
                             simpl. 
                             z3Tactic.
                             psatz R.     
                           
                         -
                           clear Rel_Err.
                           destruct Rcase_abs in r.
                           +
                             simpl in *.
                             match goal with 
                               | |- Rle _ ?Y => remember Y 
                             end.
                             clear Heqr2.
                             clear H10 H9.
                             
                             repeat match goal with
                                      | H : @eq R _ _ |- _ => revert H
                                      | H : @Rle _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                      | H : @Rlt _ _ |- _ => revert H
                                      | H :@ Rgt _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                    end.
                             unfold error.
                             simpl. 
                             z3Tactic.
                             clear H7.
                             (* psatz R.*) admit.
                             
                           +
                             simpl in *.
                             match goal with 
                               | |- Rle _ ?Y => remember Y 
                             end.
                             clear Heqr2.
                             clear H10 H9.
                             
                             repeat match goal with
                                      | H : @eq R _ _ |- _ => revert H
                                      | H : @Rle _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                      | H : @Rlt _ _ |- _ => revert H
                                      | H :@ Rgt _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                    end.
                             unfold error.
                             simpl. 
                             z3Tactic.
                             clear H7.
                             psatz R.   
                             
                       }                         
                       {
                         unfold floatMin in *.
                         unfold floatMax in *.
                         match goal with 
                           | |- Rle _ ?Y => remember Y 
                         end.
                         unfold Rabs in n.
                         clear Heqr Rel_Err H10.
                         unfold error.
                         apply Rnot_le_lt in n.
                         
                         simpl in *.
                         destruct Rcase_abs in n.
                         -
                           destruct H7.
                           +
                             clear  H9.
                             repeat match goal with
                                      | H : @eq R _ _ |- _ => revert H
                                      | H : @Rle _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                      | H : @Rlt _ _ |- _ => revert H
                                      | H :@ Rgt _ _ |- _ => revert H
                                      | H : @Rge _ _ |- _ => revert H
                                    end.
                             (* z3Tactic.*)
                             (* psatz R.*)
                             admit.
                           +  
                             destruct H.
                             *
                               clear H12 H9.
                               repeat match goal with
                                        | H : @eq R _ _ |- _ => revert H
                                        | H : @Rle _ _ |- _ => revert H
                                        | H : @Rge _ _ |- _ => revert H
                                        | H : @Rlt _ _ |- _ => revert H
                                        | H :@ Rgt _ _ |- _ => revert H
                                        | H : @Rge _ _ |- _ => revert H
                                      end.
                               (* z3Tactic.*) (*did not work*) 
                               (*psatz R*)
                               admit.
                             *
                               decompose [and] H.
                               clear H.
                               clear H8 H9 H13 r0 n H11 H0 H6.
                             
                             repeat match goal with
                                        | H : @eq R _ _ |- _ => revert H
                                        | H : @Rle _ _ |- _ => revert H
                                        | H : @Rge _ _ |- _ => revert H
                                        | H : @Rlt _ _ |- _ => revert H
                                        | H :@ Rgt _ _ |- _ => revert H
                                        | H : @Rge _ _ |- _ => revert H
                                    end.
                            
                             z3Tactic. (*this is also wrong*)
                             admit.
                         -
                           simpl in *.
                           admit.
                       }
                       *
                         
                         apply rltProof in HeqrltBoolInfo.
                         revert HeqrltBoolInfo.
                         intros HeqrltBoolInfo.
                         unfold Rabs in HeqrltBoolInfo.
                         destruct Rcase_abs in HeqrltBoolInfo.
                         {
                           revert H6 H5 H13 H9 H10 H12 H8 H7 H3. intros H6 H5 H13 H9 H10 H12 H8 H7 H3.
                           clear bplus_correct.
                           simpl in *.
                           
                           remember (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1;
                             remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1;
                             remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2;
                             remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2.
                           
                           remember (F2R {| Fnum := cond_Zopp b0 (Z.pos m0); Fexp := e1 |}) as res2.
                           remember (F2R {| Fnum := cond_Zopp b (Z.pos m); Fexp := e |}) as res1.


                           specialize (Rel_Err (res1+res2)%R).

                           remember (round radix2 (FLT_exp (-1074) custom_prec)
                                           (Znearest (fun x : Z => negb (Zeven x))) 
                                           (res1 + res2)) as roundedValue.

                           admit.

                         }
                         {
                           admit.
                         }
                    
}
destruct Rabs in HeqrltBoolInfo.
intros.
                       *
                         rewrite <- H15.
                         simpl in *.
                         remember (F2R {| Fnum := cond_Zopp b0 (Z.pos m0); Fexp := e1 |}) as res1.
                         remember (F2R {| Fnum := cond_Zopp b (Z.pos m); Fexp := e |}) as res2.
                         Print Bplus_correct.
                         rewrite <- H6.
                         rewrite <- H11.
                         clear f2RPremise.
                         
                         admit. admit.
                       Qed.
                       Set Printing All.
                       match goal with
                             | H : @eq (binary_float custom_prec custom_emax) ?X ?Y |- _ => remember Y
                       end.
                       
                       match 
                       rewrite <- Heqb1 in H12.
                       unfold B2R in H12.
                       
                       simpl bplus_correct.
                       
                       destruct Rabs.
                       unfold Rabs in bplus_correct.
                       Print Rabs.
                    unfold eval_comp in H5.
                    simpl in H5.
                    unfold eval_comp in H8.
                    simpl in H8.
                    remember (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1;
                    remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1;
                    remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2;
                    remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2.
                    destruct H4;
                    destruct H6.
                    
                    clear Heqeval_expr1
                    
                    unfold error.
                    simpl.
                    
                    repeat match goal with
                             | H : @eq R _ _ |- _ => revert H
                             | H : @Rle _ _ |- _ => revert H
                             | H : @Rge _ _ |- _ => revert H
                             | H : @Rlt _ _ |- _ => revert H
                             | H :@ Rgt _ _ |- _ => revert H
                             | H : @Rge _ _ |- _ => revert H
                           end.
                    psatz R
                    
                    unfold error.
                    
                }

                apply 
                
                  
                
                Print eq_refl.
                
                remember (  
                    match
                      Bplus custom_prec custom_emax eq_refl eq_refl Floats.Float.binop_pl
                            mode_NE (B754_finite 53 1024 b m e e0)
                            (B754_finite 53 1024 b0 m0 e1 e2)
                    with
                      | B754_zero _ =>
                        Some
                          (B2R 53 1024
                               (Bplus custom_prec custom_emax eq_refl eq_refl
                                      Floats.Float.binop_pl mode_NE
                                      (B754_finite 53 1024 b m e e0)
                                      (B754_finite 53 1024 b0 m0 e1 e2)))
                      | B754_infinity _ => None
                      | B754_nan _ _ => None
                      | B754_finite _ _ _ _ =>
                        Some
                          (B2R 53 1024
                               (Bplus custom_prec custom_emax eq_refl eq_refl
                                      Floats.Float.binop_pl mode_NE
                                      (B754_finite 53 1024 b m e e0)
                                      (B754_finite 53 1024 b0 m0 e1 e2)))
                    end) as bplusResult.
                
                
                
                
                destruct bplusResult eqn:bplusResult_des.
                
                 
                 Eval compute in (Pos.compare (xI (xO (xI (xO (xI xH)))))
                  (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO xH))))))))))).
                 simpl.
                 apply fold_right_two_list_opp.
                
                      (*proof done till here*)
                       Admitted.
