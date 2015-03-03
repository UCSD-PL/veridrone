Require Import Coq.micromega.Psatz.
Require Import Coq.Reals.Raxioms.
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
Require Import compcert.flocq.Prop.Fprop_relative.
Require Import compcert.flocq.Core.Fcore_Raux.
Require Import compcert.flocq.Core.Fcore_FLT.
Require Import compcert.flocq.Core.Fcore_generic_fmt.                       



Require Import compcert.flocq.Core.Fcore_Raux.


Local Open Scope HP_scope.


Definition error := bpow radix2 (- (custom_prec) + 1).
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
  mkSBT ((combFunc (lb triple1)  (ub triple2)) * (RealT R1- RealT error)) 
        ((combFunc (ub triple1) (lb triple2)) * (RealT R1 + RealT error)) 
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
  mkSBT ((combFunc (lb triple1)  (ub triple2)) * (RealT R1+ RealT error)) 
        ((combFunc (ub triple1) (lb triple2)) * (RealT R1 - RealT error)) 
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

Print Bplus_correct.
Check Bplus_correct.
Definition combineTriplePlus (triple triple2 : singleBoundTerm) :=
  ((simpleBound triple triple2 PlusT 
                (premise triple /\ 
                 premise triple2 /\ 
                 ((floatMin <= lb triple + lb triple2) \/ (floatMin <= ((0 -  ub triple) + (0 - ub triple2))) ) /\ 
                 ((ub triple + ub triple2)*(1+error) < floatMax) /\
                 (((0 - lb triple + (0 - lb triple2))*(1+error)) < floatMax) /\ 
                 (lb triple + lb triple2 >= R0)))
     :: ((simpleBound4 triple triple2 PlusT 
                       (premise triple /\ 
                        premise triple2 /\ 
                        ((floatMin <= lb triple + lb triple2) \/ (floatMin <= ((0 - ub triple) + (0 - ub triple2)))) /\ 
                        ((ub triple + ub triple2)*(1+error) < floatMax) /\
                        (((0 - lb triple + (0 - lb triple2))*(1+error)) < floatMax) /\ 
                        (ub triple + ub triple2 < R0))) ::
                                                        List.nil)).   

Definition combineTripleMinus (triple triple2 : singleBoundTerm) :=
  ((simpleBound2 triple triple2 MinusT 
                (premise triple /\ 
                 premise triple2  /\ 
                 (lb triple >= ub triple2) /\
                 ((floatMin <= lb triple - ub triple2) /\ 
                ((ub triple - lb triple2)*(1+error) < floatMax))))
     :: (simpleBound5 triple triple2 MinusT 
                       (premise triple /\ 
                        premise triple2 /\
                        (ub triple <= lb triple2) /\
                        ((floatMin <= lb triple2 - ub triple)) /\
                        ((ub triple2 - lb triple)*(1+error) < floatMax)) ::
                                                        List.nil)).   



Local Close Scope HP_scope.
Fixpoint cross {T U R : Type} (f : T -> U -> list R) (ls : list T) (rs : list U) : list R :=
      match ls with
      | List.nil => List.nil
      | l :: ls =>
        flat_map (f l) rs ++ cross f ls rs
      end.
    Lemma In_cross_In
      : forall {T U R : Type} f (ls : list T) (rs  : list U),
        forall x : R,
          List.In x (cross f ls rs) <->
          (exists l r, List.In l ls /\ List.In r rs /\ List.In x (f l r)).
    Proof.
      induction ls.
      { simpl. intros. split; intuition.
        destruct H. destruct H. destruct H. assumption. }
      { intros. simpl.
        rewrite in_app_iff.
        split.
        { intros.
          destruct H.
          { exists a; apply in_flat_map in H; inversion H; exists x0;
            intuition.
          }          
          { eapply IHls in H.
            repeat match goal with
                   | H : exists x , _ |- _ => destruct H
                   | H : _ /\ _ |- _ => destruct H
                   end.
            do 2 eexists; split; eauto. } }
        { intros.
          repeat destruct H. 
          { constructor; apply in_flat_map;
            exists x1; apply H0.
          }
          {
            constructor 2; apply IHls; exists x0; exists x1;
            intuition.
          }
        }
      }
    Qed.

Local Open Scope HP_scope.
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

    fold_right (
        fun triple2 curList => (simpleBoundFunc1 triple triple2 combFunc  (premise triple /\ 
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

Print cross.

Definition plusBound 
           (list1 list2: list singleBoundTerm) :
  list singleBoundTerm:= 
  cross combineTriplePlus list1 list2.
(*  (plusMinusfoldListwithList list1 list2 PlusT simpleBound simpleBound4).*)

Definition minusBound 
           (list1 list2: list singleBoundTerm): 
  list singleBoundTerm:=
  cross combineTripleMinus list1 list2.

Definition multBound 
           (list1 list2: list singleBoundTerm) :
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
                                 list singleBoundTerm) 
                     (bound_term_func : NowTerm ->
                                        list singleBoundTerm) :=  
  boundFunc (bound_term_func t1) (bound_term_func t2).

Fixpoint bound_term (x:NowTerm)  : (list singleBoundTerm):= 
  match x with
    | VarNowN var =>  [mkSBT (VarNowT var) (VarNowT var) TRUE]
    | NatN n =>  [mkSBT (RealT (INR n)) (RealT (INR n)) TRUE]
    | FloatN f => [mkSBT (RealT (B2R _ _ f)) (RealT (B2R _ _ f)) TRUE]
    | PlusN t1 t2 => cross combineTriplePlus (bound_term t1) (bound_term t2) 
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
Definition foldBoundProp (evalExpr:option Floats.float) (tr:trace) :=
  let s1 := Semantics.hd tr in
  let s2 := Semantics.hd (Semantics.tl tr) in
  match evalExpr with 
  | Some evalExpr =>  
    match floatToReal evalExpr with 
    | Some realEvalExpr => 
      (fun (triple:singleBoundTerm) (prop:Prop) =>
         (prop /\ 
          (eval_formula (premise triple) tr 
           -> eval_term (lb triple) s1 s2 <= 
              realEvalExpr <= 
              eval_term (ub triple) s1 s2)%R))
    | None => fun _ prop => prop
    end
  | None => fun _ prop => prop
  end.

Lemma fold_right_truth: forall lst, fold_right (fun (_ : singleBoundTerm) (prop : Prop) => prop) True lst = True. 
intros.
induction lst.  
* simpl.
  reflexivity.
* simpl.
  apply IHlst.
Qed.

Definition boundDef (expr:NowTerm) (tr:trace) (fState: fstate):Prop:=
  fold_right (foldBoundProp (eval_NowTerm fState expr) tr) True (bound_term expr).

Definition denote_singleBoundTerm (f : R) (tr : trace) (s : singleBoundTerm) : Prop :=
  let s1 := Semantics.hd tr in
  let s2 := Semantics.hd (Semantics.tl tr) in
  (eval_formula (premise s) tr
   -> eval_term (lb s) s1 s2 <= f <= eval_term (ub s) s1 s2)%R.

Definition boundDef' (expr:NowTerm) (tr:trace) (fState: fstate) : Prop :=
  match eval_NowTerm fState expr with
  | Some evalAsF =>
    match floatToReal evalAsF with
    | Some f =>
      List.Forall (denote_singleBoundTerm f tr) (bound_term expr)
    | None => True
    end
  | None => True
  end.




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

(*
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
*)

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
 Require Import compcert.flocq.Prop.Fprop_relative.
Print relative_error.


Lemma simpleTruth : true = true.
intuition.
Qed.             Lemma truth : true = true.
intuition.
Qed.

Lemma rltProof2 : forall r1 r2,  (r1 < r2)%R-> ( Rlt_bool r1 r2 = true). 
intros.
 unfold Rlt_bool in *.
                         Transparent Rcompare.
                         unfold Rcompare in *.
                         Transparent total_order_T.
                         destruct (total_order_T r1 r2).
                         destruct s.
                         intuition.
                         psatz R.
                         psatz R.
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

Definition related (f : fstate) (s : state) : Prop :=
  forall x y, fstate_lookup f x = Some y ->
              Some (s x) = floatToReal y.


Definition validFloat (f : Floats.float) : Prop :=
  exists r, Some r = floatToReal f.


Lemma resultImplicationsPlus : 
        forall (f : Floats.float) (expr1 expr2 : NowTerm) (fState : fstate),  
         (Some f =  lift2 (Bplus custom_prec custom_emax 
                                 eq_refl eq_refl Floats.Float.binop_pl mode_NE) 
                          (eval_NowTerm fState expr1)
                          (eval_NowTerm fState expr2)) ->
         validFloat f ->
         exists (f1 f2:Floats.float),
           Some f1 = eval_NowTerm fState expr1
           /\ Some f2 = eval_NowTerm fState expr2
           /\ validFloat f1 /\ validFloat f2.
  intros.
  unfold lift2 in H.
  remember (eval_NowTerm fState expr1) as evalExpr1.
  destruct evalExpr1.
  { exists f0. remember (eval_NowTerm fState expr2) as evalExpr2. destruct evalExpr2.
    { exists f1. intuition.
      unfold validFloat in *.
      destruct f0 eqn:f0_des.
      {
        simpl in *.
        exists R0.
        reflexivity.
      }
      {
        simpl in *.
        destruct f1.
        inversion H.
        rewrite H2 in H0.
        simpl in *.
        inversion H0.
        inversion H1.
        destruct Bool.eqb.
        inversion H.
        rewrite H2 in H0.
        inversion H0.
        simpl in *.
        inversion H1.
        inversion H.
        rewrite H2 in H0.
        simpl in *.
        inversion H0.
        inversion H1.
        inversion H.
        rewrite H2 in H0.
        inversion H0.
        simpl in *.
        inversion H1.
        inversion H.
        rewrite H2 in H0.
        inversion H0.
        inversion H1.
      }
      {
        destruct f1;
        inversion H;
        rewrite H2 in H0;
        inversion H0;
        simpl in *;
        inversion H1.
      }
      {
        simpl in *.
        remember (F2R {| Fnum := cond_Zopp b (Z.pos m); Fexp := e |}) as r.
        exists r.
        reflexivity.
      }
      {
        destruct f1 eqn:f0_des.
        {
          simpl in *.
          exists R0.
          reflexivity.
        }
        {
          simpl in *.
          destruct f0.
          inversion H.
          rewrite H2 in H0.
          simpl in *.
          inversion H0.
          inversion H1.
          simpl in *.
          destruct Bool.eqb.
          inversion H.
          rewrite H2 in H0.
          inversion H0.
          simpl in *.
          inversion H1.
          inversion H.
          rewrite H2 in H0.
          simpl in *.
          inversion H0.
          inversion H1.
          inversion H.
          rewrite H2 in H0.
          inversion H0.
          simpl in *.
          inversion H1.
          inversion H.
          rewrite H2 in H0.
          inversion H0.
          inversion H1.
        }
        {
          destruct f0;
          inversion H;
          rewrite H2 in H0;
          inversion H0;
          simpl in *;
          inversion H1.
        }
        {
          simpl in *.
          unfold validFloat.
          simpl in *.
          remember (F2R {| Fnum := cond_Zopp b (Z.pos m); Fexp := e |}) as r.
          exists r.
          reflexivity.
        } 
      }
    }
    {
      inversion H.
    }
  }
  {
   inversion H.
  }
Qed.

Lemma resultImplicationsMinus : 
        forall (f : Floats.float) (expr1 expr2 : NowTerm) (fState : fstate),  
         (Some f =  lift2 (Bminus custom_prec custom_emax 
                                 eq_refl eq_refl Floats.Float.binop_pl mode_NE) 
                          (eval_NowTerm fState expr1)
                          (eval_NowTerm fState expr2)) ->
         validFloat f ->
         exists (f1 f2:Floats.float),
           Some f1 = eval_NowTerm fState expr1
           /\ Some f2 = eval_NowTerm fState expr2
           /\ validFloat f1 /\ validFloat f2.
  intros.
  unfold lift2 in H.
  remember (eval_NowTerm fState expr1) as evalExpr1.
  destruct evalExpr1.
  { exists f0. remember (eval_NowTerm fState expr2) as evalExpr2. destruct evalExpr2.
    { exists f1. intuition.
      unfold validFloat in *.
      destruct f0 eqn:f0_des.
      {
        simpl in *.
        exists R0.
        reflexivity.
      }
      {
        simpl in *.
        destruct f1.
        inversion H.
        rewrite H2 in H0.
        simpl in *.
        inversion H0.
        inversion H1.
        simpl in *.
        destruct Bool.eqb.
        inversion H.
        rewrite H2 in H0.
        inversion H0.
        simpl in *.
        inversion H1.
        inversion H.
        rewrite H2 in H0.
        simpl in *.
        inversion H0.
        inversion H1.
        inversion H.
        rewrite H2 in H0.
        inversion H0.
        simpl in *.
        inversion H1.
        inversion H.
        rewrite H2 in H0.
        inversion H0.
        inversion H1.
      }
      {
        destruct f1;
        inversion H;
        rewrite H2 in H0;
        inversion H0;
        simpl in *;
        inversion H1.
      }
      {
        simpl in *.
        remember (F2R {| Fnum := cond_Zopp b (Z.pos m); Fexp := e |}) as r.
        exists r.
        reflexivity.
      }
      {
        destruct f1 eqn:f0_des.
        {
          simpl in *.
          exists R0.
          reflexivity.
        }
        {
          simpl in *.
          destruct f0.
          inversion H.
          rewrite H2 in H0.
          simpl in *.
          inversion H0.
          inversion H1.
          simpl in *.
          destruct Bool.eqb.
          inversion H.
          rewrite H2 in H0.
          inversion H0.
          simpl in *.
          inversion H1.
          inversion H.
          rewrite H2 in H0.
          simpl in *.
          inversion H0.
          inversion H1.
          inversion H.
          rewrite H2 in H0.
          inversion H0.
          simpl in *.
          inversion H1.
          inversion H.
          rewrite H2 in H0.
          inversion H0.
          inversion H1.
        }
        {
          destruct f0;
          inversion H;
          rewrite H2 in H0;
          inversion H0;
          simpl in *;
          inversion H1.
        }
        {
          simpl in *.
          unfold validFloat.
          simpl in *.
          remember (F2R {| Fnum := cond_Zopp b (Z.pos m); Fexp := e |}) as r.
          exists r.
          reflexivity.
        } 
      }
    }
    {
      inversion H.
    }
  }
  {
   inversion H.
  }
Qed.


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

Lemma validFloat2 : forall (f1:Floats.float) (r:R), Some r = floatToReal f1 -> r = B2R custom_prec custom_emax f1.   
intros.
unfold floatToReal in *.
destruct f1.
simpl in *.
inversion H.
reflexivity.
inversion H.
inversion H.
inversion H.
simpl in *.
reflexivity.
Qed.
Definition custom_emin := (-1021)%Z.


Definition choiceDef := (fun x => negb (Zeven x)).

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

 Lemma floatValid : forall (r:R) (f:Floats.float), Some r = floatToReal f -> is_finite _ _ f = true .
      Proof.
        intros.
        unfold floatToReal in *.
        destruct f. 
        {
          simpl in *.
          reflexivity.
        }
        {
          inversion H.
        }
        {
          inversion H.
        }
        {
          simpl in *.
          reflexivity.
        }
      Qed.  






Axiom errorGt0 : (error > 0)%R.
Lemma absoluteValGe : forall (r1 r2:R) , 
                (Rabs r1 >= r2 -> r1 >= r2 \/ -r1 >= r2)%R. 
            Proof.
              intros.
              unfold Rabs in *.
              destruct Rcase_abs; psatz R.
            Qed.
Lemma absoluteValLt : forall (r1 r2:R) , 
                (Rabs r1 < r2 -> r1 < r2 \/ -r1 < r2)%R. 
Proof.
  intros.
  unfold Rabs in *.
  destruct Rcase_abs; psatz R.
Qed.



Axiom floatMinGt0 : (floatMin > 0)%R.
Axiom floatMaxGt0 : (floatMax > 0)%R.


Declare ML Module "z3Tactic".


Lemma minusfloatMinBoundProof:  forall (x1 x2 lb1 lb2 ub1 ub2:R), 
( ((lb1 >= ub2) /\ (floatMin <= lb1 - ub2)) \/ ( (ub1 <= lb2) /\(floatMin <= lb2 - ub1)) -> lb1 <= x1 -> lb2 <= x2 -> x1 <= ub1 -> x2 <= ub2 -> (Rabs (x1 - x2) >= floatMin))%R. 
Proof.
intros.
pose proof floatMinGt0.
unfold Rabs.  
destruct Rcase_abs.
destruct H.
psatz R.
decompose [and] H.
 repeat match goal with
          | H : @eq R _ _ |- _ => revert H
          | H : @Rle _ _ |- _ => revert H
          | H : @Rge _ _ |- _ => revert H
          | H : @Rlt _ _ |- _ => revert H
          | H :@ Rgt _ _ |- _ => revert H
          | H : @Rge _ _ |- _ => revert H
        end.
(*z3Tactic*)
psatz R.

destruct H.
decompose [and] H.
psatz R.

psatz R.
Qed.
Lemma plusfloatMinBoundProof:  forall (x1 x2 lb1 lb2 ub1 ub2:R), ((floatMin <= lb1 + lb2) \/ (floatMin <= 0 - ub1 + (0 - ub2)) -> lb1 <= x1 -> lb2 <= x2 -> x1 <= ub1 -> x2 <= ub2 -> (Rabs (x1 + x2) >= floatMin))%R. 
Proof.
  intros.
  pose proof floatMinGt0.
  unfold Rabs.
  destruct Rcase_abs. destruct H.
 psatz R.
 repeat match goal with
          | H : @eq R _ _ |- _ => revert H
          | H : @Rle _ _ |- _ => revert H
          | H : @Rge _ _ |- _ => revert H
          | H : @Rlt _ _ |- _ => revert H
          | H :@ Rgt _ _ |- _ => revert H
          | H : @Rge _ _ |- _ => revert H
        end.
(*z3Tactic*)
psatz R.


destruct H.
psatz R.

psatz R.
Qed.

Lemma lbAndUbSumIsZero : forall (lb1 lb2 ub1 ub2 x1 x2: R), ((lb1 + lb2)%R = 0%R /\ (ub1 + ub2)%R = 0%R) ->  (lb1 <= x1 <= ub1)%R ->  (lb2 <= x2 <= ub2)%R -> (x1 + x2 = 0)%R.
Proof.
  intros.
  decompose [and] H.
  destruct H0.
  destruct H1.
  clear H.
  psatz R.
Qed.


Lemma relErrorBasedOnFloatMinTruthMinus : forall (x1 x2 lb1 lb2 ub1 ub2:R), 
(((lb1 >= ub2)  /\  (floatMin <= lb1 - ub2)) 
\/ ((ub1 <= lb2) /\(floatMin <= lb2 - ub1)) -> 
lb1 <= x1 -> lb2 <= x2 -> x1 <= ub1 -> x2 <= ub2 ->  
(Rabs (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (x1 - x2) - (x1 - x2)) < 
 bpow radix2 (- custom_prec + 1) * Rabs (x1 - x2)))%R.
intros.
 intros.
  pose proof relative_error as Rel_Err.
  remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp.
  specialize (Rel_Err radix2 round_fexp).
  subst.
  specialize (Rel_Err validFexpProof (custom_emin)%Z custom_prec  precThm (round_mode mode_NE)). 
  specialize (Rel_Err (valid_rnd_N choiceDef)).
  pose proof minusfloatMinBoundProof as minusfloatMinBoundProof.
  specialize (minusfloatMinBoundProof x1 x2 lb1 lb2 ub1 ub2).
  specialize (minusfloatMinBoundProof H H0 H1 H2 H3).
  specialize (Rel_Err (x1-x2)%R).
  unfold floatMin in *.
  apply Rge_le in minusfloatMinBoundProof.
  specialize (Rel_Err minusfloatMinBoundProof).
  apply Rel_Err.
Qed.




Lemma relErrorBasedOnFloatMinTruthPlus : forall (x1 x2 lb1 lb2 ub1 ub2:R), 
((floatMin <= lb1 + lb2) \/ (floatMin <= 0 - ub1 + (0 - ub2)) -> lb1 <= x1 -> lb2 <= x2 -> x1 <= ub1 -> x2 <= ub2 ->  (Rabs (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (x1 + x2) - (x1 + x2)) < bpow radix2 (- custom_prec + 1) * Rabs (x1 + x2)))%R.
Proof.
  intros.
  pose proof relative_error as Rel_Err.
  remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp.
  specialize (Rel_Err radix2 round_fexp).
  subst.
  specialize (Rel_Err validFexpProof (custom_emin)%Z custom_prec  precThm (round_mode mode_NE)). 
  specialize (Rel_Err (valid_rnd_N choiceDef)).
  pose proof plusfloatMinBoundProof as plusfloatMinBoundProof.
  specialize (plusfloatMinBoundProof x1 x2 lb1 lb2 ub1 ub2).
  specialize (plusfloatMinBoundProof H H0 H1 H2 H3).
  specialize (Rel_Err (x1+x2)%R).
  unfold floatMin in *.
  apply Rge_le in plusfloatMinBoundProof.
  specialize (Rel_Err plusfloatMinBoundProof).
  apply Rel_Err.
Qed.


Lemma minusRoundingTruth : forall (f1 f2: Floats.float)  (lb1 lb2 ub1 ub2 r1 r2:R),  (Some r1 = (floatToReal f1) -> 
    Some r2 = (floatToReal f2) ->
  ( (((lb1 >= ub2)  /\  (floatMin <= lb1 - ub2)) /\  ((ub1 - lb2)*(1+error) < floatMax)) \/ 
   (((ub1 <= lb2)  /\  (floatMin <= lb2 - ub1)) /\  ((ub2 - lb1)*(1+error) < floatMax))) ->
    (lb1 <= r1) ->
    (lb2 <= r2) ->
     (r1 <= ub1) ->
     (r2 <= ub2) ->    
((Rabs (round radix2 (FLT_exp (3-custom_emax- custom_prec) custom_prec ) (round_mode mode_NE) (B2R custom_prec custom_emax f1 - B2R custom_prec custom_emax f2))) 
 <  (bpow radix2 custom_emax)))%R. 
Proof.   
intros.
unfold floatToReal in *.
destruct f1.
{
  destruct f2. 
  {
    inversion H.
  inversion H0.
  pose proof relErrorBasedOnFloatMinTruthMinus.
  Lemma andOrProof : forall (p1 p2 p3 p4 p5 p6:Prop), 
      ((p1 /\ p2) /\ p3) \/ ((p4 /\ p5) /\ p6) -> (p1 /\ p2 ) \/ (p4 /\ p5).
    intros.
    intuition.
  Qed.
  intros.
  assert (H1':=H1).
  apply andOrProof in H1.
  specialize (H6 r1 r2 lb1 lb2 ub1 ub2 H1 H2 H3 H4 H5).
  unfold B2R.
  unfold Rabs in *.
  pose proof errorGt0 as errorGt0.
  rewrite H7 in H6.
  rewrite H8 in H6.
  remember  (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) 
             (round_mode mode_NE) (0 - 0)) as roundedValue.
  clear HeqroundedValue.
  clear H7 H8.
  clear H H0.
pose proof floatMaxGt0.
Axiom floatMaxGtError : (floatMax > error)%R.
pose proof floatMaxGtError.
pose proof floatMinGt0.
clear H1.

destruct Rcase_abs;destruct Rcase_abs;destruct Rcase_abs;
                                               repeat match goal with
                                                        | H : @eq R _ _ |- _ => revert H
                                                        | H : @Rle _ _ |- _ => revert H
                                                        | H : @Rge _ _ |- _ => revert H
                                                        | H : @Rlt _ _ |- _ => revert H
                                                        | H :@ Rgt _ _ |- _ => revert H
                                                        | H : @Rge _ _ |- _ => revert H
                                                      end;
unfold error;
unfold floatMax;
psatz R.
    
  }
  inversion H0.
  inversion H0.
  inversion H.
  inversion H0.
  pose proof relErrorBasedOnFloatMinTruthMinus.
  assert (H1':=H1).
  apply andOrProof in H1.
  specialize (H6 r1 r2 lb1 lb2 ub1 ub2 H1 H2 H3 H4 H5).
  unfold B2R.
  rewrite <- H7.
  unfold Rabs in *.
  pose proof errorGt0 as errorGt0.
  rewrite <- H8.
  remember  (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) 
             (round_mode mode_NE) (r1 - r2)) as roundedValue.
  clear HeqroundedValue.
  clear H8.
  clear H H0.
pose proof floatMaxGt0.
pose proof floatMaxGtError.
pose proof floatMinGt0.
Axiom errorLessThan1 : (error < 1)%R.
pose proof errorLessThan1.
clear H7.

destruct Rcase_abs. 
{
  destruct Rcase_abs. 
  {
    destruct Rcase_abs. 

    {
      destruct H1'.
      {
        decompose [and] H7.

        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end;
          unfold error.

        unfold floatMax.
        psatz R.
      }
      {
        decompose [and] H7.
        clear H7 H12.
        clear H8.
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        psatz R.  
      }
    }
    {
        destruct H1'.
        {
          clear H7.
          clear H8.
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          unfold error.
          unfold floatMax.
          psatz R.
        }
        {
          
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          unfold error.
          unfold floatMax.
          psatz R.
        }
    }
  }
  {      
    destruct Rcase_abs. 

    {
      destruct H1'.
      {
        decompose [and] H7.
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        psatz R.
      }
      {
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        psatz R.
      }
    }
    {
      destruct H1'.
      {
        decompose [and] H7.
        clear H8 H1 H7 H12 .
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        psatz R.
        
      }
      {
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        psatz R.
      }
    }
  }   
}
{
  destruct Rcase_abs. 
  {
    destruct Rcase_abs. 

    {
      destruct H1'.
      {
        decompose [and] H7.
        
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end;
          unfold error.
        unfold floatMax.
        psatz R.
      }
      {
        decompose [and] H7.
        
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end;
          unfold error.
        unfold floatMax.
        psatz R.
      }
    }
    {
      
      repeat match goal with
               | H : @eq R _ _ |- _ => revert H
               | H : @Rle _ _ |- _ => revert H
               | H : @Rge _ _ |- _ => revert H
               | H : @Rlt _ _ |- _ => revert H
               | H :@ Rgt _ _ |- _ => revert H
               | H : @Rge _ _ |- _ => revert H
             end;
      unfold error.
      unfold floatMax.
      psatz R.
    }
  }
  {
    destruct Rcase_abs.
    {
      repeat match goal with
               | H : @eq R _ _ |- _ => revert H
               | H : @Rle _ _ |- _ => revert H
               | H : @Rge _ _ |- _ => revert H
               | H : @Rlt _ _ |- _ => revert H
               | H :@ Rgt _ _ |- _ => revert H
               | H : @Rge _ _ |- _ => revert H
             end;
      unfold error.
      unfold floatMax.
      psatz R.
    }
    {
      destruct  H1'.
      {
        destruct H1.
        {
          decompose [and] H7.
          clear H1 H8.
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end;
            unfold error.
          unfold floatMax.
          psatz R.
        }
        {
          decompose [and] H7.
          clear H1 H8.
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end;
            unfold error.
          unfold floatMax.
          psatz R.
        }
      }
      {
        decompose [and] H7.
        clear H1 H8.
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end;
          unfold error.
        unfold floatMax.
        psatz R.
      }
    }
  }
}
}
{
  inversion H.
}
{
  inversion H.
}

 destruct f2.
{
  

  inversion H.
  unfold custom_emax,custom_prec  in *.
  remember ((B2R 53 1024 (B754_zero 53 1024 b0))) as arg2.
  inversion H0.
  rewrite H8 in *.
  pose proof relErrorBasedOnFloatMinTruthMinus.
  assert (H1':=H1).
  apply andOrProof in H1.
  specialize (H6 r1 arg2 lb1 lb2 ub1 ub2 H1 H2 H3 H4 H5).
  unfold B2R.
  rewrite <- H7.
  unfold Rabs in *.
  unfold custom_prec,custom_emax in *.
  pose proof errorGt0 as errorGt0.
  remember  (round radix2 (FLT_exp (3 - 1024 - 53) 53) 
             (round_mode mode_NE) (r1 - arg2)) as roundedValue.
  clear HeqroundedValue.
  
pose proof floatMaxGt0.
pose proof floatMaxGtError.
pose proof floatMinGt0.
pose proof errorLessThan1.
clear H Heqarg2 H0 H8 H7 H11.
unfold error in *.
unfold custom_prec,custom_emax in *.
destruct Rcase_abs. 
{
  destruct Rcase_abs. 
  {
    destruct Rcase_abs. 

    {
      destruct H1'.
      {
        decompose [and] H.
        clear H H11.
        clear H6 H9 errorGt0 H9 H10 H12 r3 H7 r.
        clear H1.
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.

        unfold floatMax.
        unfold custom_prec,custom_emax in *.
        psatz R.
      }


       {
         decompose [and] H.
         clear H.
         clear H1 H11.
         clear r0 r errorGt0 H9 H10 H12.
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        unfold custom_prec,custom_emax in *.
        (*z3Tactic*)
        admit.
      }
    }
    {
        destruct H1'.
        {
          
          
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          unfold error.
          unfold floatMax.
          unfold custom_prec,custom_emax in *.
          (*z3Tactic*)
          admit.
        }
        {
          
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          unfold error.
          unfold floatMax.
          unfold custom_prec,custom_emax in *.
          (*z3Tactic*)
          admit.
        }
    }
  }
  {      
    destruct Rcase_abs. 

    {
      destruct H1'.
      {
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        unfold custom_prec,custom_emax in *.
        (*z3Tactic*)
        admit.
      }
      {
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        unfold custom_prec,custom_emax in *.
        (*z3Tactic*)
        admit.
      }
    }
    {
      destruct H1'.
      {
        decompose [and]  H.
        clear H11 H10.
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        unfold custom_prec,custom_emax in *.
        (*z3Tactic*)
        admit.
      }
      {
        decompose [and]  H.
        clear H11 H10.
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        unfold custom_prec,custom_emax in *.
        (*z3Tactic*)
        admit.
      }
    }
  }   
}
{
  destruct Rcase_abs. 
  {
    destruct Rcase_abs. 
     {
       destruct H1'.
       {
         decompose [and] H.
         clear H11 H10.
         repeat match goal with
                  | H : @eq R _ _ |- _ => revert H
                  | H : @Rle _ _ |- _ => revert H
                  | H : @Rge _ _ |- _ => revert H
                  | H : @Rlt _ _ |- _ => revert H
                  | H :@ Rgt _ _ |- _ => revert H
                  | H : @Rge _ _ |- _ => revert H
                end.
         unfold error.
         unfold floatMax.
         unfold custom_prec,custom_emax in *.
         (*z3Tactic*)
         admit.
       }
       {
         decompose [and] H.
         clear H11 H10.
         repeat match goal with
                  | H : @eq R _ _ |- _ => revert H
                  | H : @Rle _ _ |- _ => revert H
                  | H : @Rge _ _ |- _ => revert H
                  | H : @Rlt _ _ |- _ => revert H
                  | H :@ Rgt _ _ |- _ => revert H
                  | H : @Rge _ _ |- _ => revert H
                end.
         unfold error.
         unfold floatMax.
         unfold custom_prec,custom_emax in *.
         (*z3Tactic*)
         admit.
       }
     }
     {
       {
         destruct H1'.
         {
           decompose [and] H.
           clear H11 H10.
           repeat match goal with
                    | H : @eq R _ _ |- _ => revert H
                    | H : @Rle _ _ |- _ => revert H
                    | H : @Rge _ _ |- _ => revert H
                    | H : @Rlt _ _ |- _ => revert H
                    | H :@ Rgt _ _ |- _ => revert H
                    | H : @Rge _ _ |- _ => revert H
                  end.
           unfold error.
           unfold floatMax.
           unfold custom_prec,custom_emax in *.
           (*z3Tactic*)
           admit.
         }
         {
            decompose [and] H.
           clear H11 H10.
           repeat match goal with
                    | H : @eq R _ _ |- _ => revert H
                    | H : @Rle _ _ |- _ => revert H
                    | H : @Rge _ _ |- _ => revert H
                    | H : @Rlt _ _ |- _ => revert H
                    | H :@ Rgt _ _ |- _ => revert H
                    | H : @Rge _ _ |- _ => revert H
                  end.
           unfold error.
           unfold floatMax.
           unfold custom_prec,custom_emax in *.
           (*z3Tactic*)
           admit.
         }
       }
     }
  }
  {
    destruct Rcase_abs.
    {
      destruct H1'.
      {
        decompose [and] H1.
        clear H12 H10.
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        unfold custom_prec,custom_emax in *.
        (*z3Tactic*)
        admit.
      }
      {
        decompose [and] H1.
        clear H12 H10.
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        unfold custom_prec,custom_emax in *.
        (*z3Tactic*)
        admit.
      }
    }
    {
       destruct H1'.
      {
        decompose [and] H1.
        clear H12 H10.
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        unfold custom_prec,custom_emax in *.
        (*z3Tactic*)
        admit.
      }
      {
        decompose [and] H1.
        clear H12 H10.
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end.
        unfold error.
        unfold floatMax.
        unfold custom_prec,custom_emax in *.
        (*z3Tactic*)
        admit.
      }
    }
  }
}
}
{
  inversion H0.
}
{
  inversion H0.
}
{
  pose proof relErrorBasedOnFloatMinTruthMinus.
  assert (H1':=H1).
  apply andOrProof in H1.
  specialize (H6 r1 r2 lb1 lb2 ub1 ub2 H1 H2 H3 H4 H5).
  inversion H as [r1Value].
  inversion H0 as [r2Value].
  unfold B2R.
  rewrite <- r1Value.
  rewrite <- r2Value.
  unfold Rabs in *.
  pose proof errorGt0 as errorGt0.
  remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                  (round_mode mode_NE) (r1 - r2)) as roundedValue.
  clear HeqroundedValue.
  clear H H0.
  pose proof floatMaxGt0.
  pose proof floatMaxGtError.
  pose proof floatMinGt0.
  pose proof errorLessThan1.
  clear H7.
  clear r1Value.
  clear r2Value.
  destruct Rcase_abs.
  {
    destruct Rcase_abs.
    {
      destruct Rcase_abs.
      {
        destruct H1'.
        {
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end;
            unfold error.
          unfold floatMax.
          admit.
        }
        {
          decompose [and] H7.
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          unfold error.
          unfold floatMax.
          admit.
        }
      }
      {
        destruct H1'.
        {
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          unfold error.
          unfold floatMax.
          admit.
        }
        {
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          unfold error.
          unfold floatMax.
          admit.
        }
      }
    }
    {
      destruct Rcase_abs.
      {
        destruct H1'.
        {
          decompose [and] H7.
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          unfold error.
          unfold floatMax.
          admit.
        }
        {
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          unfold error.
          unfold floatMax.
          admit.
        }
      }
      {
        destruct H1'.
        {
          decompose [and] H7.
          clear H8 H1 H7 H12 .
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          unfold error.
          unfold floatMax.
          admit.
        }
        {
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          unfold error.
          unfold floatMax.
          admit.
        }
      }
    }
  }
  {
    destruct Rcase_abs.
    {
      destruct Rcase_abs.
      {
        destruct H1'.
        {
          decompose [and] H7.
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end;
            unfold error.
          unfold floatMax.
          admit.
        }
        {
          decompose [and] H7.
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end;
            unfold error.
          unfold floatMax.
          admit.
        }
      }
      {
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end;
        unfold error.
        unfold floatMax.
        admit.
      }
    }
    {
      destruct Rcase_abs.
      {
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end;
        unfold error.
        unfold floatMax.
        admit.
      }
      {
        destruct H1'.
        {
          destruct H1.
          {
            decompose [and] H7.
            clear H1 H8.
            repeat match goal with
                     | H : @eq R _ _ |- _ => revert H
                     | H : @Rle _ _ |- _ => revert H
                     | H : @Rge _ _ |- _ => revert H
                     | H : @Rlt _ _ |- _ => revert H
                     | H :@ Rgt _ _ |- _ => revert H
                     | H : @Rge _ _ |- _ => revert H
                   end;
              unfold error.
            unfold floatMax.
            admit.
          }
          {
            decompose [and] H7.
            clear H1 H8.
            repeat match goal with
                     | H : @eq R _ _ |- _ => revert H
                     | H : @Rle _ _ |- _ => revert H
                     | H : @Rge _ _ |- _ => revert H
                     | H : @Rlt _ _ |- _ => revert H
                     | H :@ Rgt _ _ |- _ => revert H
                     | H : @Rge _ _ |- _ => revert H
                   end;
              unfold error.
            unfold floatMax.
            admit.
          }
        }
        {
          decompose [and] H7.
          clear H1 H8.
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end;
            unfold error.
          unfold floatMax.
          admit.
        }
      }
    }
  }
}

Qed.  


Lemma plusRoundingTruth : forall (f1 f2: Floats.float)  (lb1 lb2 ub1 ub2 r1 r2:R), 
   
   (Some r1 = (floatToReal f1) -> 
    Some r2 = (floatToReal f2) ->
    (floatMin <= lb1 + lb2) \/ (floatMin <= 0 - ub1 + (0 - ub2)) ->
    (lb1 <= r1) ->
    (lb2 <= r2) ->
    ((ub1 + ub2)*(1+error ) < floatMax) 
    -> ((0 - lb1 + (0 - lb2))* (1+error)) < floatMax ->
     (r1 <= ub1) ->
     (r2 <= ub2) ->    
((Rabs (round radix2 (FLT_exp (3-custom_emax- custom_prec) custom_prec ) (round_mode mode_NE) (B2R custom_prec custom_emax f1 + B2R custom_prec custom_emax f2))) 
 <  (bpow radix2 custom_emax)))%R.
intros.
unfold floatToReal in *.
destruct f1.
{
  destruct f2. 
  {
    inversion H.
  inversion H0.
  Check relErrorBasedOnFloatMinTruthPlus.
  pose proof relErrorBasedOnFloatMinTruthPlus.
  specialize (H8 r1 r2 lb1 lb2 ub1 ub2).  
  specialize (H8 H1 H2 H3 H6 H7 ).
  unfold B2R.
  unfold Rabs in *.
  pose proof errorGt0 as errorGt0.
  rewrite H9 in H8.
  rewrite H10 in H8.
  remember  (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) 
             (round_mode mode_NE) (0 + 0)) as roundedValue.
  clear HeqroundedValue.
  clear H9 H10.
  clear H H0.
pose proof floatMaxGt0.
pose proof floatMaxGtError.
pose proof floatMinGt0.
clear H1.

destruct Rcase_abs;destruct Rcase_abs;destruct Rcase_abs;
                                               repeat match goal with
                                                        | H : @eq R _ _ |- _ => revert H
                                                        | H : @Rle _ _ |- _ => revert H
                                                        | H : @Rge _ _ |- _ => revert H
                                                        | H : @Rlt _ _ |- _ => revert H
                                                        | H :@ Rgt _ _ |- _ => revert H
                                                        | H : @Rge _ _ |- _ => revert H
                                                      end;
unfold error;
unfold floatMax;
psatz R.
    
  }
  inversion H0.
  inversion H0.
  inversion H.
  inversion H0.
  Check relErrorBasedOnFloatMinTruthPlus.
  pose proof relErrorBasedOnFloatMinTruthPlus.
  specialize (H8 r1 r2 lb1 lb2 ub1 ub2).  
  specialize (H8 H1 H2 H3 H6 H7 ).
  unfold B2R.
  rewrite <- H9.
  unfold Rabs in *.
  pose proof errorGt0 as errorGt0.
  rewrite <- H10.
  remember  (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) 
             (round_mode mode_NE) (r1 + r2)) as roundedValue.
  clear HeqroundedValue.
  clear H10.
  clear H H0.
pose proof floatMaxGt0.
pose proof floatMaxGtError.
pose proof floatMinGt0.
clear H1.
clear H9.

destruct Rcase_abs; destruct Rcase_abs; destruct Rcase_abs;



                                               repeat match goal with
                                                        | H : @eq R _ _ |- _ => revert H
                                                        | H : @Rle _ _ |- _ => revert H
                                                        | H : @Rge _ _ |- _ => revert H
                                                        | H : @Rlt _ _ |- _ => revert H
                                                        | H :@ Rgt _ _ |- _ => revert H
                                                        | H : @Rge _ _ |- _ => revert H
                                                      end;
unfold error;
unfold floatMax;
psatz R.


    
  }
inversion H0.
inversion H.
inversion H.

  
 
  destruct f2.
  

  inversion H.
  inversion H0.
  Check relErrorBasedOnFloatMinTruthPlus.
  pose proof relErrorBasedOnFloatMinTruthPlus.
  specialize (H8 r1 r2 lb1 lb2 ub1 ub2).  
  specialize (H8 H1 H2 H3 H6 H7 ).
  unfold B2R.
  rewrite <- H9.
  rewrite <- H10.
  unfold Rabs in *.
  pose proof errorGt0 as errorGt0.
  unfold error in *.
  remember  (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) 
             (round_mode mode_NE) (r1 + r2)) as roundedValue.
  clear HeqroundedValue.
  clear H9 H10.
  clear H H0.
pose proof floatMaxGt0.
pose proof floatMaxGtError.
pose proof floatMinGt0.
clear H1.
destruct Rcase_abs; destruct Rcase_abs; destruct Rcase_abs;
                                               repeat match goal with
                                                        | H : @eq R _ _ |- _ => revert H
                                                        | H : @Rle _ _ |- _ => revert H
                                                        | H : @Rge _ _ |- _ => revert H
                                                        | H : @Rlt _ _ |- _ => revert H
                                                        | H :@ Rgt _ _ |- _ => revert H
                                                        | H : @Rge _ _ |- _ => revert H
                                                      end;
unfold error;
unfold floatMax;
psatz R.

inversion H0.
inversion H0.

 inversion H.
  inversion H0.
  Check relErrorBasedOnFloatMinTruthPlus.
  pose proof relErrorBasedOnFloatMinTruthPlus.
  specialize (H8 r1 r2 lb1 lb2 ub1 ub2).  
  specialize (H8 H1 H2 H3 H6 H7 ).
  unfold B2R.
  rewrite <- H9.
  rewrite <- H10.
  unfold Rabs in *.
  pose proof errorGt0 as errorGt0.
  unfold error in *.
  remember  (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) 
             (round_mode mode_NE) (r1 + r2)) as roundedValue.
  clear HeqroundedValue.
  clear H9 H10.
  clear H H0.
pose proof floatMaxGt0.
pose proof floatMaxGtError.
pose proof floatMinGt0.
clear H1.
destruct Rcase_abs; destruct Rcase_abs; destruct Rcase_abs;
                                               repeat match goal with
                                                        | H : @eq R _ _ |- _ => revert H
                                                        | H : @Rle _ _ |- _ => revert H
                                                        | H : @Rge _ _ |- _ => revert H
                                                        | H : @Rlt _ _ |- _ => revert H
                                                        | H :@ Rgt _ _ |- _ => revert H
                                                        | H : @Rge _ _ |- _ => revert H
                                                      end;
unfold error;
unfold floatMax;
psatz R.
Qed.
    

Lemma plusRoundingTruth2 : forall (f1 f2: Floats.float)  (r1 r2:R) , 
    Some r1 = floatToReal f1 -> 

    Some r2 = floatToReal f2 ->

    ((Rabs (round radix2 (FLT_exp (3-custom_emax- custom_prec) custom_prec ) (round_mode mode_NE) (B2R custom_prec custom_emax f1 + B2R custom_prec custom_emax f2))) <  (bpow radix2 custom_emax))%R  ->
 
     (B2R custom_prec custom_emax (Bplus custom_prec custom_emax  eq_refl eq_refl Floats.Float.binop_pl mode_NE f1 f2) =round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (B2R custom_prec custom_emax f1 + B2R custom_prec custom_emax f2)  /\   is_finite custom_prec custom_emax (Bplus custom_prec custom_emax eq_refl eq_refl  Floats.Float.binop_pl mode_NE f1 f2) = true)%R. 
Proof.
  intros.
  pose proof Bplus_correct.
  specialize (H2 custom_prec custom_emax).
  specialize (H2 eq_refl eq_refl Floats.Float.binop_pl ).
  specialize (H2  mode_NE).
  specialize (H2 f1 f2).
  Print floatValid.
  apply floatValid in H.
  apply floatValid in H0.
  specialize (H2 H H0).
  apply rltProof2 in H1.
  rewrite H1 in H2.
  decompose [and] H2.
  split.
  apply H2. 
apply H5.

Qed.
Print Bminus_correct.
Lemma minusRoundingTruth2 : forall (f1 f2: Floats.float)  (r1 r2:R) ,  Some r1 = (floatToReal f1) -> 
                                                                        Some r2 = (floatToReal f2) ->   
    
    ((Rabs (round radix2 (FLT_exp (3-custom_emax- custom_prec) custom_prec ) (round_mode mode_NE) (B2R custom_prec custom_emax f1 - B2R custom_prec custom_emax f2))) 
 <  (bpow radix2 custom_emax))%R -> 
                                                                        (B2R custom_prec custom_emax (Bminus custom_prec custom_emax  eq_refl eq_refl Floats.Float.binop_pl mode_NE f1 f2) =round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (B2R custom_prec custom_emax f1 - B2R custom_prec custom_emax f2)  /\   is_finite custom_prec custom_emax (Bminus custom_prec custom_emax eq_refl eq_refl  Floats.Float.binop_pl mode_NE f1 f2) = true)%R.
 
Proof.
  intros.
  pose proof Bminus_correct.
  specialize (H2 custom_prec custom_emax).
  specialize (H2 eq_refl eq_refl Floats.Float.binop_pl ).
  specialize (H2  mode_NE).
  specialize (H2 f1 f2).
  Print floatValid.
  apply floatValid in H.
  apply floatValid in H0.
  specialize (H2 H H0).
  apply rltProof2 in H1.
  rewrite H1 in H2.
  decompose [and] H2.
  split.
  apply H2. 
apply H5.
Qed.

Lemma bound_proof' : 
  forall (tr:Semantics.trace) (expr:NowTerm) (fState:fstate),
    related fState (Semantics.hd tr) -> 
    boundDef' expr tr fState.
Proof.
  unfold boundDef'.
  intros.
  remember (eval_NowTerm fState expr). destruct o; trivial.
  remember (floatToReal f). destruct o; trivial.
  revert Heqo. revert Heqo0. revert f. revert r.
  induction expr.
  { simpl. constructor; [ | constructor ].
    red. simpl. intros XXX; clear XXX.
    simpl in Heqo.
    red in H. symmetry in Heqo.
    apply H in Heqo.
    rewrite <- Heqo in *.
    inversion Heqo0.
    subst. constructor; psatz R. }
  { simpl. constructor; [ | constructor ].
    red. simpl. intros XXX; clear XXX.
    simpl in Heqo. inversion Heqo. subst.
    clear Heqo.
    admit. (** interesting lemma **) }
  { simpl. constructor; [ | constructor ].
    red. simpl. intro XXX; clear XXX.
    simpl in Heqo.
    inversion Heqo. subst.
    unfold floatToReal in Heqo0.
    destruct f; simpl; inversion Heqo0; intuition.
  }
  { simpl.   unfold getBound. unfold plusBound.
    intros.
    Print plusMinusfoldListwithList.
    assert (Heqo':=Heqo).
    apply resultImplicationsPlus in Heqo.
    Require Import ExtLib.Tactics.
    forward_reason. destruct H2; destruct H3.
    specialize (IHexpr1 _ _ H2 H0).
    specialize (IHexpr2 _ _ H3 H1).
    2: eexists; eauto.
    eapply Forall_forall. intros.
    eapply In_cross_In in H4.
    forward_reason.
    eapply Forall_forall in IHexpr1; eauto.
    eapply Forall_forall in IHexpr2; eauto.
    
    inversion Heqo'.
    unfold lift2 in Heqo'.
    rewrite <- H0 in Heqo'.
    rewrite <- H1 in Heqo'.
    inversion Heqo'.
    unfold floatToReal in Heqo0.
    rewrite H9 in Heqo0.
    unfold floatToReal in Heqo0.
    destruct f eqn:f_des.
    {
      rewrite <- H9 in Heqo0.
      inversion Heqo0.
      assert (plusResultStmt := H9).
      assert (floatToRealRelationForExpr1:= H2).
      assert (floatToRealRelationForExpr2:= H3).
      clear H f Heqo0 H0 H1 H8 f_des Heqo' H9 H10 .
      assert (floatToRealProof1:= H2).
      assert (floatToRealProof2:= H3).
      clear H2 H3.
      
      
      unfold denote_singleBoundTerm in *.
      intros.
      simpl in H6.
      unfold simpleBound in *.
      unfold simpleBound4 in *.
      destruct H6.
      
      {
        rewrite <- H0 in H.
        simpl in H.
        rewrite <- H0.
        decompose [and] H.
        apply IHexpr1 in H1.
        apply IHexpr2 in H3.
        assert (expr1Bound := H1).
        assert (expr2Bound := H3).
        assert (floatMinCase := H2).
        assert (floatMaxBound1 := H6). 
        assert (floatMaxBound2 := H7).
        assert (resultGe0 := H9).
        clear H4 H2 H1 H3 H H5 H7 H0 H9 H6 IHexpr1 IHexpr2.
        unfold Semantics.eval_comp in *.
        simpl in floatMinCase.
        simpl in expr1Bound.
        simpl in expr2Bound.
        simpl in floatMaxBound2.
        simpl in floatMaxBound1.
        simpl in resultGe0.
        simpl.
        remember (eval_term (lb x4) (hd tr) (hd (tl tr))) as lb1.
        remember (eval_term (lb x5) (hd tr) (hd (tl tr))) as lb2.
        remember (eval_term (ub x5) (hd tr) (hd (tl tr))) as ub2.
        remember (eval_term (ub x4) (hd tr) (hd (tl tr))) as ub1.
        clear Hequb1 Hequb2 Heqlb1 Heqlb2.
        pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
        specialize (relErrorBasedOnFloatMinTruthPlus x1 x2 lb1 lb2 ub1 ub2).
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        
        intros.
        specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H H1 H0 H2).
        pose proof plusRoundingTruth as plusRoundingTruth.
        specialize (plusRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 floatMinCase H H1 floatMaxBound1 floatMaxBound2 H0 H2).
        pose proof plusRoundingTruth2 as plusRoundingTruth2.
        specialize (plusRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 plusRoundingTruth).
        revert plusResultStmt. intros plusResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
        
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x +
                          B2R custom_prec custom_emax x0)) as roundedValue. 

        simpl in plusRoundingTruth2.
        simpl in plusResultStmt.
        rewrite <- plusResultStmt in plusRoundingTruth2.
        simpl in plusRoundingTruth2.
        decompose [and] plusRoundingTruth2.
        rewrite  H4.
        clear H5.
        clear plusRoundingTruth2.
        assert (plusRoundingTruth2:= H4).
        clear H4.
        clear plusResultStmt.
        clear H3.
        clear plusRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
        rewrite <- floatToRealProof2  in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.

        pose proof errorGt0.
        clear floatMinCase floatMaxBound1 floatMaxBound2 HeqroundedValue 
              plusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
        pose proof errorLessThan1.
        unfold error in *.
        unfold Rabs in *.
        destruct Rcase_abs; destruct Rcase_abs;
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end;
        psatz R.
      }
      {
        destruct H0.
        {
          rewrite <- H0 in H.
          simpl in H.
          rewrite <- H0.
          decompose [and] H.
          apply IHexpr1 in H1.
          apply IHexpr2 in H3.
          assert (expr1Bound := H1).
          assert (expr2Bound := H3).
          assert (floatMinCase := H2).
          assert (floatMaxBound1 := H6). 
          assert (floatMaxBound2 := H7).
          assert (resultGe0 := H9).
          clear H4 H2 H1 H3 H H5 H7 H0 H9 H6 IHexpr1 IHexpr2.
          unfold Semantics.eval_comp in *.
          simpl in floatMinCase.
          simpl in expr1Bound.
          simpl in expr2Bound.
          simpl in floatMaxBound2.
          simpl in floatMaxBound1.
          simpl in resultGe0.
          simpl.
          remember (eval_term (lb x4) (hd tr) (hd (tl tr))) as lb1.
          remember (eval_term (lb x5) (hd tr) (hd (tl tr))) as lb2.
          remember (eval_term (ub x5) (hd tr) (hd (tl tr))) as ub2.
          remember (eval_term (ub x4) (hd tr) (hd (tl tr))) as ub1.
          clear Hequb1 Hequb2 Heqlb1 Heqlb2.
          pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
          specialize (relErrorBasedOnFloatMinTruthPlus x1 x2 lb1 lb2 ub1 ub2).
          destruct expr1Bound.
          destruct expr2Bound.
          pose proof or_introl.
          
          intros.
          specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H H1 H0 H2).
          pose proof plusRoundingTruth as plusRoundingTruth.
          specialize (plusRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 floatMinCase H H1 floatMaxBound1 floatMaxBound2 H0 H2).
          pose proof plusRoundingTruth2 as plusRoundingTruth2.
          specialize (plusRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 plusRoundingTruth).
          revert plusResultStmt. intros plusResultStmt.
          apply validFloat2 in floatToRealProof1.
          apply validFloat2 in floatToRealProof2.
          rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
          rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
          

          remember ( round radix2
                           (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                           (round_mode mode_NE)
                           (B2R custom_prec custom_emax x +
                            B2R custom_prec custom_emax x0)) as roundedValue. 

          simpl in plusRoundingTruth2.
          simpl in plusResultStmt.
          rewrite <- plusResultStmt in plusRoundingTruth2.
          simpl in plusRoundingTruth2.
          decompose [and] plusRoundingTruth2.
          rewrite  H4.
          clear H5.
          clear plusRoundingTruth2.
          assert (plusRoundingTruth2:= H4).
          clear H4.
          clear plusResultStmt.
          clear H3.
          clear plusRoundingTruth.
          rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
          rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
          rewrite <- floatToRealProof2  in HeqroundedValue.
          rewrite <- floatToRealProof1 in HeqroundedValue.

          pose proof errorGt0.
          clear floatMinCase floatMaxBound1 floatMaxBound2 HeqroundedValue 
                plusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2 x3 x4 x4 x5 x x0 expr1 expr2 tr fState r.
          pose proof errorLessThan1.
          unfold error in *.
          unfold Rabs in *.
          destruct Rcase_abs; destruct Rcase_abs;
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end;
          psatz R.
        }
        
        {
          intuition.
        }
      }
    }
    
    {
      rewrite <- H9 in Heqo0.
      inversion Heqo0.
    }
    {
      rewrite <- H9 in Heqo0.
      inversion Heqo0.
    }
    
    {
     


      rewrite <- H9 in Heqo0.
      inversion Heqo0.
      assert (plusResultStmt := H9).
      assert (floatToRealRelationForExpr1:= H2).
      assert (floatToRealRelationForExpr2:= H3).
      clear H f Heqo0 H0 H1 H8 f_des Heqo' H9 H10 .
      assert (floatToRealProof1:= H2).
      assert (floatToRealProof2:= H3).
      clear H2 H3.
      
      
      unfold denote_singleBoundTerm in *.
      intros.
      simpl in H6.
      unfold simpleBound in *.
      unfold simpleBound4 in *.
      destruct H6.
      
      {
        rewrite <- H0 in H.
        simpl in H.

        rewrite <- H0.
        decompose [and] H.
        apply IHexpr1 in H1.
        apply IHexpr2 in H3.
        assert (expr1Bound := H1).
        assert (expr2Bound := H3).
        assert (floatMinCase := H2).
        assert (floatMaxBound1 := H6). 
        assert (floatMaxBound2 := H7).
        assert (resultGe0 := H9).
        clear H4 H2 H1 H3 H H5 H7 H0 H9 H6 IHexpr1 IHexpr2.
        unfold Semantics.eval_comp in *.
        simpl in floatMinCase.
        simpl in expr1Bound.
        simpl in expr2Bound.
        simpl in floatMaxBound2.
        simpl in floatMaxBound1.
        simpl in resultGe0.
        simpl.
        remember (eval_term (lb x4) (hd tr) (hd (tl tr))) as lb1.
        remember (eval_term (lb x5) (hd tr) (hd (tl tr))) as lb2.
        remember (eval_term (ub x5) (hd tr) (hd (tl tr))) as ub2.
        remember (eval_term (ub x4) (hd tr) (hd (tl tr))) as ub1.
        clear Hequb1 Hequb2 Heqlb1 Heqlb2.
        pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
        specialize (relErrorBasedOnFloatMinTruthPlus x1 x2 lb1 lb2 ub1 ub2).
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        
        intros.
        specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H H1 H0 H2).
        pose proof plusRoundingTruth as plusRoundingTruth.
        specialize (plusRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 floatMinCase H H1 floatMaxBound1 floatMaxBound2 H0 H2).
        pose proof plusRoundingTruth2 as plusRoundingTruth2.
        specialize (plusRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 plusRoundingTruth).
        revert plusResultStmt. intros plusResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
        

        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x +
                          B2R custom_prec custom_emax x0)) as roundedValue. 

        simpl in plusRoundingTruth2.
        simpl in plusResultStmt.
        rewrite <- plusResultStmt in plusRoundingTruth2.
        simpl in plusRoundingTruth2.
        decompose [and] plusRoundingTruth2.
        rewrite  H4.
        clear H5.
        clear plusRoundingTruth2.
        assert (plusRoundingTruth2:= H4).
        clear H4.
        clear plusResultStmt.
        clear H3.
        clear plusRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
        rewrite <- floatToRealProof2  in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.

        pose proof errorGt0.
        clear floatMinCase floatMaxBound1 floatMaxBound2 HeqroundedValue 
              plusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2 e0 e x3 x4 x4 x5 x x0 expr1 expr2 tr fState b m r.
        pose proof errorLessThan1.
        unfold error in *.
        unfold Rabs in *.
        destruct Rcase_abs; destruct Rcase_abs;
        repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
               end;
        psatz R.
      }
      {
        destruct H0.
        {
          rewrite <- H0 in H.
          simpl in H.
          rewrite <- H0.
          decompose [and] H.
          apply IHexpr1 in H1.
          apply IHexpr2 in H3.
          assert (expr1Bound := H1).
          assert (expr2Bound := H3).
          assert (floatMinCase := H2).
          assert (floatMaxBound1 := H6). 
          assert (floatMaxBound2 := H7).
          assert (resultGe0 := H9).
          clear H4 H2 H1 H3 H H5 H7 H0 H9 H6 IHexpr1 IHexpr2.
          unfold Semantics.eval_comp in *.
          simpl in floatMinCase.
          simpl in expr1Bound.
          simpl in expr2Bound.
          simpl in floatMaxBound2.
          simpl in floatMaxBound1.
          simpl in resultGe0.
          simpl.
          remember (eval_term (lb x4) (hd tr) (hd (tl tr))) as lb1.
          remember (eval_term (lb x5) (hd tr) (hd (tl tr))) as lb2.
          remember (eval_term (ub x5) (hd tr) (hd (tl tr))) as ub2.
          remember (eval_term (ub x4) (hd tr) (hd (tl tr))) as ub1.
          clear Hequb1 Hequb2 Heqlb1 Heqlb2.
          pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
          specialize (relErrorBasedOnFloatMinTruthPlus x1 x2 lb1 lb2 ub1 ub2).
          destruct expr1Bound.
          destruct expr2Bound.
          pose proof or_introl.
          
          intros.
          specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H H1 H0 H2).
          pose proof plusRoundingTruth as plusRoundingTruth.
          specialize (plusRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 floatMinCase H H1 floatMaxBound1 floatMaxBound2 H0 H2).
          pose proof plusRoundingTruth2 as plusRoundingTruth2.
          specialize (plusRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 plusRoundingTruth).
          revert plusResultStmt. intros plusResultStmt.
          apply validFloat2 in floatToRealProof1.
          apply validFloat2 in floatToRealProof2.
          rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
          rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
          

          remember ( round radix2
                           (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                           (round_mode mode_NE)
                           (B2R custom_prec custom_emax x +
                            B2R custom_prec custom_emax x0)) as roundedValue. 

          simpl in plusRoundingTruth2.
          simpl in plusResultStmt.
          rewrite <- plusResultStmt in plusRoundingTruth2.
          simpl in plusRoundingTruth2.
          decompose [and] plusRoundingTruth2.
          rewrite  H4.
          clear H5.
          clear plusRoundingTruth2.
          assert (plusRoundingTruth2:= H4).
          clear H4.
          clear plusResultStmt.
          clear H3.
          clear plusRoundingTruth.
          rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
          rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
          rewrite <- floatToRealProof2  in HeqroundedValue.
          rewrite <- floatToRealProof1 in HeqroundedValue.

          pose proof errorGt0.
          clear floatMinCase floatMaxBound1 floatMaxBound2 HeqroundedValue 
                plusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2 e0 e x3 x4 x4 x5 x x0 expr1 expr2 tr fState b m r.
          pose proof errorLessThan1.
          unfold error in *.
          unfold Rabs in *.
          destruct Rcase_abs;  destruct Rcase_abs;
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H :@ Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end;
          psatz R.
        }
        {
          intuition.
        }
      }
    }
  }
  {
   
    simpl. unfold getBound. unfold plusBound.
    intros.
    Print plusMinusfoldListwithList.
    assert (Heqo':=Heqo).
    apply resultImplicationsMinus in Heqo.
    Require Import ExtLib.Tactics.
    forward_reason. destruct H2; destruct H3.
    specialize (IHexpr1 _ _ H2 H0).
    specialize (IHexpr2 _ _ H3 H1).
    2: eexists; eauto.
    eapply Forall_forall. intros.
    eapply In_cross_In in H4.
    forward_reason.
    eapply Forall_forall in IHexpr1; eauto.
    eapply Forall_forall in IHexpr2; eauto.
    inversion Heqo'.
    unfold lift2 in Heqo'.
    rewrite <- H0 in Heqo'.
    rewrite <- H1 in Heqo'.
    inversion Heqo'.
    unfold floatToReal in Heqo0.
    rewrite H9 in Heqo0.
    unfold floatToReal in Heqo0.
    destruct f eqn:f_des.
    {
      rewrite <- H9 in Heqo0.
      inversion Heqo0.
      assert (minusResultStmt := H9).
      assert (floatToRealRelationForExpr1:= H2).
      assert (floatToRealRelationForExpr2:= H3).
      clear H f Heqo0 H0 H1 H8 f_des Heqo' H9 H10 .
      assert (floatToRealProof1:= H2).
      assert (floatToRealProof2:= H3).
      clear H2 H3.
      unfold denote_singleBoundTerm in *.
      intros.
      simpl in H6.
      unfold simpleBound2 in *.
      unfold simpleBound5 in *.
      destruct H6.
      {
         
        rewrite <- H0 in H.
        simpl in H.
        rewrite <- H0.
        decompose [and] H.
        apply IHexpr1 in H1.
        apply IHexpr2 in H3.
        assert (expr1Bound := H1).
        assert (expr2Bound := H3).
        assert (floatMinCase := H6).
        assert (floatMaxBound1 := H8).
        assert (resultGe0 := H2).
         clear H4 H2 H1 H3 H H5  H0  H6 IHexpr1 IHexpr2.
       unfold Semantics.eval_comp in *.
         simpl in floatMinCase.
        simpl in expr1Bound.
        simpl in expr2Bound.
        simpl in floatMaxBound1.
        simpl in resultGe0.
        simpl.
        remember (eval_term (lb x4) (hd tr) (hd (tl tr))) as lb1.
        remember (eval_term (lb x5) (hd tr) (hd (tl tr))) as lb2.
        remember (eval_term (ub x5) (hd tr) (hd (tl tr))) as ub2.
        remember (eval_term (ub x4) (hd tr) (hd (tl tr))) as ub1.
        clear Hequb1 Hequb2 Heqlb1 Heqlb2.
        pose proof relErrorBasedOnFloatMinTruthMinus as relErrorBasedOnFloatMinTruthMinus.
        specialize (relErrorBasedOnFloatMinTruthMinus x1 x2 lb1 lb2 ub1 ub2).
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        intros.
        
        Lemma conjoin : forall (p1 p2:Prop), p1 -> p2 -> p1 /\ p2.
          intros.
          intuition.
        Qed.
        intros.
        pose proof conjoin as conjoin.
        specialize (conjoin (lb1 >= ub2)%R (floatMin <= lb1 - ub2)%R%R).
        specialize (conjoin resultGe0 floatMinCase).
        clear floatMinCase.
        assert (floatMinCase:=conjoin).
        clear conjoin.
        Lemma orExtra : forall (p1 p2:Prop), p1 -> p1 \/ p2.
          intros.
          intuition.
        Qed.
        intros.
        pose proof orExtra as extraFloatMinCase.
        specialize (extraFloatMinCase ((lb1 >= ub2)%R /\ (floatMin <= lb1 - ub2))%R ((ub1 <= lb2)%R /\ (floatMin <= lb2 - ub1))%R ).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H H1 H0 H2).
        pose proof minusRoundingTruth as minusRoundingTruth.
        Lemma andExtra : forall (p1 p2:Prop), p1  -> p2 ->   p1 /\ p2.
          intros.
          intuition.
        Qed.
        intros.
        pose proof andExtra as andExtra.
        specialize (andExtra (lb1 >= ub2 /\ floatMin <= lb1 - ub2)%R ((ub1 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
      
          
        pose proof orExtra as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2 
                      (((lb1 >= ub2) /\ (floatMin <= lb1 - ub2)) /\ ((ub1 - lb2) * (1 + error) < floatMax)) (((ub1 <= lb2)%R /\
  (floatMin <= lb2 - ub1)) /\ ((ub2 - lb1) * (1 + error) < floatMax))).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).
        
        specialize (minusRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H H1 H0 H2).
        
        pose proof minusRoundingTruth2 as minusRoundingTruth2.
        specialize (minusRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 minusRoundingTruth).
        revert minusResultStmt. intros minusResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x -
                          B2R custom_prec custom_emax x0)) as roundedValue.
        simpl in minusRoundingTruth2.
        simpl in minusResultStmt.
        rewrite <- minusResultStmt in minusRoundingTruth2.
        simpl in minusRoundingTruth2.
        decompose [and] minusRoundingTruth2.
        rewrite H4.
        clear H5.
        clear minusRoundingTruth2.
        assert (minusRoundingTruth2:= H4).
        clear H4.
        clear minusResultStmt.
        clear H3.
        clear minusRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear  floatMinCase floatMaxBound1 HeqroundedValue minusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  H8  x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
        pose proof errorLessThan1.
        unfold error in *.
        unfold Rabs in *.
        clear extraFloatMinCase2 andExtra extraFloatMinCase.
       Local Close Scope R_scope.
 (*does not work fine*)
        destruct Rcase_abs. 
        {
          destruct Rcase_abs.
          {
            split.
            {
              clear -r r0 resultGe0 H H2.
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit.
            }
            {
              clear -r r0 resultGe0 H H2.
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit.
            }
          }
          
          {
            split.
            {
             
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit.
            }
            {
            repeat match goal with
                     | H : @eq R _ _ |- _ => revert H
                     | H : @Rle _ _ |- _ => revert H
                     | H : @Rge _ _ |- _ => revert H
                     | H : @Rlt _ _ |- _ => revert H
                     | H : @Rgt _ _ |- _ => revert H
                     | H : @Rge _ _ |- _ => revert H
                   end.
            (*z3Tactic*)
            admit.
          }
        }
        }
        {
          split.
          {
            repeat match goal with
                     | H : @eq R _ _ |- _ => revert H
                     | H : @Rle _ _ |- _ => revert H
                     | H : @Rge _ _ |- _ => revert H
                     | H : @Rlt _ _ |- _ => revert H
                     | H : @Rgt _ _ |- _ => revert H
                     | H : @Rge _ _ |- _ => revert H
                   end.
            psatz R.
           }
          destruct Rcase_abs.
          
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H : @Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          psatz R.
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H : @Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          psatz R.
          
 
        }
      }
      {
         destruct H0.
        {
        rewrite <- H0 in H.
        simpl in H.
        rewrite <- H0.
        decompose [and] H.
        apply IHexpr1 in H1.
        apply IHexpr2 in H3.
        assert (expr1Bound := H1).
        assert (expr2Bound := H3).
        assert (floatMinCase := H6).
        assert (floatMaxBound1 := H8).
        assert (resultGe0 := H2).
         clear H4 H2 H1 H3 H H5  H0  H6 IHexpr1 IHexpr2.
       unfold Semantics.eval_comp in *.
         simpl in floatMinCase.
        simpl in expr1Bound.
        simpl in expr2Bound.
        simpl in floatMaxBound1.
        simpl in resultGe0.
        simpl.
        remember (eval_term (lb x4) (hd tr) (hd (tl tr))) as lb1.
        remember (eval_term (lb x5) (hd tr) (hd (tl tr))) as lb2.
        remember (eval_term (ub x5) (hd tr) (hd (tl tr))) as ub2.
        remember (eval_term (ub x4) (hd tr) (hd (tl tr))) as ub1.
        clear Hequb1 Hequb2 Heqlb1 Heqlb2.
        pose proof relErrorBasedOnFloatMinTruthMinus as relErrorBasedOnFloatMinTruthMinus.
        specialize (relErrorBasedOnFloatMinTruthMinus x1 x2 lb1 lb2 ub1 ub2).
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        intros.
       
        intros.
        pose proof conjoin as conjoin.
        specialize (conjoin (ub1 <= lb2)%R (floatMin <= lb2 - ub1)%R%R).
        specialize (conjoin resultGe0 floatMinCase).
        clear floatMinCase.
        assert (floatMinCase:=conjoin).
        clear conjoin.
        intros.
         Lemma orExtra2 : forall p1 p2 : Prop, p2 -> p1 \/ p2.
          intros; intuition. Qed.
        pose proof orExtra2 as extraFloatMinCase.
        specialize (extraFloatMinCase ((lb1 >= ub2)%R /\ (floatMin <= lb1 - ub2)%R) ((ub1 <= lb2)%R /\ (floatMin <= lb2 - ub1))%R ).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H H1 H0 H2).
        pose proof minusRoundingTruth as minusRoundingTruth.
       
        intros.
        pose proof andExtra as andExtra.
        specialize (andExtra (ub1 <= lb2 /\ floatMin <= lb2 - ub1)%R ((ub2 - lb1) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
      
          
        pose proof orExtra2 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2 
                      (((lb1 >= ub2) /\ (floatMin <= lb1 - ub2)) /\ ((ub1 - lb2) * (1 + error) < floatMax)) (((ub1 <= lb2)%R /\
  (floatMin <= lb2 - ub1)) /\ ((ub2 - lb1) * (1 + error) < floatMax))).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).
        
        specialize (minusRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H H1 H0 H2).
        
        pose proof minusRoundingTruth2 as minusRoundingTruth2.
        specialize (minusRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 minusRoundingTruth).
        revert minusResultStmt. intros minusResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x -
                          B2R custom_prec custom_emax x0)) as roundedValue.
        simpl in minusRoundingTruth2.
        simpl in minusResultStmt.
        rewrite <- minusResultStmt in minusRoundingTruth2.
        simpl in minusRoundingTruth2.
        decompose [and] minusRoundingTruth2.
        rewrite H4.
        clear H5.
        clear minusRoundingTruth2.
        assert (minusRoundingTruth2:= H4).
        clear H4.
        clear minusResultStmt.
        clear H3.
        clear minusRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear  floatMinCase floatMaxBound1 HeqroundedValue minusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  H8  x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
        pose proof errorLessThan1.
        unfold error in *.
        unfold Rabs in *.
        clear extraFloatMinCase2 andExtra extraFloatMinCase.
        Local Close Scope R_scope.
        destruct Rcase_abs. 
        {
          destruct Rcase_abs.
          {
            split.
            {
             
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit. (*z3 verified*)
            }
            {
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit. (*z3 verified*)
            }
          }
          
          {
            split.
            {
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit. (*z3 verified*)
            }
            {
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit. (*z3 verified*)
            }
          }
        }
        {
          destruct Rcase_abs.
          {
            split.
            {
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit. (*z3 verified*)
            }
            {
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit. (*z3 verified*)
            }
          }
          
          {
            split.
            {
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit. (*z3 verified*)
            }
            {
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              
              (*z3Tactic*)
              admit. (*z3 verified*)
            }
          }
        }
        }        
        {
          {
            repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H : @Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
            psatz R.
          }
        }
      }
    }
    {
       
      rewrite <- H9 in Heqo0.
      inversion Heqo0.
    }
    {
      rewrite <- H9 in Heqo0.
      inversion Heqo0.
    }
    
    {

      rewrite <- H9 in Heqo0.
      inversion Heqo0.
      assert (minusResultStmt := H9).
      assert (floatToRealRelationForExpr1:= H2).
      assert (floatToRealRelationForExpr2:= H3).
      clear H f Heqo0 H0 H1 H8 f_des Heqo' H9 H10 .
      assert (floatToRealProof1:= H2).
      assert (floatToRealProof2:= H3).
      clear H2 H3.
      unfold denote_singleBoundTerm in *.
      intros.
      simpl in H6.
      unfold simpleBound2 in *.
      unfold simpleBound5 in *.
      destruct H6.
      {
        rewrite <- H0 in H.
        simpl in H.
        rewrite <- H0.
        decompose [and] H.
        apply IHexpr1 in H1.
        apply IHexpr2 in H3.
        assert (expr1Bound := H1).
        assert (expr2Bound := H3).
        assert (floatMinCase := H6).
        assert (floatMaxBound1 := H8).
        assert (resultGe0 := H2).
        clear H4 H2 H1 H3 H H5 H0 H6 IHexpr1 IHexpr2.
        unfold Semantics.eval_comp in *.
        simpl in floatMinCase.
        simpl in expr1Bound.
        simpl in expr2Bound.
        simpl in floatMaxBound1.
        simpl in resultGe0.
        simpl.
        remember (eval_term (lb x4) (hd tr) (hd (tl tr))) as lb1.
        remember (eval_term (lb x5) (hd tr) (hd (tl tr))) as lb2.
        remember (eval_term (ub x5) (hd tr) (hd (tl tr))) as ub2.
        remember (eval_term (ub x4) (hd tr) (hd (tl tr))) as ub1.
        clear Hequb1 Hequb2 Heqlb1 Heqlb2.
        pose proof relErrorBasedOnFloatMinTruthMinus as relErrorBasedOnFloatMinTruthMinus.
        specialize (relErrorBasedOnFloatMinTruthMinus x1 x2 lb1 lb2 ub1 ub2).
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        intros.
        intros.
        pose proof conjoin as conjoin.
        specialize (conjoin (lb1 >= ub2)%R (floatMin <= lb1 - ub2)%R%R).
        specialize (conjoin resultGe0 floatMinCase).
        clear floatMinCase.
        assert (floatMinCase:=conjoin).
        clear conjoin.
        intros.
        pose proof orExtra as extraFloatMinCase.
        specialize (extraFloatMinCase ((lb1 >= ub2)%R /\ (floatMin <= lb1 - ub2))%R ((ub1 <= lb2)%R /\ (floatMin <= lb2 - ub1))%R ).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H H1 H0 H2).
        pose proof minusRoundingTruth as minusRoundingTruth.


        intros.
        pose proof andExtra as andExtra.
        specialize (andExtra (lb1 >= ub2 /\ floatMin <= lb1 - ub2)%R ((ub1 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        pose proof orExtra as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2
                      (((lb1 >= ub2) /\ (floatMin <= lb1 - ub2)) /\ ((ub1 - lb2) * (1 + error) < floatMax)) (((ub1 <= lb2)%R /\
                                                                                                              (floatMin <= lb2 - ub1)) /\ ((ub2 - lb1) * (1 + error) < floatMax))).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).
        specialize (minusRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H H1 H0 H2).
        pose proof minusRoundingTruth2 as minusRoundingTruth2.
        specialize (minusRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 minusRoundingTruth).
        revert minusResultStmt. intros minusResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x -
                          B2R custom_prec custom_emax x0)) as roundedValue.
        simpl in minusRoundingTruth2.
        simpl in minusResultStmt.
        rewrite <- minusResultStmt in minusRoundingTruth2.
        simpl in minusRoundingTruth2.
        decompose [and] minusRoundingTruth2.
        rewrite H4.
        clear H5.
        clear minusRoundingTruth2.
        assert (minusRoundingTruth2:= H4).
        clear H4.
        clear minusResultStmt.
        clear H3.
        clear minusRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear floatMinCase floatMaxBound1 HeqroundedValue minusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2 H8 x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
        pose proof errorLessThan1.
        unfold error in *.
        unfold Rabs in *.
        clear extraFloatMinCase2 andExtra extraFloatMinCase.
        Local Close Scope R_scope.
        (*does not work fine*)
        destruct Rcase_abs.
        {
          destruct Rcase_abs.
          {
            split.
            {
              clear -r r0 resultGe0 H H2.
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit.
            }
            {
              clear -r r0 resultGe0 H H2.
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit.
            }
          }
          {
            split.
            {
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit.
            }
            {
              repeat match goal with
                       | H : @eq R _ _ |- _ => revert H
                       | H : @Rle _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                       | H : @Rlt _ _ |- _ => revert H
                       | H : @Rgt _ _ |- _ => revert H
                       | H : @Rge _ _ |- _ => revert H
                     end.
              (*z3Tactic*)
              admit.
            }
          }
        }
        {
          split.
          {
            repeat match goal with
                     | H : @eq R _ _ |- _ => revert H
                     | H : @Rle _ _ |- _ => revert H
                     | H : @Rge _ _ |- _ => revert H
                     | H : @Rlt _ _ |- _ => revert H
                     | H : @Rgt _ _ |- _ => revert H
                     | H : @Rge _ _ |- _ => revert H
                   end.
            psatz R.
          }
          destruct Rcase_abs.
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H : @Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          psatz R.
          repeat match goal with
                   | H : @eq R _ _ |- _ => revert H
                   | H : @Rle _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                   | H : @Rlt _ _ |- _ => revert H
                   | H : @Rgt _ _ |- _ => revert H
                   | H : @Rge _ _ |- _ => revert H
                 end.
          psatz R.
        }
      }
      {
        destruct H0.
        {
          rewrite <- H0 in H.
          simpl in H.
          rewrite <- H0.
          decompose [and] H.
          apply IHexpr1 in H1.
          apply IHexpr2 in H3.
          assert (expr1Bound := H1).
          assert (expr2Bound := H3).
          assert (floatMinCase := H6).
          assert (floatMaxBound1 := H8).
          assert (resultGe0 := H2).
          clear H4 H2 H1 H3 H H5 H0 H6 IHexpr1 IHexpr2.
          unfold Semantics.eval_comp in *.
          simpl in floatMinCase.
          simpl in expr1Bound.
          simpl in expr2Bound.
          simpl in floatMaxBound1.
          simpl in resultGe0.
          simpl.
          remember (eval_term (lb x4) (hd tr) (hd (tl tr))) as lb1.
          remember (eval_term (lb x5) (hd tr) (hd (tl tr))) as lb2.
          remember (eval_term (ub x5) (hd tr) (hd (tl tr))) as ub2.
          remember (eval_term (ub x4) (hd tr) (hd (tl tr))) as ub1.
          clear Hequb1 Hequb2 Heqlb1 Heqlb2.
          pose proof relErrorBasedOnFloatMinTruthMinus as relErrorBasedOnFloatMinTruthMinus.
          specialize (relErrorBasedOnFloatMinTruthMinus x1 x2 lb1 lb2 ub1 ub2).
          destruct expr1Bound.
          destruct expr2Bound.
          pose proof or_introl.
          intros.
          intros.
          pose proof conjoin as conjoin.
          specialize (conjoin (ub1 <= lb2)%R (floatMin <= lb2 - ub1)%R%R).
          specialize (conjoin resultGe0 floatMinCase).
          clear floatMinCase.
          assert (floatMinCase:=conjoin).
          clear conjoin.
          intros.

          pose proof orExtra2 as extraFloatMinCase.
          specialize (extraFloatMinCase ((lb1 >= ub2)%R /\ (floatMin <= lb1 - ub2)%R) ((ub1 <= lb2)%R /\ (floatMin <= lb2 - ub1))%R ).
          specialize (extraFloatMinCase floatMinCase).
          specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H H1 H0 H2).
          pose proof minusRoundingTruth as minusRoundingTruth.
          intros.
          pose proof andExtra as andExtra.
          specialize (andExtra (ub1 <= lb2 /\ floatMin <= lb2 - ub1)%R ((ub2 - lb1) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
          pose proof orExtra2 as extraFloatMinCase2.
          simpl in andExtra.
          simpl in extraFloatMinCase2.
          Local Open Scope R_scope.
          specialize (extraFloatMinCase2
                        (((lb1 >= ub2) /\ (floatMin <= lb1 - ub2)) /\ ((ub1 - lb2) * (1 + error) < floatMax)) (((ub1 <= lb2)%R /\
                                                                                                                (floatMin <= lb2 - ub1)) /\ ((ub2 - lb1) * (1 + error) < floatMax))).
          simpl in extraFloatMinCase2.
          specialize (extraFloatMinCase2 andExtra).
          specialize (minusRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H H1 H0 H2).
          pose proof minusRoundingTruth2 as minusRoundingTruth2.
          specialize (minusRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 minusRoundingTruth).
          revert minusResultStmt. intros minusResultStmt.
          apply validFloat2 in floatToRealProof1.
          apply validFloat2 in floatToRealProof2.
          rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
          rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
          remember ( round radix2
                           (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                           (round_mode mode_NE)
                           (B2R custom_prec custom_emax x -
                            B2R custom_prec custom_emax x0)) as roundedValue.
          simpl in minusRoundingTruth2.
          simpl in minusResultStmt.
          rewrite <- minusResultStmt in minusRoundingTruth2.
          simpl in minusRoundingTruth2.
          decompose [and] minusRoundingTruth2.
          rewrite H4.
          clear H5.
          clear minusRoundingTruth2.
          assert (minusRoundingTruth2:= H4).
          clear H4.
          clear minusResultStmt.
          clear H3.
          clear minusRoundingTruth.
          rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
          rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
          rewrite <- floatToRealProof2 in HeqroundedValue.
          rewrite <- floatToRealProof1 in HeqroundedValue.
          pose proof errorGt0.
          clear floatMinCase floatMaxBound1 HeqroundedValue minusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2 H8 x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
          pose proof errorLessThan1.
          unfold error in *.
          unfold Rabs in *.
          clear extraFloatMinCase2 andExtra extraFloatMinCase.
          Local Close Scope R_scope.
          destruct Rcase_abs.
          {
            destruct Rcase_abs.
            {
              split.
              {
                repeat match goal with
                         | H : @eq R _ _ |- _ => revert H
                         | H : @Rle _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                         | H : @Rlt _ _ |- _ => revert H
                         | H : @Rgt _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                       end.
                (*z3Tactic*)
                admit. (*z3 verified*)
              }
              {
                repeat match goal with
                         | H : @eq R _ _ |- _ => revert H
                         | H : @Rle _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                         | H : @Rlt _ _ |- _ => revert H
                         | H : @Rgt _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                       end.
                (*z3Tactic*)
                admit. (*z3 verified*)
              }
            }
            {
              split.
              {
                repeat match goal with
                         | H : @eq R _ _ |- _ => revert H
                         | H : @Rle _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                         | H : @Rlt _ _ |- _ => revert H
                         | H : @Rgt _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                       end.
                (*z3Tactic*)
                admit. (*z3 verified*)
              }
              {
                repeat match goal with
                         | H : @eq R _ _ |- _ => revert H
                         | H : @Rle _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                         | H : @Rlt _ _ |- _ => revert H
                         | H : @Rgt _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                       end.
                (*z3Tactic*)
                admit. (*z3 verified*)
              }
            }
          }
          {
            destruct Rcase_abs.
            {
              split.
              {
                repeat match goal with
                         | H : @eq R _ _ |- _ => revert H
                         | H : @Rle _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                         | H : @Rlt _ _ |- _ => revert H
                         | H : @Rgt _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                       end.
                (*z3Tactic*)
                admit. (*z3 verified*)
              }
              {
                repeat match goal with
                         | H : @eq R _ _ |- _ => revert H
                         | H : @Rle _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                         | H : @Rlt _ _ |- _ => revert H
                         | H : @Rgt _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                       end.
                (*z3Tactic*)
                admit. (*z3 verified*)
              }
            }
            {
              split.
              {
                repeat match goal with
                         | H : @eq R _ _ |- _ => revert H
                         | H : @Rle _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                         | H : @Rlt _ _ |- _ => revert H
                         | H : @Rgt _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                       end.
                (*z3Tactic*)
                admit. (*z3 verified*)
              }
              {
                repeat match goal with
                         | H : @eq R _ _ |- _ => revert H
                         | H : @Rle _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                         | H : @Rlt _ _ |- _ => revert H
                         | H : @Rgt _ _ |- _ => revert H
                         | H : @Rge _ _ |- _ => revert H
                       end.
                (*z3Tactic*)
                admit. (*z3 verified*)
              }
            }
          }
        }
        {
          {
            repeat match goal with
                     | H : @eq R _ _ |- _ => revert H
                     | H : @Rle _ _ |- _ => revert H
                     | H : @Rge _ _ |- _ => revert H
                     | H : @Rlt _ _ |- _ => revert H
                     | H : @Rgt _ _ |- _ => revert H
                     | H : @Rge _ _ |- _ => revert H
                   end.
            psatz R.
          }
        }
      }
    }
  }  
Admitted.   
