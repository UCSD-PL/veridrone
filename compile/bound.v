Require Import Coq.micromega.Psatz.
Require Import Coq.Reals.Raxioms.
Require Import Coq.micromega.Psatz.
Require Import compcert.flocq.Core.Fcore_defs.

Require Import compcert.lib.Integers.
Require Import Coq.Reals.Rdefinitions.
Require Import List.
Import ListNotations.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.Automation.
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
Print Bplus_correct.
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
  mkSBT ((combFunc (ub triple1)  (ub triple2)) * (RealT R1 - RealT error)) 
        ((combFunc (lb triple1) (lb triple2)) * (RealT R1 + RealT error)) 
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

(*used for multiplication - when one of the arguments is negative*)
Definition simpleBound7 
           (triple1 triple2:singleBoundTerm) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple1)  (ub triple2)) * (RealT R1+ RealT error)) 
        ((combFunc (ub triple1) (lb triple2)) * (RealT R1 - RealT error)) 
        fla.

(*used for multiplication - when one of the arguments is negative*)
Definition simpleBound8 
           (triple1 triple2:singleBoundTerm) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple1)  (ub triple2)) * (RealT R1+ RealT error)) 
        ((combFunc (ub triple1) (lb triple2)) * (RealT R1 + RealT error)) 
        fla.
(*used for additon - when lb1 + lb2 < floatMin*)
Definition simpleBound9
           (triple1 triple2:singleBoundTerm) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  singleBoundTerm := 
  mkSBT 0 
        ((combFunc (ub triple1) (ub triple2)) * (RealT R1 + RealT error)) 
        fla.



Definition floatMax:= bpow radix2 custom_emax.
Definition floatMin := bpow radix2 custom_emin%Z.

(*used for addition when ub1 + ub2 < floatMin*)
Definition simpleBound10
           (triple1 triple2:singleBoundTerm) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  singleBoundTerm := 
  mkSBT 0 floatMin 
        fla.



(*used for subtraction - when lb1 + lb2 is greater than -floatMin*)
Definition simpleBound11
           (triple1 triple2:singleBoundTerm) 
           (combFunc:Term->Term->Term)  
           (fla:Formula) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple1)  (lb triple2)) * (RealT R1 + RealT error)) 0
        fla.

Definition isFloatConstValid (f:binary_float custom_prec custom_emax) : Prop 
  := match f with 
       | B754_zero _ => True
       | B754_infinity _=> False
       | B754_nan _ _=> False
       | B754_finite _ _ _ _=> True
     end.


Definition plusResultValidity (t1 t2 : NowTerm) := 
      (forall (fState:fstate),
          let result := (lift2
                           (Bplus custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                  custom_nan mode_NE) (eval_NowTerm fState t1) (eval_NowTerm fState t2)) 
          in match result with 
                | Some f => isFloatConstValid f 
                | None => False
              end).
Definition minusResultValidity (t1 t2 : NowTerm) := 
      (forall (fState:fstate),
          let result := (lift2
                           (Bminus custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                  custom_nan mode_NE) (eval_NowTerm fState t1) (eval_NowTerm fState t2)) 
          in match result with 
                | Some f => isFloatConstValid f 
                | None => False
              end).

Definition multResultValidity (t1 t2 : NowTerm) := 
      (forall (fState:fstate),
          let result := (lift2
                           (Bmult custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                  custom_nan mode_NE) (eval_NowTerm fState t1) (eval_NowTerm fState t2)) 
          in match result with 
                | Some f => isFloatConstValid f 
                | None => False
              end).

Definition combineTriplePlus (triple triple2 : singleBoundTerm) (t1 t2 : NowTerm):=
  ((simpleBound triple triple2 PlusT 
                (premise triple //\\
                 premise triple2 //\\ 
                 ((floatMin <= lb triple + lb triple2)) //\\ 
                 ((ub triple + ub triple2)*(1+error) < floatMax) //\\
                 (lb triple + lb triple2 >= R0) //\\
                 (PropF (plusResultValidity t1 t2))))
     :: (simpleBound4 triple triple2 PlusT 
                      (premise triple //\\ 
                       premise triple2 //\\ 
                       (floatMin <= ((0 - ub triple) + (0 - ub triple2))) //\\
                       (((0 - lb triple + (0 - lb triple2))*(1+error)) < floatMax) //\\ 
                       (ub triple + ub triple2 < R0)//\\
                       (PropF (plusResultValidity t1 t2))))
     :: (simpleBound9 triple triple2 PlusT 
                      (premise triple //\\ 
                       premise triple2 //\\
                       (lb triple + lb triple2 < floatMin) //\\ 
                       (ub triple + ub triple2 >= floatMin) //\\ 
                       ((ub triple + ub triple2)*(1+error) < floatMax) //\\ 
                       (lb triple + lb triple2 >= R0)//\\
                       (PropF (plusResultValidity t1 t2))))
     :: (simpleBound10 triple triple2 PlusT 
                      (premise triple //\\ 
                       premise triple2 //\\
                       (ub triple + ub triple2 < floatMin) //\\ 
                       ((ub triple + ub triple2)*(1+error) < floatMax) //\\ 
                       (lb triple + lb triple2 >= R0)//\\
                       (PropF (plusResultValidity t1 t2))))
     :: List.nil). 

(*
    (((ub triple - ub triple2 >= floatMin) //\\ (lb triple - lb triple2 >=floatMin) //\\ (ub triple2 - lb triple >= floatMin)) \\//
                                         ((ub triple2 - ub triple >= floatMin) //\\ (lb triple - lb triple2 >=floatMin)) \\//
                                         ((ub triple - ub triple2 >= floatMin) /\ (lb triple2 - lb triple >= floatMin)) \\//
                                         ((ub triple2 - ub triple >=floatMin) /\ (ub triple - lb triple2 >=floatMin) /\ (lb triple2 - lb triple >= floatMin)) ) /\
*)
Print Float.
Definition combineTripleMinus (triple triple2 : singleBoundTerm) (t1 t2:NowTerm):=
  ((simpleBound2 triple triple2 MinusT 
                 (premise triple //\\ 
                  premise triple2  //\\ 
                  (lb triple >= ub triple2) //\\
                 (floatMin <= lb triple - ub triple2) //\\ 
                ((ub triple - lb triple2)*(1+error) < floatMax)//\\
                (PropF (minusResultValidity t1 t2))))
     :: (simpleBound5 triple triple2 MinusT 
                      (premise triple //\\ 
                       premise triple2 //\\
                       (ub triple <= lb triple2) //\\
                       (floatMin <= lb triple2 - ub triple) //\\
                       ((ub triple2 - lb triple)*(1+error) < floatMax) //\\
                       (PropF (minusResultValidity t1 t2)))
                    :: List.nil)).   
Definition combineTripleMult (triple triple2 : singleBoundTerm) (t1 t2:NowTerm):=
  ((simpleBound triple triple2 MultT 
                (premise triple //\\ 
                 premise triple2 //\\ 
                 (floatMin <= lb triple * lb triple2) //\\ 
                 ((ub triple * ub triple2)*(1+error) < floatMax) //\\ 
                 (lb triple >= R0) //\\ (lb triple2 >= R0) //\\ 
                (PropF (multResultValidity t1 t2))))
    :: (simpleBound3 triple triple2 MultT 
                      (premise triple //\\ 
                       premise triple2 //\\ 
                       (floatMin <= (0 - ub triple) * (0 - ub triple2)) //\\ 
                       (((0 - lb triple) * (0 - lb triple2))*(1+error) < floatMax) //\\ 
                       (ub triple < R0) //\\ (ub triple2 < R0) //\\ 
                       (PropF (multResultValidity t1 t2))))
          :: (simpleBound6 triple triple2 MultT 
                      (premise triple //\\ 
                       premise triple2 //\\ 
                       (floatMin <= (lb triple) * (0 - (ub triple2))) //\\ 
                       ((ub triple * (0 - lb triple2))*(1+error) < floatMax) //\\ 
                       (lb triple >= R0) //\\  (ub triple2 < R0) //\\ (PropF (multResultValidity t1 t2)))) 
                      ::  (simpleBound7 triple triple2 MultT 
                                        (premise triple //\\ 
                                         premise triple2 //\\ 
                                         (floatMin <= (0 - ub triple) * lb triple2) //\\ 
                                         (((0 - lb triple) * (ub triple2))*(1+error) < floatMax) //\\ 
                                         (ub triple < R0) //\\  (lb triple2 >= R0) //\\ (PropF (multResultValidity t1 t2)))) :: List.nil).   
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
          (exists l r, List.In l ls //\\ List.In r rs //\\ List.In x (f l r)).
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
                   | H : _ //\\ _ |- _ => destruct H
                   end.
            do 2 eexists; split; eauto. } }
        { intros.
          repeat destruct H. 
          { constructor; apply in_flat_map;
            exists x1; apply H0.
          }
          {
            constructor 2; apply IHls; exists x0; exists x1;
            tlaIntuition.
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
                                                      (premise triple //\\ 
                                                       premise triple2 //\\ 
                                                       ((floatMin <= lb triple + lb triple2) \\// (floatMin <= ((0 - lb triple) + (0 - lb triple2))) \\// ((lb triple + lb triple =0) //\\ (ub triple + ub triple =0))) //\\ 
                                                       (ub triple + ub triple2 < floatMax) //\\
                                                             ((0- ub triple) + (0 - ub triple2) < floatMax) //\\ 
                                                       (lb triple + lb triple2 >= R0)))
                                       :: ((simpleBoundFunc2 triple triple2 combFunc 
                                                            (premise triple //\\ 
                                                             premise triple2 //\\ 
                                                            ((floatMin <= lb triple + lb triple2) \\// (floatMin <= ((0 - lb triple) + (0 - lb triple2))) \\// ((lb triple + lb triple =0) //\\ (ub triple + ub triple =0))) //\\ 
                                                             (ub triple + ub triple2 < floatMax) //\\
                                                             ((0 - ub triple) + (0 - ub triple2) < floatMax) //\\ 
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
        fun triple2 curList => (simpleBoundFunc1 triple triple2 combFunc  (premise triple //\\ 
                                                                           premise triple2 //\\ 
                                                                           ((floatMin <= lb triple + lb triple2) \\// (floatMin <= ((0 - lb triple) + (0 - lb triple2))) \\// ((lb triple + lb triple =0) //\\ (ub triple + ub triple =0)))//\\
                                                                           (ub triple + ub triple2 < floatMax) //\\  
                                                                           ((0 - ub triple) + (0 - ub triple2) < floatMax) //\\
                                                                           (lb triple >= R0) //\\ (lb triple2 >= R0)))
                                 :: ((simpleBoundFunc2 triple triple2 combFunc 
                                                       (premise triple //\\ 
                                                        premise triple2 //\\ 
                                                        ((floatMin <= lb triple + lb triple2) \\// (floatMin <= ((0 - lb triple) + (0 - lb triple2))) \\// ((lb triple + lb triple =0) //\\ (ub triple + ub triple =0))) //\\ 
                                                        
                                                        (ub triple + ub triple2 < floatMax) //\\
                                                        ((0 - ub triple) + (0 - ub triple2) < floatMax) //\\
                                                        (ub triple < R0) //\\ (ub triple2 < R0)))
                                       :: ((simpleBoundFunc3 triple triple2 combFunc 
                                                             (premise triple //\\ 
                                                              premise triple2 //\\ 
                                                              ((floatMin <= lb triple + lb triple2) \\// (floatMin <= ((0 - lb triple) + (0 - lb triple2))) \\// ((lb triple + lb triple =0) //\\ (ub triple + ub triple =0))) //\\ 
                                                              (ub triple + ub triple2 < floatMax) //\\
                                                              ((0 - ub triple) + (0 - ub triple2) < floatMax) //\\
                                                              (lb triple >= R0) //\\ (ub triple2 < R0)))
                                             :: ((simpleBoundFunc4 triple triple2 combFunc 
                                                                   (premise triple //\\ 
                                                                    premise triple2 //\\ 
                                                                    ((floatMin <= lb triple + lb triple2) \\// (floatMin <= ((0 - lb triple) + (0 - lb triple2))) \\// ((lb triple + lb triple =0) //\\ (ub triple + ub triple =0))) //\\ 
                                                                    ((ub triple + ub triple2 < floatMax) //\\
                                                                     ((0 - ub triple) + (0 - ub triple2) < floatMax)) //\\ 
                                                                    (ub triple < R0) //\\ (lb triple2 >= R0)))
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

Print eval_NowTerm.



Definition isVarValid (v:Var) : Prop 
  := forall (fState:fstate),
    match (fstate_lookup fState v) with 
        | Some f => isFloatConstValid f
        | None => False
    end.



Definition natBound (n:nat): list singleBoundTerm :=

   [ (mkSBT (RealT ((INR n) *(1-error)) ) (RealT ((INR n) * (1+error))) ((floatMin <= RealT (INR n)) //\\ (INR n >= 0) //\\  ((INR n)* (1+error) <  (floatMax)) //\\ (PropF (isFloatConstValid (nat_to_float n))) )) ;  (mkSBT (RealT ((INR n) * (1+error))) (RealT ((INR n)*(1-error))) ((floatMin <= (0 - INR n)) //\\ (INR n < 0) //\\  ((0 - INR n)* (1+error) <  (floatMax)) //\\ (PropF (isFloatConstValid (nat_to_float n))) )  )].



Print eval_NowTerm.
Print singleBoundTerm.
Fixpoint addPlusResultValidity (bounds:list singleBoundTerm) (t1:NowTerm) (t2:NowTerm) := 
  match bounds with 
    | (h :: t) => 
      (match h with  
         | mkSBT lb ub premise  =>
           (let resultValidPremise := 
                (forall (fState:fstate),
                    let result := (lift2
                                     (Bplus custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                            custom_nan mode_NE) (eval_NowTerm fState t1) (eval_NowTerm fState t2)) 
                    in (match result with 
                          | Some f => isFloatConstValid f 
                          | None => False
                        end)
                ) in (mkSBT lb ub (premise //\\ PropF resultValidPremise))
           )
       end) ::  (addPlusResultValidity t t1 t2) 
  | Nil => Nil
  end. 

Fixpoint bound_term (x:NowTerm)  : (list singleBoundTerm):= 
  match x with
    | VarNowN var =>  [mkSBT (VarNowT var) (VarNowT var) (PropF (isVarValid var))]
    | NatN n =>  natBound n
    | FloatN f => [mkSBT (RealT (B2R _ _ f)) (RealT (B2R _ _ f)) (PropF (isFloatConstValid f))]
    | PlusN t1 t2 => cross (fun bd1 bd2 => combineTriplePlus bd1 bd2 t1 t2) (bound_term t1) (bound_term t2)
    | MinusN t1 t2 => cross (fun bd1 bd2 => combineTripleMinus bd1 bd2 t1 t2) (bound_term t1) (bound_term t2)
    | MultN t1 t2 =>  cross (fun bd1 bd2 => combineTripleMult bd1 bd2 t1 t2) (bound_term t1) (bound_term t2)
  end.



Definition floatToReal (f:binary_float custom_prec custom_emax) : option R :=
  match f with 
    | B754_zero _ =>  Some (B2R _ _ f)
    | B754_infinity _ => None
    | B754_nan _ _ => None
    | _ => Some (B2R _ _ f)
    end.

Local Close Scope HP_scope.
Definition foldBoundProp (evalExpr:option (binary_float custom_prec custom_emax)) (tr:trace) :=
  let s1 := Stream.hd tr in
  let s2 := Stream.hd (Stream.tl tr) in
  match evalExpr with 
  | Some evalExpr =>  
    match floatToReal evalExpr with 
    | Some realEvalExpr => 
      (fun (triple:singleBoundTerm) (prop:Prop) =>
         (prop //\\ 
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

CoFixpoint traceFromState (st:state) : (trace) := 
  @Stream.Cons state st (traceFromState st).


Definition denote_singleBoundTermNew (st:state) (s:singleBoundTerm) : Prop*(R->Prop) :=
  let tr := traceFromState st in                                              
  let s1 := Stream.hd tr in
  let s2 := Stream.hd (Stream.tl tr) in
  ((eval_formula (premise s) tr, fun f => eval_term (lb s) s1 s2 <= f <= eval_term (ub s) s1 s2)%R).



Definition denote_singleBoundTerm (f : R) (tr : trace) (s : singleBoundTerm) : Prop :=
  let s1 := Stream.hd tr in
  let s2 := Stream.hd (Stream.tl tr) in
  (eval_formula (premise s) tr
   -> eval_term (lb s) s1 s2 <= f <= eval_term (ub s) s1 s2)%R.

Print List.Forall.

Definition boundDef' :=
fun (expr : NowTerm) (st : Syntax.state) (fState : fstate) =>
match eval_NowTerm fState expr with
| Some evalAsF =>

        List.Forall
          (fun term : singleBoundTerm =>
           let (premise, pred) := denote_singleBoundTermNew st term in
           premise ->
                  match floatToReal evalAsF with
                        | Some f => pred f
                        | None => False
                  end) (bound_term expr)

| None => True
end.


(*
Definition boundDef' (expr:NowTerm) (st:state) (fState: fstate) : Prop :=
  match eval_NowTerm fState expr with
  | Some evalAsF =>
    match floatToReal evalAsF with
    | Some f =>
      List.Forall (fun (term:singleBoundTerm) 
                   => match (denote_singleBoundTermNew st term)  with 
                        | (premise,pred) => premise -> (pred f)
                      end
                  ) (bound_term expr)
    | None => True
    end
  | None => True
  end.
*)
Print boundDef'.


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

Lemma and_proof : forall x1 x2 : Prop, x1 //\\ x2 -> x1.
intros.
tlaIntuition.
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
         prop //\\
         (eval_formula (premise triple) tr ->
          (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
           eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True (a::lst) -> fold_right (fun (triple : singleBoundTerm) (prop : Prop) =>
         prop //\\
         (eval_formula (premise triple) tr ->
          (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
           eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True lst   //\\  (eval_formula (premise a) tr ->
       (eval_term (lb a) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
        eval_term (ub a) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R).
intros.
simpl in *.
tlaIntuition.
Qed.
        
  

Lemma fold_right_combine : forall tr lst a x,   fold_right
         (fun (triple : singleBoundTerm) (prop : Prop) =>
          prop //\\
          (eval_formula (premise triple) tr ->
           (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
            eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True lst //\\ 
             (eval_formula (premise a) tr ->
       (eval_term (lb a) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
        eval_term (ub a) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R) ->   fold_right (fun (triple : singleBoundTerm) (prop : Prop) =>
          prop //\\
          (eval_formula (premise triple) tr ->
           (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
            eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True (a::lst).

intros.
simpl in *.
intuition.
Qed.

Lemma fold_right_combine_opp :   forall tr lst a x,  fold_right (fun (triple : singleBoundTerm) (prop : Prop) =>
          prop //\\
          (eval_formula (premise triple) tr ->
           (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
            eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True (a::lst) -> fold_right
         (fun (triple : singleBoundTerm) (prop : Prop) =>
          prop //\\
          (eval_formula (premise triple) tr ->
           (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
            eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True lst //\\ 
             (eval_formula (premise a) tr ->
       (eval_term (lb a) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
        eval_term (ub a) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R).
intros.
simpl in *.
intuition.
Qed.


Lemma fold_right_inferr_sublist : forall lst1 lst2 tr x, fold_right
        (fun (triple : singleBoundTerm) (prop : Prop) =>
         prop //\\
         (eval_formula (premise triple) tr ->
          (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
           eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True
        (lst1 ++ lst2) -> fold_right
     (fun (triple : singleBoundTerm) (prop : Prop) =>
      prop //\\
      (eval_formula (premise triple) tr ->
       (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
        eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True lst2 //\\ fold_right
     (fun (triple : singleBoundTerm) (prop : Prop) =>
      prop //\\
      (eval_formula (premise triple) tr ->
       (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
        eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True lst1.
  breakAbstraction.
  intros.
split.
induction lst1.
simpl in *.
tlaIntuition.
rewrite firstappend in H.
apply fold_right_subList_inferring in H.
breakAbstraction.
destruct H.
simpl in *.
apply IHlst1 in H.
intuition.
induction lst1.
simpl.
intuition.
rewrite firstappend in H.
apply fold_right_subList_inferring in H.
apply fold_right_combine.
breakAbstraction.
decompose [and] H.
intuition.
Qed.



 


Lemma fold_right_two_list :forall lst1 lst2 x tr, 
                      fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop //\\
                (eval_formula (premise triple) tr ->
                 (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
                  eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True
               (lst1 ++ lst2) ->   (fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop //\\
                (eval_formula (premise triple) tr ->
                 (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
                  eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True
               lst1) //\\ (fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop //\\
                (eval_formula (premise triple) tr ->
                 (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
                  eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True
               lst2) .
  breakAbstraction.
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
destruct H.
apply IHlst1 in H.
simpl.
intuition.
apply fold_right_inferr_sublist in H.
breakAbstraction.
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
                prop //\\
                (eval_formula (premise triple) tr ->
                 (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
                  eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True
               lst1) //\\ (fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop //\\
                (eval_formula (premise triple) tr ->
                 (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
                  eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True
               lst2) -> fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop //\\
                (eval_formula (premise triple) tr ->
                 (eval_term (lb triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)) <= x <=
                  eval_term (ub triple) (Stream.hd tr) (Stream.hd (Stream.tl tr)))%R)) True
               (lst1 ++ lst2).
  breakAbstraction.
  intros.
  decompose [and] H.
  induction lst1.
  simpl in *.
  intuition.
  rewrite  list3Commutative.
  apply fold_right_combine.
  apply fold_right_subList_inferring in H0.
  breakAbstraction.
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


Definition validFloat (f : binary_float custom_prec custom_emax) : Prop :=
  exists r, Some r = floatToReal f.


Print Floats.float.
Lemma resultImplicationsPlus : 
        forall (f : float) (expr1 expr2 : NowTerm) (fState : fstate),  
         (Some f =  lift2 (Bplus custom_prec custom_emax 
                                 custom_precGt0 custom_precLtEmax custom_nan mode_NE) 
                          (eval_NowTerm fState expr1)
                          (eval_NowTerm fState expr2)) ->
         validFloat f ->
         exists (f1 f2:float),
           Some f1 = eval_NowTerm fState expr1
           //\\ Some f2 = eval_NowTerm fState expr2
                                       //\\ validFloat f1 //\\ validFloat f2.
  breakAbstraction.
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

Lemma resultImplicationsMult : 
        forall (f : float) (expr1 expr2 : NowTerm) (fState : fstate),  
         (Some f =  lift2 (Bmult custom_prec custom_emax 
                                 custom_precGt0 custom_precLtEmax custom_nan mode_NE) 
                          (eval_NowTerm fState expr1)
                          (eval_NowTerm fState expr2)) ->
         validFloat f ->
         exists (f1 f2:float),
           Some f1 = eval_NowTerm fState expr1
           //\\ Some f2 = eval_NowTerm fState expr2
                                       //\\ validFloat f1 //\\ validFloat f2.
  breakAbstraction.
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
        inversion H.
        rewrite H2 in H0.
        simpl in *.

        inversion H0.
        apply H0.
        inversion H.
        rewrite H2 in H0.
        simpl in *.
        apply H0.
        inversion H.
        rewrite H2 in H0.
        simpl in *.
        apply H0.
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
        clear H.
        remember (F2R {| Fnum := cond_Zopp b (Z.pos m); Fexp := e |}) as r2.
        exists r2.
        reflexivity.
      }
      {
        destruct f1 eqn:f1_des.
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
          inversion H.
          rewrite H2 in H0.
          apply H0.
          simpl in *.
          inversion H.
          rewrite H2 in H0.
          unfold validFloat in *.
          simpl in *.
          apply H0.
          inversion H.
          rewrite H2 in H0.
          unfold validFloat in *.
          simpl in *.
          apply H0.
        }
        {
          inversion H.
          destruct f0.
          unfold Bmult in H2.
          simpl in *.

          simpl in *.
          rewrite H2 in H0.
          unfold validFloat in *.
          simpl in *.
          apply H0.
          simpl in *.
          rewrite H2 in H0.
          unfold validFloat in *.
          simpl in *.
          apply H0.
          rewrite H2 in H0.
          unfold validFloat in *.
          simpl in *.
          apply H0.
          rewrite H2 in H0.
          unfold validFloat in *.
          simpl in *.
          apply H0.
        }
        {
          destruct f0 eqn:f0_des.
          unfold validFloat.
          inversion H0.
          simpl in *.
          clear H.
          remember (F2R {| Fnum := cond_Zopp b (Z.pos m); Fexp := e |}) as r.
          exists r.
          reflexivity.
          simpl in *.
          inversion H.
          rewrite H2 in H0.
          unfold validFloat in *.
          simpl in *.
          inversion H0.
          inversion H1.
          inversion H.
          rewrite H2 in H0.
          unfold validFloat in *.
          inversion H0.
          simpl in *.
          inversion H1.
          simpl in *.
          unfold validFloat.
          simpl in *.
          clear H.
          remember (F2R {| Fnum := cond_Zopp b (Z.pos m); Fexp := e |}) as r.
          exists r.
          reflexivity.
        }
      }
    }
    inversion H.
  }
  inversion H.
Qed.

Lemma resultImplicationsMinus : 
        forall (f : float) (expr1 expr2 : NowTerm) (fState : fstate),  
         (Some f =  lift2 (Bminus custom_prec custom_emax 
                                 custom_precGt0 custom_precLtEmax custom_nan mode_NE) 
                          (eval_NowTerm fState expr1)
                          (eval_NowTerm fState expr2)) ->
         validFloat f ->
         exists (f1 f2:float),
           Some f1 = eval_NowTerm fState expr1
           //\\ Some f2 = eval_NowTerm fState expr2
                                       //\\ validFloat f1 //\\ validFloat f2.
  breakAbstraction.
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
  breakAbstraction.
  pose proof custom_precGt0.
  pose proof custom_precLtEmax.
  unfold Fcore_FLX.Prec_gt_0 in *.
  unfold custom_prec, custom_emax in *.
  unfold Valid_exp,custom_prec,custom_emax.
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

Lemma validFloat2 : forall (f1:float) (r:R), Some r = floatToReal f1 -> r = B2R custom_prec custom_emax f1.   
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


Definition choiceDef := (fun x => negb (Zeven x)).

(* commenting this for now - since we are abstracting the float type 
Lemma precThm: (forall k : Z, (-1021 < k)%Z -> (custom_prec <= k - FLT_exp (3-custom_emax - custom_prec) custom_prec k)%Z).
  intros.
  unfold custom_emax in *. unfold custom_prec in *. unfold FLT_exp. unfold custom_emin in *. 
  unfold Z.max.
  pose proof Z_lt_ge_dec ((k - 53)%Z) ((3 - 1024 - 53)%Z).
  pose (k - 53 ?= 3 - 1024 - 53)%Z.
  Print Datatypes.Eq.
  Search (_ -> Datatypes.comparison).
  Print Cge.
  destruct H0 eqn:H0_des. 
  destruct (k - 53 ?= 3 - 1024 - 53)%Z eqn:des.
  lia.  simpl in *. 
c  clear des.
  simpl in *.
  lia. 
  lia.
  destruct ( k - 53 ?= 3 - 1024 - 53)%Z.
  lia.
  lia.
  lia.
  
Qed.
*)
Lemma floatValid : forall (r:R) (f:float), Some r = floatToReal f -> is_finite _ _ f = true .
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










Lemma posZ: forall p, (P2R p > 0)%R.
  intros.
  unfold P2R.
  induction p.
  destruct p.
  remember ( match p with
             | (_~1)%positive =>
               1 +
               2 *
               (fix P2R (p1 : positive) : R :=
                  match p1 with
                  | ((_~1 as t)~1)%positive => 1 + 2 * P2R t
                  | ((_~0 as t)~1)%positive => 1 + 2 * P2R t
                  | 3%positive => 3
                  | ((_~1 as t)~0)%positive => 2 * P2R t
                  | ((_~0 as t)~0)%positive => 2 * P2R t
                  | 2%positive => 2
                  | 1%positive => 1
                  end) p
             | (_~0)%positive =>
               1 +
               2 *
               (fix P2R (p1 : positive) : R :=
                  match p1 with
                  | ((_~1 as t)~1)%positive => 1 + 2 * P2R t
                  | ((_~0 as t)~1)%positive => 1 + 2 * P2R t
                  | 3%positive => 3
                  | ((_~1 as t)~0)%positive => 2 * P2R t
                  | ((_~0 as t)~0)%positive => 2 * P2R t
                  | 2%positive => 2
                  | 1%positive => 1
                  end) p
             | 1%positive => 3
             end)%R as des.
  clear Heqdes.
  psatz R.
  remember (match p with
            | (_~1)%positive =>
              2 *
              (fix P2R (p1 : positive) : R :=
                 match p1 with
                 | ((_~1 as t)~1)%positive => 1 + 2 * P2R t
                 | ((_~0 as t)~1)%positive => 1 + 2 * P2R t
                 | 3%positive => 3
                 | ((_~1 as t)~0)%positive => 2 * P2R t
                 | ((_~0 as t)~0)%positive => 2 * P2R t
                 | 2%positive => 2
                 | 1%positive => 1
                 end) p
            | (_~0)%positive =>
              2 *
              (fix P2R (p1 : positive) : R :=
                 match p1 with
                 | ((_~1 as t)~1)%positive => 1 + 2 * P2R t
                 | ((_~0 as t)~1)%positive => 1 + 2 * P2R t
                 | 3%positive => 3
                 | ((_~1 as t)~0)%positive => 2 * P2R t
                 | ((_~0 as t)~0)%positive => 2 * P2R t
                 | 2%positive => 2
                 | 1%positive => 1
                 end) p
            | 1%positive => 2
            end )%R as des.
  psatz R.
  psatz R.

  destruct p.
  remember (match p with
            | (_~1)%positive =>
              1 +
              2 *
              (fix P2R (p1 : positive) : R :=
                 match p1 with
                 | ((_~1 as t)~1)%positive => 1 + 2 * P2R t
                 | ((_~0 as t)~1)%positive => 1 + 2 * P2R t
                 | 3%positive => 3
                 | ((_~1 as t)~0)%positive => 2 * P2R t
                 | ((_~0 as t)~0)%positive => 2 * P2R t
                 | 2%positive => 2
                 | 1%positive => 1
                 end) p
            | (_~0)%positive =>
              1 +
              2 *
              (fix P2R (p1 : positive) : R :=
                 match p1 with
                 | ((_~1 as t)~1)%positive => 1 + 2 * P2R t
                 | ((_~0 as t)~1)%positive => 1 + 2 * P2R t
                 | 3%positive => 3
                 | ((_~1 as t)~0)%positive => 2 * P2R t
                 | ((_~0 as t)~0)%positive => 2 * P2R t
                 | 2%positive => 2
                 | 1%positive => 1
                 end) p
            | 1%positive => 3
            end)%R as des.
  psatz R.
  remember (match p with
            | (_~1)%positive =>
              2 *
              (fix P2R (p1 : positive) : R :=
                 match p1 with
                 | ((_~1 as t)~1)%positive => 1 + 2 * P2R t
                 | ((_~0 as t)~1)%positive => 1 + 2 * P2R t
                 | 3%positive => 3
                 | ((_~1 as t)~0)%positive => 2 * P2R t
                 | ((_~0 as t)~0)%positive => 2 * P2R t
                 | 2%positive => 2
                 | 1%positive => 1
                 end) p
            | (_~0)%positive =>
              2 *
              (fix P2R (p1 : positive) : R :=
                 match p1 with
                 | ((_~1 as t)~1)%positive => 1 + 2 * P2R t
                 | ((_~0 as t)~1)%positive => 1 + 2 * P2R t
                 | 3%positive => 3
                 | ((_~1 as t)~0)%positive => 2 * P2R t
                 | ((_~0 as t)~0)%positive => 2 * P2R t
                 | 2%positive => 2
                 | 1%positive => 1
                 end) p
            | 1%positive => 2
            end)%R as des.
  psatz R.
  psatz R.
  intuition.
Qed.




Lemma RtoZ: forall z, (Z2R z > 0)%R <-> (z > 0)%Z. 
  split.
  intros.
  compute in *.
  induction z.
  psatz R.
  reflexivity.
  pose proof posZ.
  specialize (H0 p).
  unfold P2R in *.
  psatz R.

  intros.
  induction z.
  intuition.
  unfold Z2R.
  apply posZ.
  unfold Z2R.
  specialize (posZ p).
  intros.
  lia.
Qed.


Lemma RtoZgt1: forall z, (Z2R z >= 1)%R <-> (z >= 1)%Z. 
  split.
  {
    intros.
    compute.
    induction z.
    {
      compute in H.
      psatz R.
    }
    {
      destruct p.
      {
        intros.
        inversion H0.
      }
      {
        intros.
        inversion H0.
      }
      {
        intros.
        inversion H0.
      }
    }
    {
      
      unfold Z2R in *.
      pose proof posZ as posZ.
      specialize (posZ p).
      psatz R.
    }
  }    
  
{
  intros.
  induction z.
    { lia. }
    { unfold Z2R.
      unfold P2R.
      destruct p eqn:des.
      {
        remember ((fix P2R (p2 : positive) : R :=
                     match p2 with
                     | ((_~1 as t)~1)%positive => 1 + 2 * P2R t
                     | ((_~0 as t)~1)%positive => 1 + 2 * P2R t
                     | 3%positive => 3
                     | ((_~1 as t)~0)%positive => 2 * P2R t
                     | ((_~0 as t)~0)%positive => 2 * P2R t
                     | 2%positive => 2
                     | 1%positive => 1
                     end) p0)%R as pr.
        Lemma P2Rgt0: forall p0, (((fix P2R (p2 : positive) : R :=
                                      match p2 with
                                      | ((_~1 as t)~1)%positive => 1 + 2 * P2R t
                                      | ((_~0 as t)~1)%positive => 1 + 2 * P2R t
                                      | 3%positive => 3
                                      | ((_~1 as t)~0)%positive => 2 * P2R t
                                      | ((_~0 as t)~0)%positive => 2 * P2R t
                                      | 2%positive => 2
                                      | 1%positive => 1
                                      end) p0) >= 1)%R.
          intros.
          induction p0.
          {
            remember  ((fix P2R (p2 : positive) : R :=
                          match p2 with
                          | ((_~1 as t)~1)%positive => 1 + 2 * P2R t
                          | ((_~0 as t)~1)%positive => 1 + 2 * P2R t
                          | 3%positive => 3
                          | ((_~1 as t)~0)%positive => 2 * P2R t
                          | ((_~0 as t)~0)%positive => 2 * P2R t
                          | 2%positive => 2
                          | 1%positive => 1
                          end) p0)%R as pr. 
            destruct p0.
            psatz R.
            psatz R.
            psatzl R.
          }
          {
            remember  ((fix P2R (p2 : positive) : R :=
                          match p2 with
                          | ((_~1 as t)~1)%positive => 1 + 2 * P2R t
                          | ((_~0 as t)~1)%positive => 1 + 2 * P2R t
                          | 3%positive => 3
                          | ((_~1 as t)~0)%positive => 2 * P2R t
                          | ((_~0 as t)~0)%positive => 2 * P2R t
                          | 2%positive => 2
                          | 1%positive => 1
                          end) p0)%R as pr.
            destruct p0.
            psatz R.
            psatz R.
            psatz R.
          }
          psatz R.
        Qed.
        intros.
        pose proof P2Rgt0 as P2Rgt0.
        specialize (P2Rgt0 p0).
        rewrite <- Heqpr in P2Rgt0.
        destruct p0 eqn:p0_des. 
        {
          psatz R.
        }
        {
          psatz R.
        }
        {
          clear H des pr Heqpr P2Rgt0.
          psatzl R.
        }
      }
      {
        remember ((fix P2R (p2 : positive) : R :=
                     match p2 with
                     | ((_~1 as t)~1)%positive => 1 + 2 * P2R t
                     | ((_~0 as t)~1)%positive => 1 + 2 * P2R t
                     | 3%positive => 3
                     | ((_~1 as t)~0)%positive => 2 * P2R t
                     | ((_~0 as t)~0)%positive => 2 * P2R t
                     | 2%positive => 2
                     | 1%positive => 1
                     end) p0)%R as pr.
        pose proof P2Rgt0 as P2Rgt0.
        specialize (P2Rgt0 p0).
        rewrite <- Heqpr in P2Rgt0.
        destruct p0 eqn:p0_des. 
        {
          psatz R.
        }
        {
          psatz R.
        }
        {
          clear H des pr Heqpr P2Rgt0.
          psatzl R.
        }
        
      }
      intuition.
    }
    lia.
  }
Qed.


Lemma powLe1 : forall (pow:Z), (pow <= 0)%Z -> (bpow radix2 pow <=1)%R.
intros.
unfold bpow.
destruct pow eqn:pow_des.
psatzl R.
lia.
pose proof RtoZgt1.
Lemma inverse: forall p:positive, (Z.neg p <= 0)%Z -> (Z2R (Z.pow_pos radix2 p) >= 1)%R.
intros. apply RtoZgt1.
unfold Z.pow_pos.
pose proof Pos.iter_invariant.
specialize (H0 p Z).
simpl.
specialize (H0 (Z.mul 2)).
specialize (H0 (fun z => z>=1 )%Z).
Lemma negToPos : forall p:positive, (Zneg p <= -1)%Z <-> (p >= 1)%positive.
split;lia. Qed.
pose proof negToPos as negToPos.

Lemma inverseTemp: (forall x : Z, (fun z:Z => (z >= 1)%Z) x -> 
(fun z:Z => (z>=1)%Z) (2*x) %Z).
intros.
simpl in *.
destruct x.
lia.
lia. 
lia.
Qed.

intros.
specialize (H0 inverseTemp).
specialize (H0 1%Z).
Lemma inverseTemp2: ((fun z : Z => (z >= 1)%Z) 1%Z). 
simpl.
intuition.
Qed.
intros.
specialize (H0 inverseTemp2).
simpl in H0.
lia.
Qed.
intros.
pose proof inverse.
specialize (H1 p H).
clear  pow_des H H0.
 repeat match goal with
          | H : @eq R _ _ |- _ => revert H
          | H : @Rle _ _ |- _ => revert H
          | H : @Rge _ _ |- _ => revert H
          | H : @Rlt _ _ |- _ => revert H
          | H :@ Rgt _ _ |- _ => revert H
          | H : @Rge _ _ |- _ => revert H
        end.

generalize (Z2R (Z.pow_pos radix2 p)).
Require Import ArithFacts.
pose proof Rmult_le_algebra.
intros.
specialize (Rmult_le_algebra 1 r 1).
rewrite Rmult_1_l.
intros.
psatzl R.
Qed.


Lemma errorLessThan1: (error <= 1)%R.
  unfold error.
  pose proof custom_precGe1.
  Lemma OneMinus : forall x:Z, (x >= 1 -> 1-x <= 0)%Z. 
    intros.
    lia.
  Qed.
  intros.
  pose proof OneMinus.
  apply H0 in H.
Lemma minus: forall x, (1- x = -x +1 ) %Z. 
intros.
lia.
Qed.
intros.
specialize (minus custom_prec).
intros.
rewrite <- H1.
remember (1 - custom_prec)%Z as x.
specialize (powLe1 x H).
intuition.
Qed.
Lemma powGt0 : forall pow,   (bpow radix2 pow > 0)%R.
Proof.
  intros.
  destruct (pow)%Z eqn:pow_des.
  {
    intuition.
  }
  {
    Lemma proveZPos : forall p, (Z2R (Z.pow_pos radix2 p) > 0)%R.
      Proof.
        intros.
        unfold Z.pow_pos.
        apply RtoZ.
        simpl.
        SearchAbout Pos.iter.
        pose proof Pos.iter_invariant.
        specialize (H p Z).
        specialize (H (Z.mul 2)).
        specialize (H (fun x => (x > 0)%Z)).
        Lemma multiplyBy2 : (forall x : Z, (fun x0 : Z => (x0 > 0)%Z) x -> (fun x0 : Z => (x0 > 0)%Z) (2 * x)%Z).
        Proof.
          intros.
          simpl in *.
          destruct x.
          apply H.
          lia.
          lia.
        Qed.

        specialize (H multiplyBy2).
        specialize (H 1%Z).  
        simpl in *.
        Lemma OneGt0 : (1 > 0)%Z.
        Proof.
          lia.
        Qed.
        specialize (H OneGt0).
        apply H.
      Qed.
      intros.

      apply proveZPos.
  }
  {
    apply Rinv_0_lt_compat.
    apply proveZPos.
  }
Qed.



Lemma errorGt0 : (error > 0)%R.
Proof.  
  unfold error. 
  apply powGt0.
Qed.


Lemma floatMinGt0 : (floatMin > 0)%R.
Proof.
  unfold floatMin.
  apply powGt0.
Qed.

Lemma floatMaxGt0 : (floatMax > 0)%R.
Proof.
  unfold floatMin.
  apply powGt0.
Qed.


Lemma absoluteValGe : forall (r1 r2:R) , 
                (Rabs r1 >= r2 -> r1 >= r2 \\// -r1 >= r2)%R. 
            Proof.
              intros.
              unfold Rabs in *. simpl.
              destruct Rcase_abs; psatz R.
            Qed.
            
Lemma absoluteValLt : forall (r1 r2:R) , 
                (Rabs r1 < r2 -> r1 < r2 \\// -r1 < r2)%R. 
Proof.
  intros.
  unfold Rabs in *. simpl.
  destruct Rcase_abs; psatz R. 
Qed.





Declare ML Module "z3Tactic".
(*((ub2 >= lb1) //\\ 
      (ub1 >= lb2) //\\ 
      (((ub1 - ub2 >= floatMin) //\\ (lb1 - lb2 >=floatMin) //\\ (ub2 - lb1 >= floatMin)) \\//
       ((ub2 - ub1 >= floatMin) //\\ (lb1 - lb2 >=floatMin)) \\//
       ((ub1 - ub2 >= floatMin) //\\ (lb2 - lb1 >= floatMin)) \\//
       ((ub2 - ub1 >=floatMin) //\\ (ub1 - lb2 >=floatMin) //\\ (lb2 - lb1 >= floatMin)) ))*)
Lemma minusfloatMinBoundProof:  forall (x1 x2 lb1 lb2 ub1 ub2:R), 
    (((lb1 >= ub2) //\\ (floatMin <= lb1 - ub2)) \\// 
     ((ub1 <= lb2) //\\(floatMin <= lb2 - ub1))
    -> 
  lb1 <= x1 -> lb2 <= x2 -> x1 <= ub1 -> x2 <= ub2 -> (Rabs (x1 - x2) >= floatMin))%R. 
Proof.
breakAbstraction.
intros.
pose proof floatMinGt0.
unfold Rabs.  
destruct Rcase_abs.
destruct H. simpl in H.
psatz R.
destruct H.
decompose [and] H.
clear H.
(*z3Tactic*)

psatz R.
destruct H.
decompose [and] H.
clear H.
clear -H6 H0 H3.
psatz R.
decompose [and] H.
clear H.
clear -H6 r H4 H1 H2.
psatz R.
Qed.

Lemma plusfloatMinBoundProof:  forall (x1 x2 lb1 lb2 ub1 ub2:R), ((floatMin <= lb1 + lb2) \\// (floatMin <= 0 - ub1 + (0 - ub2)) -> lb1 <= x1 -> lb2 <= x2 -> x1 <= ub1 -> x2 <= ub2 -> (Rabs (x1 + x2) >= floatMin))%R. 
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


Lemma multfloatMinBoundProof:  forall (x1 x2 lb1 lb2 ub1 ub2:R), 
    (((floatMin <= lb1 * lb2) //\\  (lb1 >= R0) //\\ (lb2 >= R0))
    \\// (floatMin <= (0 - ub1) * (0 - ub2) //\\ (ub1 < R0) //\\ (ub2 < R0)) 
    \\// (floatMin <= lb1 * (0 - ub2) //\\ (lb1 >= R0) //\\  (ub2 < R0)) 
    \\// (floatMin <= (0 - ub1) * lb2 //\\ (ub1 < R0) //\\  (lb2 >= R0)) -> lb1 <= x1 -> lb2 <= x2 -> x1 <= ub1 -> x2 <= ub2 -> (Rabs (x1 * x2) >= floatMin))%R. 
Proof.
  breakAbstraction.
  intros;
  pose proof floatMinGt0;
  unfold Rabs;
  destruct Rcase_abs;
  destruct H;
  psatz R.
Qed.


Lemma lbAndUbSumIsZero : forall (lb1 lb2 ub1 ub2 x1 x2: R), ((lb1 + lb2)%R = 0%R //\\ (ub1 + ub2)%R = 0%R) ->  (lb1 <= x1 <= ub1)%R ->  (lb2 <= x2 <= ub2)%R -> (x1 + x2 = 0)%R.
Proof.
  breakAbstraction.
  intros.
  decompose [and] H.
  destruct H0.
  destruct H1.
  clear H.
  psatz R.
Qed.

Lemma relErrorBasedOnFloatMinTruthMult : forall (x1 x2 lb1 lb2 ub1 ub2:R), 
    ((((floatMin <= lb1 * lb2) //\\  (lb1 >= R0) //\\ (lb2 >= R0)) 
\\// (floatMin <= (0 - ub1) * (0 - ub2) //\\ (ub1 < R0) //\\ (ub2 < R0))
\\// (floatMin <= lb1 * (0 - ub2) //\\ (lb1 >= R0) //\\  (ub2 < R0)) 
\\// (floatMin <= (0 - ub1) * lb2 //\\ (ub1 < R0) //\\  (lb2 >= R0)))
 -> 
lb1 <= x1 -> lb2 <= x2 -> x1 <= ub1 -> x2 <= ub2 ->  
(Rabs (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (x1 * x2) - (x1 * x2)) < 
 bpow radix2 (- custom_prec + 1) * Rabs (x1 * x2)))%R.
Proof.
  breakAbstraction.
  intros.
  pose proof relative_error as Rel_Err.
(* 


(Rabs
                (round radix2 (Fcore_FLX.FLX_exp custom_prec)
                   (Znearest choiceDef) (x1 * x2) - 
                 x1 * x2) <=
              / 2 * bpow radix2 (- custom_prec + 1) * Rabs (x1 * x2))%R*)
  unfold round_mode.
  unfold FLT_exp.
  unfold Fcore_FLX.FLX_exp in *.
  remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp. 
  specialize (Rel_Err radix2 round_fexp).
  Check relative_error.
  subst.
  specialize (Rel_Err validFexpProof (custom_emin)%Z custom_prec precThm (round_mode mode_NE)). 
  specialize (Rel_Err (valid_rnd_N choiceDef)).
  pose proof multfloatMinBoundProof as multfloatMinBoundProof.
  specialize (multfloatMinBoundProof x1 x2 lb1 lb2 ub1 ub2).
  specialize (multfloatMinBoundProof H H0 H1 H2 H3).
  specialize (Rel_Err (x1*x2)%R).
  unfold floatMin in *.
  apply Rge_le in multfloatMinBoundProof.
  specialize (Rel_Err multfloatMinBoundProof).
  apply Rel_Err.
Qed.
Lemma relErrorBasedOnFloatMinTruthMinus : forall (x1 x2 lb1 lb2 ub1 ub2:R), 
(((lb1 >= ub2)  //\\  (floatMin <= lb1 - ub2)) 
\\// ((ub1 <= lb2) //\\(floatMin <= lb2 - ub1)) -> 
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

Lemma relErrorBasedOnFloatMinTruthPlus2 : forall (x1 x2 lb1 lb2 ub1 ub2:R), (lb1 <= x1 -> 
      lb2 <= x2 -> 
      x1 <= ub1 -> 
      x2 <= ub2 ->  (Rabs
                (round radix2 (Fcore_FLX.FLX_exp custom_prec)
                   (Znearest choiceDef) (x1 + x2) - 
                 (x1 + x2)) <=
              / 2 * bpow radix2 (- custom_prec + 1) * Rabs (x1 + x2)))%R.
Proof.
  intros.
  pose proof relative_error_N_FLX as Rel_Err.
  specialize (Rel_Err radix2 custom_prec custom_precGt0 choiceDef (x1+x2)%R).
  apply Rel_Err.
Qed.
Lemma relErrorBasedOnFloatMinTruthPlus : forall (x1 x2 lb1 lb2 ub1 ub2:R), 
    (
      (floatMin <= lb1 + lb2)  
      \\// (floatMin <= 0 - ub1 + (0 - ub2)) -> 
      lb1 <= x1 -> 
      lb2 <= x2 -> 
      x1 <= ub1 -> 
      x2 <= ub2 ->  
      (Rabs 
         (round 
            radix2 (FLT_exp 
                      (3 - custom_emax - custom_prec) 
                      custom_prec
                   ) 
            (round_mode mode_NE) 
            (x1 + x2) - (x1 + x2)
         )
       < bpow radix2 (- custom_prec + 1) * Rabs (x1 + x2))
    )%R.
Proof.
  intros.
  pose proof relative_error as Rel_Err.
  pose proof relative_error_N_FLX as Rel_Err2.
  specialize (Rel_Err2 radix2 custom_prec custom_precGt0 choiceDef (x1+x2)%R).
  
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


Lemma minusRoundingTruth : forall (f1 f2:float)  (lb1 lb2 ub1 ub2 r1 r2:R),  (Some r1 = (floatToReal f1) -> 
                                                                              Some r2 = (floatToReal f2) ->
                                                                              ( (((lb1 >= ub2)  //\\  (floatMin <= lb1 - ub2)) //\\  ((ub1 - lb2)*(1+error) < floatMax)) \\// 
                                                                                (((ub1 <= lb2)  //\\  (floatMin <= lb2 - ub1)) //\\  ((ub2 - lb1)*(1+error) < floatMax)) 
                                                                              ) ->
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
                           ((p1 //\\ p2) //\\ p3) \\// ((p4 //\\ p5) //\\ p6) -> (p1 //\\ p2 ) \\// (p4 //\\ p5).
        tlaIntuition.
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
    pose proof floatMinGt0.

    clear H7.
    breakAbstraction.
    destruct Rcase_abs;
      destruct Rcase_abs;
      destruct Rcase_abs; destruct H1';
      unfold error in *; unfold floatMax in *;
    (* very slow; admitted for now -- Mario *)
    (* psatz R. *)
    admit.
    
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
    remember ((B2R custom_prec custom_emax (B754_zero custom_prec custom_emax b0))) as arg2.
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
    pose proof floatMinGt0.
    clear H Heqarg2 H0 H8 H7.
    unfold error in *.
    unfold custom_prec,custom_emax in *.
    destruct Rcase_abs;
      destruct Rcase_abs; 
      destruct Rcase_abs; 
      unfold floatMax,custom_prec,custom_emax in *;
     admit.
      (*psatz R.*)
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
    pose proof floatMinGt0.
    clear r1Value.
    clear r2Value.
    
    destruct Rcase_abs;
      destruct Rcase_abs;
      destruct Rcase_abs;
      unfold error,floatMax in *;
      (*psatz R.*)
      admit.
  }    
Qed.  
  Lemma abs: forall x y, (x >= y \\// x <= (0-y) -> y <= Rabs x)%R.
  Proof.
    breakAbstraction.
    intros.
    admit.
(*          destruct H;unfold Rabs;destruct Rcase_abs; breakAbstraction; psatz R;psatz R. *)
        Qed.

        Lemma orExtra : forall (p1 p2:Prop), p1 -> p1 \\// p2.
          breakAbstraction.
        intros.
        intuition.
      Qed.
Lemma plusRoundingTruth3 : forall (f1 f2: float)  (lb1 lb2 ub1 ub2 x1 x2:R), 
    (
      Some x1 = (floatToReal f1) -> 
      Some x2 = (floatToReal f2) ->
      (
        x1 + x2 >= floatMin \\// x1 + x2 <= (0-floatMin)
      ) ->
      lb1 <= x1 ->
      lb2 <= x2 ->
      (ub1 + ub2)*(1+error ) < floatMax -> 
      (0 - lb1 + (0 - lb2))* (1+error) < floatMax ->
      x1 <= ub1 ->
      x2 <= ub2 ->
      (
        (
          Rabs 
            (round 
               radix2 
               (FLT_exp 
                  (3-custom_emax- custom_prec) 
                  custom_prec) 
               (round_mode mode_NE) 
               (B2R custom_prec custom_emax f1 
                + B2R custom_prec custom_emax f2))
        ) 
        <  (bpow radix2 custom_emax)
      )
    )%R.
Proof.
  intros.
  unfold floatToReal in *.

 (*getting the relative error proof*)
  remember (x1 + x2)%R as realResult. 
  pose proof relative_error.
  remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp.
  

  specialize (H8 radix2 round_fexp). 
  rewrite Heqround_fexp in H8.
  specialize (H8 validFexpProof  (custom_emin)%Z custom_prec  precThm (round_mode mode_NE)).
  specialize (H8 (valid_rnd_N choiceDef) (x1+x2)%R).
  
  intros.
  pose proof abs as absProof.
  specialize (absProof realResult floatMin H1).
  rewrite HeqrealResult in absProof.
  unfold floatMin in absProof.
  specialize (H8 absProof).
  clear absProof.
  rewrite HeqrealResult in *.
  rewrite Heqround_fexp.
  clear HeqrealResult round_fexp Heqround_fexp.
  (*getting the relative error proof*)
  destruct f1.
  {
    destruct f2. 
    {
      inversion H.
      inversion H0.
      

      Check relErrorBasedOnFloatMinTruthPlus.
      unfold B2R in *.
      unfold Rabs in *.
      pose proof errorGt0 as errorGt0.
      remember  (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) 
                       (round_mode mode_NE) (0 + 0)) as roundedValue.
      clear HeqroundedValue.
      clear H H0.
      pose proof floatMaxGt0.
      pose proof floatMinGt0.
      clear H1.
      unfold error in *.
      unfold floatMax in *.
      breakAbstraction.
      (*
      destruct Rcase_abs; destruct Rcase_abs; destruct Rcase_abs;
      psatz R.
       *)
      admit.
    }
    inversion H0.
    inversion H0.
    inversion H.
    inversion H0.
    rewrite H10 in *.
    unfold B2R in *.
    unfold Rabs in *.
    pose proof errorGt0 as errorGt0.
    rewrite <- H11 in *.
    remember  (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) 
                     (round_mode mode_NE) (0  + x2)) as roundedValue.
    clear HeqroundedValue.
    clear H10.
    clear H H0.
    pose proof floatMaxGt0.
    pose proof floatMinGt0.
    clear H1.
    clear H11.

    (*
    destruct Rcase_abs; destruct Rcase_abs; destruct Rcase_abs;
    unfold error in *;
    unfold floatMax in *;
    psatz R.
*)
    
    admit.
  }
  inversion H0.
  inversion H.
  inversion H.
  
  destruct f2.
  

  inversion H.
  inversion H0.
  unfold B2R in *.
  rewrite H11 in *.
  rewrite <- H10 in *.
  unfold Rabs in *.
  pose proof errorGt0 as errorGt0.
  unfold error in *.
  remember  (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) 
                   (round_mode mode_NE) (x1 + 0)) as roundedValue.
  clear HeqroundedValue.
  clear H11 H10.
  clear H H0.
  pose proof floatMaxGt0.
  pose proof floatMinGt0.
  clear H1.
  admit.
  (*
  destruct Rcase_abs; destruct Rcase_abs; destruct Rcase_abs;
  unfold error in *;
  unfold floatMax in *;
  psatz R.
   *)

  inversion H0.
  inversion H0.

  inversion H.
  inversion H0.
  unfold B2R in *.
  rewrite <- H10 in *.
  rewrite <- H11 in *.
  unfold Rabs in *.
  pose proof errorGt0 as errorGt0.
  unfold error in *.
  remember  (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) 
                   (round_mode mode_NE) (x1 + x2)) as roundedValue.
  clear HeqroundedValue.
  clear H11 H10.
  clear H H0.
  pose proof floatMaxGt0.
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



Lemma plusRoundingTruth : forall (f1 f2: float)  (lb1 lb2 ub1 ub2 r1 r2:R), 
    
    (
      Some r1 = (floatToReal f1) -> 
      Some r2 = (floatToReal f2) ->
      (
        (floatMin <= lb1 + lb2) \\// 
        (floatMin <= 0 - ub1 + (0 - ub2))
      ) ->
      lb1 <= r1 ->
      lb2 <= r2 ->
      (ub1 + ub2)*(1+error ) < floatMax -> 
      (0 - lb1 + (0 - lb2))* (1+error) < floatMax ->
      r1 <= ub1 ->
      r2 <= ub2 ->
      (
        (
          Rabs 
            (round 
               radix2 
               (FLT_exp 
                  (3-custom_emax- custom_prec) 
                  custom_prec) 
               (round_mode mode_NE) 
               (B2R custom_prec custom_emax f1 
                + B2R custom_prec custom_emax f2))
        ) 
        <  (bpow radix2 custom_emax)
      )
    )%R.
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
    


Lemma multRoundingTruth : forall (f1 f2: float)  (lb1 lb2 ub1 ub2 r1 r2:R),  (Some r1 = (floatToReal f1) -> 
    Some r2 = (floatToReal f2) ->
    
    (((floatMin <= lb1 * lb2) //\\  (lb1 >= R0) //\\ (lb2 >= R0)) //\\ ((ub1 * ub2)*(1+error) < floatMax)) 

    \\// ((floatMin <= (0 - ub1) * (0 - ub2) //\\ (ub1 < R0) //\\ (ub2 < R0)) //\\ (((0 - lb1) * (0 - lb2))*(1+error) < floatMax))

    \\//   ((floatMin <= lb1 * (0 - ub2) //\\ (lb1 >= R0) //\\  (ub2 < R0)) //\\ ((ub1 * (0 - lb2))*(1+error) < floatMax)) 

    \\//   ((floatMin <= (0 - ub1) * lb2 //\\ (ub1 < R0) //\\  (lb2 >= R0)) //\\ (((0 - lb1) * (ub2))*(1+error) < floatMax)) ->
    
    
    (lb1 <= r1) ->
    
    (lb2 <= r2) ->
    
    (r1 <= ub1) ->
    
    (r2 <= ub2) ->    

    ((Rabs (round radix2 (FLT_exp (3-custom_emax- custom_prec) custom_prec ) (round_mode mode_NE) (B2R custom_prec custom_emax f1 * B2R custom_prec custom_emax f2))) 
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
      pose proof relErrorBasedOnFloatMinTruthMult.
      Lemma andOrProof2 : forall (p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16:Prop),
          (p1 //\\ p2 //\\ p3) //\\ p4
          \\// (p5 //\\ p6 //\\ p7) //\\ p8 
          \\// (p9 //\\ p10 //\\ p11) //\\ p12
          \\// ( p13 //\\ p14 //\\ p15) //\\ p16 
          ->
          (p1 //\\ p2 //\\ p3)
          \\// (p5 //\\ p6 //\\ p7)
          \\// (p9 //\\ p10 //\\ p11)
          \\// (p13 //\\ p14 //\\ p15).
      Proof.
        intros.
        tlaIntuition.      
      Qed.
      
      intros.
      assert (H1':=H1).
      apply andOrProof2 in H1.
      specialize (H6 r1 r2 lb1 lb2 ub1 ub2 H1 H2 H3 H4 H5).
      unfold B2R.
      unfold Rabs in *.
      pose proof errorGt0 as errorGt0.
      rewrite H7 in H6.
      rewrite H8 in H6.
      remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                      (round_mode mode_NE) (0 - 0)) as roundedValue.
      clear HeqroundedValue.
      clear H7 H8.
      clear H H0.
      pose proof floatMaxGt0.
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
    pose proof relErrorBasedOnFloatMinTruthMult.
    assert (H1':=H1).
    apply andOrProof2 in H1.
    specialize (H6 r1 r2 lb1 lb2 ub1 ub2 H1 H2 H3 H4 H5).
    unfold B2R.
    rewrite <- H7.
    unfold Rabs in *.
    pose proof errorGt0 as errorGt0.
    rewrite <- H8.
    remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                    (round_mode mode_NE) (r1 * r2)) as roundedValue.
    clear HeqroundedValue.
    clear H8.
    clear H H0.
    pose proof floatMaxGt0.
    pose proof floatMinGt0.
    clear H1.
    destruct Rcase_abs.
    {
      destruct Rcase_abs.
      {
        destruct Rcase_abs.
        {
          destruct H1'.
          {
            breakAbstraction.
            decompose [and] H1.
            clear H9 H0 H7 H8.
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
            destruct H1.
            {
              breakAbstraction.
              decompose [and] H1.
              clear H10 H0.
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
              destruct H1. 
              {
                breakAbstraction.
                decompose [and] H1.
                clear H10 H0 H1. 
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
                breakAbstraction.
                decompose [and] H1.
                clear H10 H0 H1.
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
          destruct H1'.
          {
            breakAbstraction.

            decompose [and] H1.
            clear H10 H0.
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
            destruct H1.
            {
              breakAbstraction.
              decompose [and] H1.
              clear H10 H0.
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
              destruct H1.
              {
                breakAbstraction.
                decompose [and] H1.
                clear H10 H0.
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
                breakAbstraction.
                decompose [and] H1.
                clear H10 H0.
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
      }
      {
        destruct Rcase_abs.
        {
          destruct H1'.
          {
            breakAbstraction.
            decompose [and] H1.
            clear H10 H0.
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
            destruct H1.
            {
              breakAbstraction; decompose [and] H1.
              clear H10 H0.
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
              destruct H1.
              {
                breakAbstraction; decompose [and] H1.
                clear H10 H10.
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
               
                breakAbstraction; decompose [and] H1.
                clear H10 H10.
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
          destruct H1'.
          {
            breakAbstraction; decompose [and] H1.
            clear H10 H0.
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
            destruct H1.
            {
              breakAbstraction; decompose [and] H1.
              clear H10 H0 r0 H1.
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
              destruct H1.
              {
                breakAbstraction; decompose [and] H1.
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
                breakAbstraction; decompose [and] H1.
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
      }
    }
    {
       destruct Rcase_abs.
        {
          destruct Rcase_abs.
          {
            destruct H1'.
            {
              breakAbstraction; decompose [and] H1.
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
              destruct H1.
              {
                breakAbstraction; decompose [and] H1.
                clear H10 H9 H8 H0 H1.
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
                destruct H1. 
                {
                  breakAbstraction; decompose [and] H1.
                  clear H10 H0 H1 H8.
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
                  breakAbstraction; decompose [and] H1.
                  clear H10 H0 H1 H8.
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
            destruct H1'.
            {
              breakAbstraction; decompose [and] H1.
              clear H10 H0 H1 H8.
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
            destruct H1.
            {
              breakAbstraction; decompose [and] H1.
              clear H10 H0 H1 H8.
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
              destruct H1.
              {
                breakAbstraction; decompose [and] H1.
                clear H10 H0 H1 H8.
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
                breakAbstraction; decompose [and] H1.
                clear H10 H0 H1 H8.
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
        }
        {
          destruct Rcase_abs.
          {
            destruct H1'.
            {
              breakAbstraction; decompose [and] H1.
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
              destruct H1.
              {
                breakAbstraction; decompose [and] H1.
                clear H10 H8 H0 H1.
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
                destruct H1. 
                {
                  breakAbstraction; decompose [and] H1.
                   clear H10 H8 H0 H1.
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
                  breakAbstraction; decompose [and] H1.
                   clear H10 H8 H0 H1.
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
            destruct H1'.
            {
              breakAbstraction; decompose [and] H1.
              clear H10 H8 H0 H1.
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
              destruct H1.
              {
                breakAbstraction; decompose [and] H1.
                 clear H10 H8 H0 H1.
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
                destruct H1.
                {
                  breakAbstraction; decompose [and] H1.
                   clear H10 H8 H0 H1.
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
                  breakAbstraction; decompose [and] H1.
                   clear H10 H8 H0 H1.
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
        }
    }
  }
  {
    inversion H.
  }
  {
    inversion H.
  }
  {
    destruct f2 eqn:f2_des.
    {
     inversion H.
      inversion H0.
      pose proof relErrorBasedOnFloatMinTruthMult.
      
      
      intros.
      assert (H1':=H1).
      apply andOrProof2 in H1.
      specialize (H6 r1 r2 lb1 lb2 ub1 ub2 H1 H2 H3 H4 H5).
      unfold B2R.
      unfold Rabs in *.
      pose proof errorGt0 as errorGt0.
      rewrite H7 in H6.
      rewrite H8 in H6.
      remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                      (round_mode mode_NE) (0 - 0)) as roundedValue.
      clear HeqroundedValue.
      clear H7 H8.
      clear H H0.
      pose proof floatMaxGt0.
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
    pose proof relErrorBasedOnFloatMinTruthMult.
    assert (H1':=H1).
    apply andOrProof2 in H1.
    specialize (H6 r1 r2 lb1 lb2 ub1 ub2 H1 H2 H3 H4 H5).
    unfold B2R.
    rewrite <- H7.
    unfold Rabs in *.
    pose proof errorGt0 as errorGt0.
    rewrite <- H8.
    remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                    (round_mode mode_NE) (r1 * r2)) as roundedValue.
    clear HeqroundedValue.
    clear H8.
    clear H H0.
    pose proof floatMaxGt0.
    pose proof floatMinGt0.
    clear H1.
    destruct Rcase_abs.
    {
      destruct Rcase_abs.
      {
        destruct Rcase_abs.
        {
          destruct H1'.
          {
            breakAbstraction; decompose [and] H1.
            clear H9 H0 H7 H8.
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
            destruct H1.
            {
              breakAbstraction; decompose [and] H1.
              clear H10 H0 H1.
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
              destruct H1. 
              {
                breakAbstraction; decompose [and] H1.
                clear H10 H0 H1 H7.
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
                breakAbstraction; decompose [and] H1.
                clear H10 H0 H7 H1. 
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
          destruct H1'.
          {
            breakAbstraction; decompose [and] H1.
            clear H0 H1 H10 H7.
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
            destruct H1.
            breakAbstraction; decompose [and] H1.
            clear H1 H10 H0 H7.
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
            destruct H1.
            breakAbstraction; decompose [and] H1.
            clear H1 H10 H0 H7.
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
            breakAbstraction; decompose [and] H1.
            clear H1 H10 H0 H7.
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
            breakAbstraction; decompose [and] H1.
            clear H10 H0 H1 H7.
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
            destruct H1.
            {
              breakAbstraction; decompose [and] H1.
              clear H10 H0 H1 H7.
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
              destruct H1.
              {
                breakAbstraction; decompose [and] H1.
                clear H10 H0 H1 H7.
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
                destruct H1.
                {
                  breakAbstraction; decompose [and] H1.
                  clear H9 H0 H1 H7.
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
        }
        {
          destruct H1'.
          {
            breakAbstraction; decompose [and] H1.
            clear H10 H0 H1 H7.
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
            destruct H1.
            {
              breakAbstraction; decompose [and] H1.
              clear H10 H0 H1 H7.
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
              destruct H1.
              {
                breakAbstraction; decompose [and] H1.
                clear H10 H0 H1 H7.
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
                breakAbstraction; decompose [and] H1.
                clear H10 H0 H1 H7.
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
      }
    }
    {
       destruct Rcase_abs.
       {
         destruct Rcase_abs.
         {
           destruct H1'.
           {
             breakAbstraction; decompose [and] H1.
             clear H10 H0 H1 H7.
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
             destruct H1.
             {
               breakAbstraction; decompose [and] H1.
               clear H10 H0 H1 H7.
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
               destruct H1. 
               {
                 breakAbstraction; decompose [and] H1.
                 clear  H10 H0 H1 H7.
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
                 breakAbstraction; decompose [and] H1.
                 clear  H10 H0 H1 H7.
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
          destruct H1'.
          {
            breakAbstraction; decompose [and] H1.
            clear  H10 H0 H1 H7.
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
            destruct H1.
            {
              breakAbstraction; decompose [and] H1.
              clear  H10 H0 H1 H7.
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
              destruct H1.
              {
                breakAbstraction; decompose [and] H1.
                clear  H10 H0 H1 H7.
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
                breakAbstraction; decompose [and] H1.
                clear  H10 H0 H1 H7.
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
  }
       {
         destruct Rcase_abs.
         {
           destruct H1'.
           {
             breakAbstraction; decompose [and] H1.
             clear  H10 H0 H1 H7.
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
             destruct H1.
             {
               breakAbstraction; decompose [and] H1.
               clear  H10 H0 H1 H7.
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
               destruct H1. 
               {
                 breakAbstraction; decompose [and] H1.
                 clear  H10 H0 H1 H7.
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
                 breakAbstraction; decompose [and] H1.
                 clear  H10 H0 H1 H7.
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
           destruct H1'.
           {
             breakAbstraction; decompose [and] H1.
             clear H10 H0 H7 H1.
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
             destruct H1.
             {
               breakAbstraction; decompose [and] H1.
               clear H10 H0 H7 H1.
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
               destruct H1.
               {
                 breakAbstraction; decompose [and] H1.
                 clear H10 H0 H7 H1.
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
                 breakAbstraction; decompose [and] H1.
                 clear H10 H0 H7 H1.
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
       }     
    }
}
Qed.


Lemma plusRoundingTruth2 : forall (f1 f2: float)  (r1 r2:R) , 
    Some r1 = floatToReal f1 -> 

    Some r2 = floatToReal f2 ->

    ((Rabs (round radix2 (FLT_exp (3-custom_emax- custom_prec) custom_prec ) (round_mode mode_NE) (B2R custom_prec custom_emax f1 + B2R custom_prec custom_emax f2))) <  (bpow radix2 custom_emax))%R  ->
    
    (B2R custom_prec custom_emax (Bplus custom_prec custom_emax  custom_precGt0 custom_precLtEmax custom_nan mode_NE f1 f2) =round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (B2R custom_prec custom_emax f1 + B2R custom_prec custom_emax f2)  //\\   is_finite custom_prec custom_emax (Bplus custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_NE f1 f2) = true)%R. 
Proof.
  intros.
  pose proof Bplus_correct.
  specialize (H2 custom_prec custom_emax).
  specialize (H2 custom_precGt0 custom_precLtEmax custom_nan ).
  specialize (H2  mode_NE).
  specialize (H2 f1 f2).
  Print floatValid.
  apply floatValid in H.
  apply floatValid in H0.
  specialize (H2 H H0).
  apply rltProof2 in H1.
  rewrite H1 in H2.
  breakAbstraction; decompose [and] H2.
  split.
  apply H2. 
  apply H5.

Qed.
Print Bminus_correct.
Lemma minusRoundingTruth2 : forall (f1 f2: float)  (r1 r2:R) ,  Some r1 = (floatToReal f1) -> 
                                                                       Some r2 = (floatToReal f2) ->   
                                                                       
                                                                       ((Rabs (round radix2 (FLT_exp (3-custom_emax- custom_prec) custom_prec ) (round_mode mode_NE) (B2R custom_prec custom_emax f1 - B2R custom_prec custom_emax f2))) 
                                                                        <  (bpow radix2 custom_emax))%R -> 
                                                                       (B2R custom_prec custom_emax (Bminus custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_NE f1 f2) =round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (B2R custom_prec custom_emax f1 - B2R custom_prec custom_emax f2)  //\\   is_finite custom_prec custom_emax (Bminus custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_NE f1 f2) = true)%R.

Proof.
  intros.
  pose proof Bminus_correct.
  specialize (H2 custom_prec custom_emax).
  specialize (H2 custom_precGt0 custom_precLtEmax custom_nan ).
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


Lemma multRoundingTruth2 : forall (f1 f2: float)  (r1 r2:R) ,  Some r1 = (floatToReal f1) -> 
                                                                      Some r2 = (floatToReal f2) ->   
                                                                      
                                                                      ((Rabs (round radix2 (FLT_exp (3-custom_emax- custom_prec) custom_prec ) (round_mode mode_NE) (B2R custom_prec custom_emax f1 * B2R custom_prec custom_emax f2))) 
                                                                       <  (bpow radix2 custom_emax))%R -> 
                                                                      (B2R custom_prec custom_emax (Bmult custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_NE f1 f2) =round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (B2R custom_prec custom_emax f1 * B2R custom_prec custom_emax f2)  //\\   is_finite custom_prec custom_emax (Bmult custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_NE f1 f2) = true)%R.

Proof.
  intros.
  pose proof Bmult_correct.
  specialize (H2 custom_prec custom_emax).
  specialize (H2 custom_precGt0 custom_precLtEmax custom_nan ).
  specialize (H2  mode_NE).
  specialize (H2 f1 f2).
  Print floatValid.
  apply floatValid in H.
  apply floatValid in H0.
  apply rltProof2 in H1.
  rewrite H1 in H2.
  decompose [and] H2.
  split.
  apply H3. 
  unfold custom_prec, custom_emax in *.
  rewrite H in H5.
  rewrite H0 in H5.
  revert H5.
  intros H5.
  simpl in H5.
  apply H5.
Qed.


Lemma natFloatMinBoundProof : 
  forall n,
    ((floatMin <= INR n //\\ INR n >= 0) \\// (floatMin <= 0 -(INR n) //\\ INR n < 0) -> floatMin <= Rabs (INR n))%R.
Proof.
  breakAbstraction.
    intros.
    unfold Rabs.
    destruct Rcase_abs.
    destruct H.
    decompose [and] H.
    psatz R.
    decompose [and] H.
    simpl in H0.
    psatz R.
    destruct H.
    decompose [and] H.
    apply H0.
    decompose [and] H.
    psatz R.
Qed.

Lemma relErrorTruthNat : 
  forall n, 
    (
      (floatMin <= INR n)%R //\\ (INR n >= 0)%R \\//
       (floatMin <= 0 - INR n)%R //\\ (INR n < 0)%R
      -> 
      (Rabs 
         (round 
            radix2 
            (FLT_exp (3 - custom_emax - custom_prec) custom_prec) 
            (round_mode mode_NE) 
            (INR n) - 
          (INR n)
         ) < 
       bpow radix2 (- custom_prec + 1) * Rabs (INR n))
    )%R.
  Proof.
    intros.
    pose proof relative_error as Rel_Err.
remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp.
specialize (Rel_Err radix2 round_fexp).
  subst.
  specialize (Rel_Err validFexpProof (custom_emin)%Z custom_prec  precThm (round_mode mode_NE)). 
  specialize (Rel_Err (valid_rnd_N choiceDef)).
  specialize (Rel_Err (INR n)).
  pose proof natFloatMinBoundProof.
  specialize (H0 n H).
  unfold floatMin in H0.
  unfold custom_emin in Rel_Err.
  specialize (Rel_Err H0).
  apply Rel_Err.
Qed.


  Lemma natRoundingTruth : 
    forall n, 
      (((floatMin <= INR n)%R //\\ (INR n >= 0)%R //\\  ((INR n)* (1+error) <  (floatMax))%R) \\//
       ((floatMin <= 0 - INR n)%R //\\ (INR n < 0)%R //\\  ((0 -(INR n))* (1+error) <  (floatMax))) 

       ->
       
       (Rabs 
          (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (Z2R (Z.of_nat n))) 
   < (bpow radix2 custom_emax)))%R.
                               
Proof.
  intros.
  pose proof relErrorTruthNat as relErrorTruthNat.
  Lemma orProof: forall (p1 p2 p3 p4 p5 p6 : Prop), (p1 //\\ p2 //\\ p3) \\// (p4 //\\ p5 //\\ p6) -> (p1 //\\ p2) \\// (p4 //\\ p5).
  Proof.
    intros.
    tlaIntuition.
    Qed.
  intros.
  assert (H1 := H). 
  apply orProof in H.
  
  specialize (relErrorTruthNat n H).
 Lemma natToReal : forall n,  Z2R (Z.of_nat n) = INR n.
   intros.
   rewrite  INR_IZR_INZ.
   rewrite Z2R_IZR.
   reflexivity.
Qed.
 intros.
 rewrite natToReal. 
 remember    (round radix2
                    (FLT_exp (3 - custom_emax - custom_prec)
                             custom_prec) (round_mode mode_NE) 
                    (INR n)) as roundedValue.
 clear HeqroundedValue.
 unfold floatMax in *.
 unfold floatMin in *.
 unfold custom_emax in *.
 unfold error in *.
 destruct H1;
   breakAbstraction;
   decompose [and] H0;
   clear H0;
   clear H;
   unfold Rabs in *;
   destruct Rcase_abs in *;
   destruct Rcase_abs in *;
   destruct Rcase_abs in *; 
   repeat match goal with
          | H : @eq R _ _ |- _ => revert H
          | H : @Rle _ _ |- _ => revert H
          | H : @Rge _ _ |- _ => revert H
          | H : @Rlt _ _ |- _ => revert H
          | H :@ Rgt _ _ |- _ => revert H
          | H : @Rge _ _ |- _ => revert H
          end;
   psatz R.
Qed.

SearchAbout Fappli_IEEE_extra.BofZ.

Lemma natRoundingTruth2 : forall (f:float) (r:R) (n:nat),
    Some r = floatToReal f ->
    Some f = Some (nat_to_float n)->
    (Rabs 
       (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (Z2R (Z.of_nat n))) 
     < (bpow radix2 custom_emax))%R ->
    B2R custom_prec custom_emax (Fappli_IEEE_extra.BofZ custom_prec custom_emax custom_precGt0 custom_precLtEmax (Z.of_nat n)) =
    round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (Z2R (Z.of_nat n)).                         

Proof.       
  intros.
  pose proof Fappli_IEEE_extra.BofZ_correct as Z2Rcorrect.
  specialize (Z2Rcorrect custom_prec custom_emax custom_precGt0 custom_precLtEmax (Z.of_nat n)).
  apply rltProof2 in H1.
  rewrite H1 in Z2Rcorrect.
  decompose [and] Z2Rcorrect.
  apply H2.
Qed.



 Lemma denote_singleBoundTermsEquality :   forall (st : state) (expr : NowTerm) (fState : fstate),
   related fState (Stream.hd (traceFromState st)) ->
   match eval_NowTerm fState expr with
   | Some evalAsF =>
           List.Forall
             (fun term : singleBoundTerm =>
              let (premise0, pred) := denote_singleBoundTermNew st term in
              premise0 -> match floatToReal evalAsF with 
                            | Some f => pred f
                            | None => True
                          end) (bound_term expr)

   | None => True
   end ->   
   related fState (Stream.hd (traceFromState st)) ->
   match eval_NowTerm fState expr with
   | Some evalAsF =>
     match floatToReal evalAsF with 
       | Some f => 
           List.Forall
          (denote_singleBoundTerm f (traceFromState st))   (bound_term expr)
       | None => True
     end
   | None => True
   end.
   
    unfold denote_singleBoundTermNew.
    unfold denote_singleBoundTerm.
    Lemma boundTermProof : forall fState st expr,  
        match eval_NowTerm fState expr with
          | Some evalAsF =>
            List.Forall
              (fun term : singleBoundTerm =>
                 eval_formula (premise term) (traceFromState st) ->
                 match floatToReal evalAsF with
                   | Some f =>
                     (eval_term (lb term) (Stream.hd (traceFromState st))
                                (Stream.hd (Stream.tl (traceFromState st))) <= f <=
                      eval_term (ub term) (Stream.hd (traceFromState st))
                                (Stream.hd (Stream.tl (traceFromState st))))%R
                   | None => True
                 end) (bound_term expr)
          | None => True
        end ->  
        match eval_NowTerm fState expr with
          | Some evalAsF =>
            match floatToReal evalAsF with
              | Some f =>
                List.Forall
                  (fun s : singleBoundTerm =>
                     eval_formula (premise s) (traceFromState st) ->
                     (eval_term (lb s) (Stream.hd (traceFromState st))
                                (Stream.hd (Stream.tl (traceFromState st))) <= f <=
                      eval_term (ub s) (Stream.hd (traceFromState st))
                                (Stream.hd (Stream.tl (traceFromState st))))%R) 
                  (bound_term expr)
              | None => True
            end
          | None => True
        end.
      intros.
      remember (eval_NowTerm fState expr) as evaluatedFloat.
      destruct evaluatedFloat.
      {
        (remember (floatToReal f) as floatConvertedToReal).
        destruct floatConvertedToReal eqn:floatConvertedToReal_des. 
        {
          apply H. 
        }
        {
          intuition.
        }
      }
      {
        apply H.
        
      } 
    Qed.
    intros.    
   
     pose proof boundTermProof.
     specialize (H2 fState st expr H0).
     apply H2.
 Qed.


Lemma bound_proof' : 
  forall (st:state) (expr:NowTerm) (fState:fstate),
    related fState st -> 
    boundDef' expr st fState.
Proof.
(*
  unfold boundDef'. 
  intros.
  remember (eval_NowTerm fState expr). destruct o; trivial.
  remember (floatToReal f). destruct o; trivial.
  revert Heqo. revert Heqo0. revert f. revert r.
  remember (traceFromState st) as tr.
  clear Heqtr.
  induction expr.



  { simpl. 
    intros.
    constructor; [ | constructor ]. intros.
    unfold premise in H0.
    unfold eval_formula in H0.
    unfold lb. unfold ub.
    simpl.
    red in H.
    symmetry in Heqo.
    apply H in Heqo.
    rewrite <- Heqo in *.
    inversion Heqo0.
    psatz R.
  }

  { simpl. constructor; [ | constructor ].
    {
      intros.
      simpl in *.
      unfold Semantics.eval_comp in *.
      
      simpl in H0.
      decompose [and] H0.
      clear H5.
      clear H0.
      
      Lemma conjoin2 : forall (p1 p2 p3:Prop), p1 -> p2 -> p3 -> p1 //\\ p2 //\\ p3.
        intros.
        tlaIntuition.
      Qed.
      intros. 
      pose proof conjoin2 as premise.
      
      specialize (premise (floatMin <= INR n)%R (INR n >= 0)%R (INR n * (1 + error) < floatMax)%R H1 H3 H2).
     
      intros.
      pose proof orExtra as orExtra1.
      specialize (orExtra1 ((floatMin <= INR n)%R //\\
                            (INR n >= 0)%R //\\ (INR n * (1 + error) < floatMax)%R) 
                           ((floatMin <=0 - INR n)%R //\\
                            (INR n < 0)%R //\\ ((0 - INR n) * (1 + error) < floatMax)%R) premise).
      pose proof natRoundingTruth as natRoundingTruth.
      specialize (natRoundingTruth n orExtra1).
      pose proof natRoundingTruth2 as natRoundingTruth2.
      specialize (natRoundingTruth2 f r n Heqo0 Heqo natRoundingTruth).
      Lemma conjoin : forall (p1 p2:Prop), p1 -> p2 -> p1 //\\ p2.
        intros.
        tlaIntuition.
      Qed.
      pose proof conjoin as premise2.
      specialize (premise2 (floatMin <= INR n)%R (INR n >= 0)%R H1 H3).
      pose proof orExtra as orExtra2.
      specialize (orExtra2 ((floatMin <= INR n)%R //\\ (INR n >= 0)%R) 
                           ((floatMin <= 0 - INR n)%R //\\ (INR n < 0)%R) premise2).
      
      unfold floatToReal in *.
      unfold nat_to_float in *.
      destruct f eqn:f_des.
      {
        inversion Heqo0.
        inversion Heqo.
        Print nat_to_float.
        unfold Fappli_IEEE_extra.b64_of_Z in H5.    
        rewrite <- H5 in natRoundingTruth2 at 1.
        
        unfold B2R in natRoundingTruth2.
        
        
        rewrite natRoundingTruth2.
        clear natRoundingTruth2.
        clear natRoundingTruth.
        
        clear H2.
        pose proof relErrorTruthNat as relErrorTruthNat.
      
        specialize (relErrorTruthNat n orExtra2).
        Lemma simplify2 : (round_mode mode_NE)  =  (Znearest (fun x : Z => negb (Zeven x))).
          simpl.
          reflexivity.
        Qed.
        intros.
        rewrite natToReal.
        remember (round radix2
                        (FLT_exp (3 - custom_emax  - custom_prec)
                                 custom_prec) (round_mode mode_NE) 
                        (INR n)) as roundedValue.
        clear HeqroundedValue.
        clear H5.
        clear premise premise2 orExtra2.
        clear Heqo0 Heqo f_des orExtra1 H1 H4.
        unfold Rabs in *.
        
        pose proof errorGt0 as errorGt0.
        pose proof errorLessThan1 as errorLessThan1.
        unfold error in *.
        breakAbstraction.
        admit.
        (*
        destruct Rcase_abs;
          destruct Rcase_abs;
          repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 end;
          psatz R.*)
      }
      {
        inversion Heqo0.
      }
      {
        inversion Heqo0.
      }
      {
        inversion Heqo0.
        inversion Heqo.
        Print nat_to_float.
        unfold Fappli_IEEE_extra.b64_of_Z in H5.    
        rewrite <- H5 in natRoundingTruth2 at 1.
        unfold B2R in natRoundingTruth2.
        
        rewrite natRoundingTruth2.
        clear natRoundingTruth2.
        clear natRoundingTruth.
        
        clear H2.
        pose proof relErrorTruthNat as relErrorTruthNat.
        specialize (relErrorTruthNat n orExtra2).
  
        rewrite natToReal.
        remember (round radix2
                        (FLT_exp (3 - custom_emax  - custom_prec)
                                 custom_prec) (round_mode mode_NE) 
                        (INR n)) as roundedValue.
        clear HeqroundedValue.
        clear H5.
        clear premise premise2 orExtra2.
        clear Heqo0 Heqo f_des e0 orExtra1 H1 H4.
        unfold Rabs in *.
        
        pose proof errorGt0 as errorGt0.
        pose proof errorLessThan1 as errorLessThan1.
        unfold error in *.
        breakAbstraction.
        admit.
        (*destruct Rcase_abs;
          destruct Rcase_abs;
          repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 end;
          psatz R. *)
      }
    } 
    {
      
      intros.
      simpl in *.
      unfold Semantics.eval_comp in *.
      unfold Semantics.eval_comp in H0.
      simpl in H0.
      decompose [and] H0.
      clear H5.
      clear H0.
      intros. 
      pose proof conjoin2 as premise.
      
      specialize (premise (floatMin <= 0 - INR n)%R  (INR n < 0)%R ((0 - INR n) * (1 + error) < floatMax)%R H1 H3 H2).
      intros.
        Lemma orExtra2 : forall p1 p2 : Prop, p2 -> p1 \\// p2.
          intros; tlaIntuition. Qed.
      
      pose proof orExtra2 as orExtra1.
      specialize (orExtra1 ((floatMin <= INR n)%R //\\
                            (INR n >= 0)%R //\\ (INR n * (1 + error) < floatMax)%R) 
                           ((floatMin <= 0 - INR n)%R //\\
                            (INR n < 0)%R //\\ ((0 - INR n) * (1 + error) < floatMax)%R) premise).
      pose proof natRoundingTruth as natRoundingTruth.
      specialize (natRoundingTruth n orExtra1).
      pose proof natRoundingTruth2 as natRoundingTruth2.
      specialize (natRoundingTruth2 f r n Heqo0 Heqo natRoundingTruth).
      pose proof conjoin as premise2.
      specialize (premise2 (floatMin <= 0 - INR n)%R (INR n < 0)%R H1 H3).
      pose proof orExtra2 as orExtra2.
      specialize (orExtra2 ((floatMin <= INR n)%R //\\ (INR n >= 0)%R) 
                           ((floatMin <=0 - INR n)%R //\\ (INR n < 0)%R) premise2).
      
      unfold floatToReal in *.
      unfold nat_to_float in *.
      destruct f eqn:f_des.
      {
        inversion Heqo0.
        inversion Heqo.
        Print nat_to_float.
        unfold Fappli_IEEE_extra.b64_of_Z in H5.    
        rewrite <- H5 in natRoundingTruth2 at 1.
        unfold B2R in natRoundingTruth2.
        
        rewrite natRoundingTruth2.
        clear natRoundingTruth2.
        clear natRoundingTruth.
        
        clear H2.
        pose proof relErrorTruthNat as relErrorTruthNat.
       
        specialize (relErrorTruthNat n orExtra2).
        
        rewrite natToReal.
        remember (round radix2
                        (FLT_exp (3 - custom_emax  - custom_prec)
                                 custom_prec) (round_mode mode_NE) 
                        (INR n)) as roundedValue.
        clear HeqroundedValue.
        clear H5.
        clear premise premise2 orExtra2.
        clear Heqo0 Heqo f_des orExtra1 H1 H4.
        unfold Rabs in *.
        
        pose proof errorGt0 as errorGt0.
        pose proof errorLessThan1 as errorLessThan1.
        unfold error in *.
        breakAbstraction.
        admit.
        (*
        destruct Rcase_abs;
          destruct Rcase_abs;
          repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 end;
          psatz R. *)
      }
      {
        inversion Heqo0.
      }
      {
        inversion Heqo0.
      }
      {
        inversion Heqo0.
        inversion Heqo.
        Print nat_to_float.
        unfold Fappli_IEEE_extra.b64_of_Z in H5.    
        rewrite <- H5 in natRoundingTruth2 at 1.
        
        unfold B2R in natRoundingTruth2.
        
        rewrite natRoundingTruth2.
        clear natRoundingTruth2.
        clear natRoundingTruth.
        
        clear H2.
        pose proof relErrorTruthNat as relErrorTruthNat.
        specialize (relErrorTruthNat n orExtra2).

        rewrite natToReal.
        remember (round radix2
                        (FLT_exp (3 - custom_emax  - custom_prec)
                                 custom_prec) (round_mode mode_NE) 
                        (INR n)) as roundedValue.
        clear HeqroundedValue.
        clear H5.
        clear premise premise2 orExtra2.
        clear Heqo0 Heqo f_des e0 orExtra1 H1 H4.
        unfold Rabs in *.
        
        pose proof errorGt0 as errorGt0.
        pose proof errorLessThan1 as errorLessThan1.
        unfold error in *.
        breakAbstraction.
        (*
        destruct Rcase_abs;
          destruct Rcase_abs;
          repeat match goal with
                 | H : @eq R _ _ |- _ => revert H
                 | H : @Rle _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 | H : @Rlt _ _ |- _ => revert H
                 | H :@ Rgt _ _ |- _ => revert H
                 | H : @Rge _ _ |- _ => revert H
                 end;
          psatz R. *)
        admit.
      }
    } 
    {
      constructor.
    }
  }
 
  { simpl. constructor; [ | constructor ].
    simpl in *. 
    intro XXX; clear XXX.
    simpl in Heqo.
    inversion Heqo. subst.
    unfold floatToReal in Heqo0.
    destruct f; simpl; inversion Heqo0; intuition.
  }
  { simpl.   unfold getBound. 
    intros.
    Print plusMinusfoldListwithList.
    assert (Heqo':=Heqo).
    apply resultImplicationsPlus in Heqo.
    Require Import ExtLib.Tactics.
    breakAbstraction.
    forward_reason. destruct H2; destruct H3.
    specialize (IHexpr1 _ _ H2 H0).
    specialize (IHexpr2 _ _ H3 H1).
    2: eexists; eauto.
    eapply Forall_forall. intros.
    revert H5.
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
    breakAbstraction.
    rewrite H7 in Heqo0.
    unfold floatToReal in Heqo0.
    unfold denote_singleBoundTerm in *.
    destruct f eqn:f_des.
    {
      rewrite <- H7 in Heqo0.
      inversion Heqo0.
      assert (plusResultStmt := H7).
      assert (floatToRealRelationForExpr1:= H2).
      assert (floatToRealRelationForExpr2:= H3).
      clear H f Heqo0 H0 H1 H8 f_des Heqo' H7 H8 .
      assert (floatToRealProof1:= H2).
      assert (floatToRealProof2:= H3).
      clear H2 H3.      
      
      unfold denote_singleBoundTerm in *.
      intros H.
      simpl in H6.
      unfold simpleBound in *.
      unfold simpleBound4 in *.
      destruct H6. 
      {
        rewrite <- H0 in H.
        simpl in H.
        rewrite <- H0.
        decompose [and] H.
        clear H9.
        assert (H8:= H7).
        clear H7.
        apply IHexpr1 in H1.
        apply IHexpr2 in H3.
        assert (expr1Bound := H1).
        assert (expr2Bound := H3).
        assert (floatMinCase := H2).
        assert (floatMaxBound1 := H6). 
        assert (resultGe0 := H8).
        clear H4 H2 H1 H3 H H5  H0 H8 H6 IHexpr1 IHexpr2.
        unfold Semantics.eval_comp in *.
        unfold eval_term in .
        simpl in floatMinCase.
        simpl in expr1Bound.
        simpl in expr2Bound.
        simpl in floatMaxBound1.
        simpl in resultGe0.
        simpl.
        remember (eval_term (lb x4) st st) as lb1.
        remember (eval_term (lb x5) st st) as lb2.
        remember (eval_term (ub x5) st st) as ub2.
        remember (eval_term (ub x4) st st) as ub1.
        clear Hequb1 Hequb2 Heqlb1 Heqlb2.
        
        
        pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
        specialize (relErrorBasedOnFloatMinTruthPlus x1 x2 lb1 lb2 ub1 ub2).
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        
        intros.
        assert (floatMinCase1 := floatMinCase).
        clear floatMinCase.
        pose proof orExtra as floatMinCase. 
        specialize (floatMinCase (floatMin <= lb1 + lb2)%R  (floatMin <= 0 - ub1 + (0 - ub2))%R floatMinCase1).
        clear floatMinCase1.
        specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H H1 H0 H2).
        pose proof plusRoundingTruth as plusRoundingTruth. 
        Lemma floatMaxBoundHelper : forall lb1 lb2 floatMax error, (lb1 + lb2 >= R0)%R -> (floatMax > 0)%R ->  (error > R0)%R -> ((0-lb1+(0-lb2))*(1+error)<floatMax)%R.
          intros. psatz R. Qed.
        pose proof floatMaxBoundHelper as floatMaxBound2.
        specialize (floatMaxBound2 lb1 lb2 floatMax error resultGe0 floatMaxGt0 errorGt0).
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
        unfold error in *.
        unfold Rabs in *.
       
        pose proof errorLessThan1 as errorLessThan1.
        unfold error in *.
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
          clear H9.
          assert (H8:=H7).
          clear H7.
          apply IHexpr1 in H1.
          apply IHexpr2 in H3.
          assert (expr1Bound := H1).
          assert (expr2Bound := H3).
          assert (floatMinCase := H2).
          assert (floatMaxBound1 := H6). 
          assert (resultGe0 := H8).
          clear H4 H2 H1 H3 H H5 H0 H8 H6 IHexpr1 IHexpr2.
          unfold Semantics.eval_comp in *.
          simpl in floatMinCase.
          simpl in expr1Bound.
          simpl in expr2Bound.
          simpl in floatMaxBound1.
          simpl in resultGe0.
          simpl.
          remember (eval_term (lb x4) st st) as lb1.
          remember (eval_term (lb x5) st st) as lb2.
          remember (eval_term (ub x5) st st) as ub2.
          remember (eval_term (ub x4) st st) as ub1.
          clear Hequb1 Hequb2 Heqlb1 Heqlb2.
          pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
          specialize (relErrorBasedOnFloatMinTruthPlus x1 x2 lb1 lb2 ub1 ub2).
          destruct expr1Bound.
          destruct expr2Bound.
          pose proof or_introl.
          
          intros.          
          assert (floatMinCase1 := floatMinCase).
          clear floatMinCase.
          pose proof orExtra2 as floatMinCase. 
          specialize (floatMinCase (floatMin <= lb1 + lb2)%R  (floatMin <= 0 - ub1 + (0 - ub2))%R floatMinCase1).
          clear floatMinCase1.
          specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H H1 H0 H2).
          pose proof plusRoundingTruth as plusRoundingTruth.
           Lemma floatMaxBoundHelper2 : forall ub1 ub2 floatMax error, (ub1 + ub2 < R0)%R -> (floatMax > 0)%R ->  (error > R0)%R -> ((ub1 + ub2)*(1+error)<floatMax)%R.
             intros. psatz R. Qed.
           pose proof floatMaxBoundHelper2 as floatMaxBound2.
           specialize (floatMaxBound2 ub1 ub2 floatMax error resultGe0 floatMaxGt0 errorGt0).
           specialize (plusRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 floatMinCase H H1 floatMaxBound2 floatMaxBound1 H0 H2).
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
          unfold error in *.
          unfold Rabs in *.
          pose proof errorLessThan1 as errorLessThan1.
          unfold error in *.
          destruct Rcase_abs;destruct Rcase_abs;psatz R.
        }
        {
                    destruct H0.
          {
            rewrite <- H0 in H.
            simpl in H.
            rewrite <- H0.
            decompose [and] H.
            clear H10.
            assert (H9:=H8).
            apply IHexpr1 in H1.
            apply IHexpr2 in H3.
            assert (expr1Bound := H1).
            assert (expr2Bound := H3).
            assert (floatMinCase1 := H2).
            assert (floatMinCase2 := H6).
            assert (floatMaxBound1 := H7).
            assert (resultGe0 := H9).
            clear H4 H2 H1 H3 H H5 H0 H7 H9 H6 IHexpr1 IHexpr2.
            unfold Semantics.eval_comp in *.
            simpl in floatMinCase1.
            simpl in floatMinCase2.
            simpl in expr1Bound.
            simpl in expr2Bound.
            simpl in floatMaxBound1.
            simpl in resultGe0.
            simpl.
            remember (eval_term (lb x4) st st) as lb1.
            remember (eval_term (lb x5) st st) as lb2.
            remember (eval_term (ub x5) st st) as ub2.
            remember (eval_term (ub x4) st st) as ub1.
            clear Hequb1 Hequb2 Heqlb1 Heqlb2.
            destruct (Rge_dec (x1+x2)%R floatMin).
            {
              assert (floatMinCase3 := r0).
              clear r0.
              (* relative_error*)
              pose proof relative_error as relative_error.
              specialize (relative_error radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) validFexpProof (custom_emin)%Z custom_prec precThm (round_mode mode_NE) (valid_rnd_N choiceDef) (x1 + x2)%R).
              Lemma absHelper: forall x y, (x>=0)%R -> (x>=y)%R -> (y<=(Rabs x))%R.
                intros. unfold Rabs in *. destruct Rcase_abs; psatz R. Qed.
              Lemma posResInf : forall lb1 lb2 x1 x2, (x1 >= lb1 -> x2 >= lb2 -> lb1 + lb2 >=0 -> x1 + x2 >= 0)%R.
                intros. 
                psatz R. Qed.
              intros.
              
              pose proof absHelper as absProof.
              pose proof posResInf as posResInf.
              destruct expr1Bound.
              destruct expr2Bound.
              assert (x1lb := H).
              assert (x1ub := H0).
              assert (x2lb := H1).
              assert (x2ub := H2).
              clear H H0 H1 H2.
              SearchAbout (_<=_->_>=_)%R.
              apply Rle_ge in x1lb.
              apply Rle_ge in x2lb.
              specialize (posResInf lb1 lb2 x1 x2 x1lb x2lb resultGe0).
              specialize (absProof (x1+x2)%R floatMin posResInf floatMinCase3).
              specialize (relative_error absProof).
              (* relative_error *)
              pose proof plusRoundingTruth3 as plusRoundingTruth3.
              specialize (plusRoundingTruth3 x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 ).
              pose proof orExtra as floatMinPremise.
              specialize (floatMinPremise (x1 + x2 >= floatMin)%R (x1 + x2 <= 0 - floatMin)%R floatMinCase3).
              apply Rge_le in x1lb.
              apply Rge_le in x2lb.
              specialize (plusRoundingTruth3 floatMinPremise x1lb x2lb floatMaxBound1).
              pose proof floatMaxBoundHelper as floatMaxBound2.
              specialize (floatMaxBound2 lb1 lb2 floatMax error resultGe0 floatMaxGt0 errorGt0).
              specialize (plusRoundingTruth3 floatMaxBound2 x1ub x2ub).
              pose proof plusRoundingTruth2 as plusRoundingTruth2.
              specialize (plusRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2
                         plusRoundingTruth3).
              rewrite <- plusResultStmt in plusRoundingTruth2.
              remember (  B2R custom_prec custom_emax
                         (B754_zero custom_prec custom_emax b)).
              simpl in Heqr0.
              rewrite Heqr0 in plusRoundingTruth2.
              destruct plusRoundingTruth2.
              clear r0 Heqr0.
              assert (bplusCorrectStmt := H).
              assert (resultFiniteTruth := H0).
              clear H H0.
              clear bplusCorrectStmt resultFiniteTruth plusRoundingTruth3 absProof floatMinPremise floatMinCase1 floatMinCase2 floatMinCase3 floatMaxBound1 floatMaxBound2.
              apply validFloat2 in floatToRealProof1.
              apply validFloat2 in floatToRealProof2.
              pose proof errorGt0.
              psatz R.
            }
            {
              apply Rnot_ge_lt in n.
              Check relative_error.
              Definition el2 (r : radix) (x : R) (lbp : ln_beta_prop r x) : 
                (x <> 0%R -> (bpow r (ln_beta_val r x lbp - 1) <= Rabs x < bpow r (ln_beta_val r x lbp)))%R := let '(Build_ln_beta_prop _ pf) := lbp in pf.
              generalize (el2 radix2 (x1+x2)%R (ln_beta radix2 (x1+x2))).
              intros ln_beta_premise. 
              Lemma subNormal: forall x:R,  (x > R0)%R -> (x < floatMin)%R ->  (ln_beta radix2 x <= custom_emin)%Z.
                intros.
                unfold floatMin in *.
                assert (H1 := H).
                pose proof ln_beta_le_bpow.
                apply Rgt_not_eq in H.
                specialize (H2 radix2 x custom_emin H).
                

                Lemma abs2: forall x0 y : R, (x0 > 0)%R -> (x0 < y)%R -> (Rabs x0 < y)%R.
                  intros. unfold Rabs. destruct Rcase_abs. 
                  psatz R.
                  psatz R.
                Qed.

                intros.
                pose proof abs2.
                specialize (H3 x (bpow radix2 custom_emin) H1 H0).
                specialize (H2 H3).
                apply H2.
              Qed.
              intros. 
              Lemma absImp : forall x, (x > 0)%R-> Rabs x = x.
                intros. unfold Rabs. destruct Rcase_abs. psatz R. psatz R. Qed.
              intros.
              pose proof absImp as absImp.
              pose proof posResInf as posResInf.
              destruct expr1Bound.
              destruct expr2Bound.
              assert (x1lb := H).
              assert (x1ub := H0).
              assert (x2lb := H1).
              assert (x2ub := H2).
              clear H H0 H1 H2.
              apply Rle_ge in x1lb.
              apply Rle_ge in x2lb.
              specialize (posResInf lb1 lb2 x1 x2 x1lb x2lb resultGe0).
              apply Rge_le in posResInf.
              Check Rle_lt_or_eq_dec.
              destruct (Rle_lt_or_eq_dec 0 (x1+x2)%R).
              {
                apply posResInf.
              }
              {
                pose proof subNormal as subNormalProof. 
                apply Rlt_gt in r0.
                specialize (subNormalProof (x1+x2)%R r0 n).
                remember (ln_beta radix2 (x1 + x2)) as ex.
                Lemma gt0ImpNE0 :forall x, (x>0 -> x<>0)%R.
                  intros. psatz R. Qed.
                pose proof gt0ImpNE0 as gt0ImpNE0.
                specialize (gt0ImpNE0 (x1+x2)%R r0).
                specialize (ln_beta_premise gt0ImpNE0).
                Check bpow_lt.
                pose proof bpow_le as bpow_le.
                specialize (bpow_le radix2 ex custom_emin subNormalProof).
                pose proof plusRoundingTruth2.
                Lemma floatMaxProofRounding : 
                  forall x ex, (bpow radix2 (ex - 1) <= Rabs (x) < bpow radix2 ex)%R -> 
                               (ex <= custom_emin)%Z ->
                               (x < floatMin -> x > 0 ->                        
                                (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) x = bpow radix2 ((FLT_exp (3 - custom_emax - custom_prec) custom_prec) ex) \\// round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) x = R0 \\// bpow radix2 (ex - 1)<= round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) x <= bpow radix2 ex) //\\ Rabs (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) x) < bpow radix2 custom_emax)%R.
                  intros. 
                  assert (gt0 := H2).                  
                  apply gt0ImpNE0 in H2.
                  pose proof bpow_le.
                  specialize (H3 radix2 ex custom_emin H0).
                  pose proof emaxGtEmin.
                  SearchAbout (_ > _ -> _ < _)%Z.
                  apply Z.gt_lt in H4.
                  
                  pose proof bpow_lt.
                  specialize (H5 radix2 emin emax H4 ).
                  clear H4.
                  pose proof absImp.
                  specialize (H4 x gt0).
                  rewrite H4 in H.
                  clear H4.
                  destruct (Coqlib.zle ex  (FLT_exp (3 - custom_emax - custom_prec) custom_prec ex)).
                  {
                    pose proof round_bounded_small_pos.
                    specialize (H4 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef) x ex).
                    specialize (H4 l H).
                    remember  (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                     (round_mode mode_NE) x).
                    destruct H4.
                    {
                      rewrite H4 in *.
                      pose proof floatMaxGt0.
                      unfold floatMax in *.
                      unfold Rabs. destruct Rcase_abs.                       
                      split. constructor 2. constructor 1. intuition. 
                      psatz R. split. constructor 2. constructor 1. intuition.
                      psatz R. 
                    }
                    {
                      pose proof bpow_lt.
                      unfold FLT_exp in *.
                      SearchAbout ({_ <= _} + {_ > _ })%Z.
                      destruct (Z_le_gt_dec (ex - custom_prec) (3 - custom_emax - custom_prec)%Z).
                      {
                        Lemma zMaxProof : forall x1 x2, (x1<=x2 -> Z.max x1 x2 = x2)%Z. 
                          intros. SearchAbout Z.max . pose proof Z.max_r. 
                          specialize (H0 x1 x2 H). apply H0.
                        Qed.
                        intros.
                        pose proof zMaxProof as zMaxProof.
                        specialize (zMaxProof (ex - custom_prec)%Z (3 - custom_emax - custom_prec)%Z l0).
                        rewrite zMaxProof in *.
                        
                        clear zMaxProof l0 H6 Heqr. 
                        pose proof errorGt0.
                        unfold error in *.
                        Lemma fexpEminGtEmax :  (3 - custom_emax - custom_prec < custom_emax)%Z.
                          pose proof precGe1. pose proof precLtEmax. unfold error,custom_emax, custom_prec in *. 
                          lia. 
                        Qed.
                        intros.
                        pose proof fexpEminGtEmax as fexpEminGtEmax.
                        pose proof bpow_lt.
                        specialize (H7 radix2 (3 - custom_emax - custom_prec)%Z custom_emax fexpEminGtEmax).
                        split. 
                        constructor 1. apply H4.
                        clear fexpEminGtEmax H H1 H6 l H2 H5.     
                        SearchAbout bpow.
                        pose proof bpow_gt_0.
                        specialize (H radix2 (3 - custom_emax - custom_prec)%Z).
                        pose proof bpow_gt_0.
                        specialize (H1 radix2 custom_emax).
                        unfold Rabs. destruct Rcase_abs. psatz R.   psatz R.
                      }
                      {
                        pose proof zMaxProof as zMaxProof. 
                        SearchAbout (_>_ -> _<_)%Z.
                        apply Z.gt_lt in g.
                        SearchAbout (_<_ -> _<=_)%Z.
                        pose proof Z.lt_le_incl.
                        
                        specialize (H7 (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z g).
                        specialize (zMaxProof   (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z H7).
                        SearchAbout Z.max.
                        rewrite Z.max_comm in zMaxProof.
                        rewrite zMaxProof in *.
                        
                        clear zMaxProof g H7 H6 Heqr. 
                        
                        Lemma fexpEminGtEmax1 : forall ex,  (ex <= custom_emin -> (ex <= ex - custom_prec) -> ex - custom_prec < custom_emax)%Z.
                          intros. unfold custom_emin, custom_prec,custom_emax in *. 
                          pose proof precGe1. pose proof precLtEmax.
                          pose proof emaxGtEmin. lia.
                        Qed.
                        intros.
                        pose proof fexpEminGtEmax1.
                        specialize (H6 ex H0 l).
                        pose proof bpow_lt.
                        specialize (H7 radix2 (ex - custom_prec)%Z custom_emax H6).
                        clear H.
                        pose proof errorGt0. unfold error in *. unfold custom_emax,custom_emin,custom_prec in *.
                        pose proof bpow_gt_0. specialize (H8 radix2 (ex-prec)%Z).
                        split. constructor 1. apply H4.
                        unfold Rabs. destruct Rcase_abs.
                        psatz R. psatz R.
                      }
                    }
                  }
                  {
                    pose proof round_bounded_large_pos.
                    apply Z.gt_lt in g.
                    specialize (H4 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef) x ex g H).
                    remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                    (round_mode mode_NE) x).
                    split. constructor 2. constructor 2. apply H4.
                    unfold custom_emax, custom_prec, custom_emin in *.
                    unfold Rabs. destruct Rcase_abs.
                    pose proof bpow_gt_0.
                    specialize (H6 radix2 ex).
                    pose proof bpow_gt_0.
                    specialize (H7 radix2 (ex-1)%Z).
                    psatz R. psatz R.
                    
                  }
                Qed.


                Lemma floatMaxProof1 : forall x, 
                    (x < floatMin ->
                     x > 0 ->
                     Rabs (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                 (round_mode mode_NE) x) < bpow radix2 custom_emax)%R.
                  intros.
                  generalize (el2 radix2 (x)%R (ln_beta radix2 (x))).
                  intros. 
                  assert (gt0 := H0).
                  apply gt0ImpNE0 in H0.
                  specialize (H1 H0).
                  pose proof subNormal.
                  specialize (H2 x gt0 H).
                  remember (ln_beta radix2 x) as ex.
                  pose proof bpow_le.
                  specialize (H3 radix2 ex custom_emin H2).
                  pose proof emaxGtEmin.
                  SearchAbout (_ > _ -> _ < _)%Z.
                  apply Z.gt_lt in H4.
                  
                  pose proof bpow_lt.
                  specialize (H5 radix2 emin emax H4 ).
                  clear H4.
                  pose proof absImp.
                  specialize (H4 x gt0).
                  rewrite H4 in H1.
                  clear H4.
                  destruct (Coqlib.zle ex  (FLT_exp (3 - custom_emax - custom_prec) custom_prec ex)).
                  {
                    pose proof round_bounded_small_pos.
                    specialize (H4 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef) x ex).
                    specialize (H4 l H1).
                    remember  (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                     (round_mode mode_NE) x).
                    destruct H4.
                    {
                      rewrite H4 in *.
                      pose proof floatMaxGt0.
                      unfold floatMax in *.
                      unfold Rabs. destruct Rcase_abs.                       
                      psatz R. psatz R.
                    }
                    {
                      pose proof bpow_lt.
                      unfold FLT_exp in *.
                      SearchAbout ({_ <= _} + {_ > _ })%Z.
                      destruct (Z_le_gt_dec (ex - custom_prec) (3 - custom_emax - custom_prec)%Z).
                      {
                        intros.
                        pose proof zMaxProof as zMaxProof.
                        specialize (zMaxProof (ex - custom_prec)%Z (3 - custom_emax - custom_prec)%Z l0).
                        rewrite zMaxProof in H4.
                        clear zMaxProof l0 H6 Heqr. 
                        pose proof errorGt0.
                        unfold error in *.
                        intros.
                        pose proof fexpEminGtEmax as fexpEminGtEmax.
                        pose proof bpow_lt.
                        specialize (H7 radix2 (3 - custom_emax - custom_prec)%Z custom_emax fexpEminGtEmax).
                        clear fexpEminGtEmax H H1 H6 l H2 H5.     
                        SearchAbout bpow.
                        pose proof bpow_gt_0.
                        specialize (H radix2 (3 - custom_emax - custom_prec)%Z).
                        pose proof bpow_gt_0.
                        specialize (H1 radix2 custom_emax).
                        unfold Rabs. destruct Rcase_abs. psatz R. psatz R.
                      }
                      {
                        pose proof zMaxProof as zMaxProof. 
                        SearchAbout (_>_ -> _<_)%Z.
                        apply Z.gt_lt in g.
                        SearchAbout (_<_ -> _<=_)%Z.
                        pose proof Z.lt_le_incl.
                        
                        specialize (H7 (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z g).
                        specialize (zMaxProof   (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z H7).
                        SearchAbout Z.max.
                        rewrite Z.max_comm in zMaxProof.
                        rewrite zMaxProof in l, H4.
                        
                        clear zMaxProof g H7 H6 Heqr. 
                        
                        intros.
                        pose proof fexpEminGtEmax1.
                        specialize (H6 ex H2 l).
                        pose proof bpow_lt.
                        specialize (H7 radix2 (ex - custom_prec)%Z custom_emax H6).
                        clear H.
                        pose proof errorGt0. unfold error in *. unfold custom_emax,custom_emin,custom_prec in *.
                        pose proof bpow_gt_0. specialize (H8 radix2 (ex-prec)%Z).
                        unfold Rabs. destruct Rcase_abs.
                        psatz R. psatz R.
                      }
                    }
                  }
                  {
                    pose proof round_bounded_large_pos.
                    apply Z.gt_lt in g.
                    specialize (H4 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef) x ex g H1).
                    remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                    (round_mode mode_NE) x).
                    unfold custom_emax, custom_prec, custom_emin in *.
                    unfold Rabs. destruct Rcase_abs.
                    pose proof bpow_gt_0.
                    specialize (H6 radix2 ex).
                    pose proof bpow_gt_0.
                    specialize (H7 radix2 (ex-1)%Z).
                    psatz R. psatz R.
                    
                  }
                Qed.
                intros.
                pose proof floatMaxProofRounding.
                specialize (H0 (x1 +x2)%R ex ln_beta_premise subNormalProof n r0).
                apply validFloat2 in floatToRealProof1.
                apply validFloat2 in floatToRealProof2.
                
                specialize (H x x0 x1 x2 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                rewrite <- floatToRealProof1 in H.
                rewrite <- floatToRealProof2 in H.
                destruct H0.
                specialize (H H1).
                destruct H.
                rewrite <- plusResultStmt in H.
                unfold B2R in H.
                rewrite H.
                remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                (round_mode mode_NE) (x1 + x2)) as roundedValue.
                destruct H0.
                {
                  unfold FLT_exp in H0.
                  destruct (Z_le_gt_dec (ex - custom_prec) (3 - custom_emax - custom_prec)%Z).
                  {
                    pose proof zMaxProof as zMaxProof.
                    specialize (zMaxProof (ex - custom_prec)%Z (3 - custom_emax - custom_prec)%Z l).
                    rewrite zMaxProof in *.
                    clear zMaxProof.  
                    
                    pose proof customEminMinValue as customEminMinValue.
                    SearchAbout (_ > _ -> _ < _)%Z.
                    apply Z.gt_lt in customEminMinValue.
                    pose proof bpow_lt.
                    specialize (H3 radix2 (3 - custom_emax - custom_prec)%Z custom_emin customEminMinValue).
                    unfold floatMin in *.
                    unfold error, custom_emin,custom_emax, custom_prec in *.
                    pose proof bpow_gt_0 as bpowGt0_1.
                    specialize (bpowGt0_1 radix2 (- prec + 1)%Z)%R.
                    clear H H2 H1 l customEminMinValue ln_beta_premise floatToRealProof1 floatToRealProof2 absImp posResInf.
                    split.
                    pose proof bpow_gt_0 as bpow_gt_0_2.
                    specialize (bpow_gt_0_2 radix2 (3-emax-prec)%Z).
                    psatz R.
                    psatz R.
                  }
                  {
                    pose proof zMaxProof as zMaxProof.
                    Lemma zlt_le : forall x1 x2, (x1 > x2 -> x1 >= x2)%Z.
                      intros.
                      lia.
                    Qed.
                    intros.
                    apply zlt_le in g.
                    apply Z.ge_le in g.
                    specialize (zMaxProof (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z g).
                    SearchAbout Z.max.
                    pose proof Z.max_comm.
                    specialize (H3 (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z).
                    rewrite <- H3 in H0.
                    rewrite zMaxProof in *.
                    clear zMaxProof H3 g.
                    Lemma exCustomPrec : forall x, (x <= custom_emin ->  custom_prec >=1 -> x - custom_prec  < custom_emin)%Z. 
                      intros. lia. 
                    Qed.
                    intros.
                    specialize (exCustomPrec ex subNormalProof custom_precGe1).
                    intros.
                    pose proof bpow_lt.
                    specialize (H4 radix2 (ex-custom_prec)%Z custom_emin H3).
                    pose proof bpow_gt_0.
                    specialize (H5 radix2 (ex - prec)%Z ).
                    pose proof bpow_gt_0.
                    specialize (H6 radix2 (- prec +1)%Z).
                    unfold floatMin, error, custom_emin,custom_emax, custom_prec in *.
                    psatz R.
                    
                  }
                }
                {
                  destruct H0.
                  {
                    unfold floatMin in *.
                    pose proof bpow_gt_0.
                    specialize (H3 radix2 custom_emin).
                    unfold error in *.
                    pose proof bpow_gt_0.
                    specialize (H4 radix2 (-custom_prec +1)%Z).
                    psatz R.
                  }
                  {
                    unfold floatMin in *.
                    pose proof bpow_gt_0.
                    specialize (H3 radix2 custom_emin).
                    unfold error in *.
                    pose proof bpow_gt_0.
                    specialize (H4 radix2 (-custom_prec +1)%Z).
                    pose proof bpow_gt_0.
                    specialize (H5 radix2 (ex -1 )%Z).
                    pose proof bpow_gt_0.
                    specialize (H6 radix2 (ex)%Z ).
                    psatz R.
                  }
                }
              }
              {
                pose proof plusRoundingTruth2.
                pose proof round_0 as round_0.
                specialize (round_0 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef)).
                Lemma zeroLtFloatMax : forall x, (x = 0 -> Rabs x <floatMax)%R .
                  intros.  unfold Rabs in *. destruct Rcase_abs; unfold floatMax in *;
                  pose proof bpow_gt_0;
                  specialize (H0 radix2 custom_emax);
                  psatz R.
                Qed.
                pose proof zeroLtFloatMax.
                specialize (H0 (round radix2
                                      (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                      (round_mode mode_NE) 0) round_0).
                apply validFloat2 in floatToRealProof1.
                apply validFloat2 in floatToRealProof2.
                unfold floatMax in *.
                specialize (H x x0 x1 x2 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                rewrite <- floatToRealProof1 in H.
                rewrite <- floatToRealProof2 in H.
                unfold floatMin in *.
                pose proof bpow_gt_0.
                specialize (H1 radix2 custom_emin).
                pose proof errorGt0.
                psatz R.
              }
            }
          }
          {
            destruct H0.
            {
              rewrite <- H0 in H.
              simpl in H.
              rewrite <- H0.
              decompose [and] H.
              clear H9.
              assert (H8:=H7).
              clear H7.
              apply IHexpr1 in H1.
              apply IHexpr2 in H3.
              assert (expr1Bound := H1).
              assert (expr2Bound := H3).
              assert (floatMinCase1 := H2).
              assert (floatMaxBound1 := H6).
              assert (resultGe0 := H8).
              clear H1 H2 H3 H6 H8 H IHexpr1 IHexpr2.
              unfold Semantics.eval_comp in *.
              simpl in *.
              remember (eval_term (lb x4) st st) as lb1.
              remember (eval_term (lb x5) st st) as lb2.
              remember (eval_term (ub x5) st st) as ub2.
              remember (eval_term (ub x4) st st) as ub1.
              clear Hequb1 Hequb2 Heqlb1 Heqlb2.
              destruct (Rle_dec floatMin (x1+x2)%R).
              {
                psatz R.
              }
              {
                SearchAbout (~(_<=_) -> (_>_))%R.
                apply Rnot_le_gt in n.
                pose proof floatMaxProofRounding as floatMaxProofRounding.
                generalize (el2 radix2 (x1+x2)%R (ln_beta radix2 (x1+x2)%R)).
                intros.
                destruct (Rle_lt_or_eq_dec 0 (x1+x2)%R).
                {
                  psatz R.
                }
                {
                  assert (resultNe0 := r0).                
                  apply RMicromega.Rlt_neq in resultNe0.
                  assert (ln_beta_premise :=H).
                  clear H.
                  specialize (ln_beta_premise resultNe0).
                  remember (ln_beta radix2 (x1 + x2)) as ex.
                  specialize (floatMaxProofRounding (x1 + x2)%R ex ln_beta_premise).
                  pose proof subNormal as subNormalProof.
                  apply Rlt_gt in r0.
                  apply Rgt_lt in n.
                  specialize (subNormalProof (x1+x2)%R r0 n).
                  rewrite <- Heqex in subNormalProof.
                  specialize (floatMaxProofRounding subNormalProof n r0).
                  destruct floatMaxProofRounding.
                  pose proof plusRoundingTruth2 as plusRoundingTruth2.
                  apply validFloat2 in floatToRealRelationForExpr1.
                  apply validFloat2 in floatToRealRelationForExpr2.
                  specialize (plusRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2).
                  rewrite <- floatToRealRelationForExpr1 in plusRoundingTruth2.
                  rewrite <- floatToRealRelationForExpr2 in plusRoundingTruth2.
                  specialize (plusRoundingTruth2 H1).
                  destruct plusRoundingTruth2.
                  rewrite <- plusResultStmt in H2.
                  unfold B2R in H2.
                  rewrite H2 in *.
                  remember ( round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                   (round_mode mode_NE) (x1 + x2)) as roundedValue.
                  destruct H.
                  {
                    unfold FLT_exp in H.
                    Lemma roundedValLessThanFloatMin: forall ex, ((ex <=custom_emin)%Z -> (bpow radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec ex) <= floatMin))%R. 
                      intros.
                      unfold FLT_exp. 
                      destruct (Coqlib.zle (3 - custom_emax - custom_prec) (ex-custom_prec)).
                      {
                        SearchAbout Z.max.
                        pose proof Z.max_l.
                        specialize (H0 (ex-custom_prec)%Z (3 - custom_emax - custom_prec)%Z l).
                        rewrite H0.
                        unfold floatMin.
                        Lemma exHelper : forall x, (x <= custom_emin -> x - custom_prec <custom_emin)%Z. 
                          intros. unfold custom_prec, custom_emin in *.
                          pose proof precGe1.
                          lia.
                        Qed.
                        specialize (exHelper ex H).
                        intros.
                        pose proof bpow_lt.
                        specialize (H2 radix2 (ex - custom_prec)%Z custom_emin H1).
                        psatz R.
                      }
                      {
                        pose proof Z.max_r.
                        SearchAbout (_>_ -> _ >= _)%Z.
                        apply zlt_le in g.
                        SearchAbout (_>=_ -> _<=_)%Z.
                        apply Z.ge_le in g.
                        specialize (H0 (ex - custom_prec)%Z (3 - custom_emax - custom_prec)%Z g).
                        rewrite H0.
                        unfold floatMin.
                        unfold custom_emin,custom_prec, custom_emax in *.
                        pose proof eminMinValue.
                        SearchAbout (_>_ -> _<_)%Z.
                        apply Z.gt_lt in H1.
                        pose proof bpow_lt.
                        specialize (H2 radix2  (3 - emax - prec)%Z emin H1).
                        psatz R.
                      }
                    Qed.
                    intros.
                    pose proof roundedValLessThanFloatMin.
                    specialize (H6 ex subNormalProof).
                    unfold FLT_exp in H6.
                    pose proof bpow_gt_0.
                    specialize (H7 radix2 (Z.max (ex - custom_prec) (3 - custom_emax - custom_prec))).
                    psatz R.
                  }  
                  {
                    destruct H.
                    {
                      unfold floatMin.
                      pose proof bpow_gt_0.
                      specialize (H6 radix2 custom_emin).
                      psatz R.
                    }
                    {
                      pose proof bpow_le.
                      specialize (H6 radix2 ex custom_emin subNormalProof).
                      pose proof bpow_gt_0.
                      specialize (H7 radix2 (ex-1)%Z).
                      unfold floatMin.
                      psatz R.
                    }

                  }
                }
                {
                  unfold floatMin.
                  pose proof bpow_gt_0.
                  specialize (H1 radix2 custom_emin).
                  psatz R.
                }
                
               
              }
            }
            {
              intuition.
            }
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
      assert (plusResultStmt := H9).
      assert (floatToRealRelationForExpr1:= H2).
      assert (floatToRealRelationForExpr2:= H3).
      clear H f Heqo0 H0 H1 H8 f_des Heqo' H9 H10 .
      assert (floatToRealProof1:= H2).
      assert (floatToRealProof2:= H3).
      clear H2 H3.
      
      
      unfold denote_singleBoundTerm in *.
      intros H.
      simpl in H6.
      unfold simpleBound in *.
      unfold simpleBound4 in *.
      destruct H6.
      
      {
        rewrite <- H0 in H.
        simpl in H.

        rewrite <- H0.
        decompose [and] H.
        clear H9.
        apply IHexpr1 in H1.
        apply IHexpr2 in H3.
        assert (expr1Bound := H1).
        assert (expr2Bound := H3).
        assert (floatMinCase := H2).
        assert (floatMaxBound1 := H6).
        assert (resultGe0 := H7).
        clear H4 H2 H1 H3 H H5 H0 H7 H6 IHexpr1 IHexpr2.
        unfold Semantics.eval_comp in *.
        simpl in floatMinCase.
        simpl in expr1Bound.
        simpl in expr2Bound.
        simpl in floatMaxBound1.
        simpl in resultGe0.
        simpl.
        remember (eval_term (lb x4) st st) as lb1.
        remember (eval_term (lb x5) st st) as lb2.
        remember (eval_term (ub x5) st st) as ub2.
        remember (eval_term (ub x4) st st) as ub1.
        clear Hequb1 Hequb2 Heqlb1 Heqlb2.
        pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
        specialize (relErrorBasedOnFloatMinTruthPlus x1 x2 lb1 lb2 ub1 ub2).
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        intros.
        assert (partialFloatMinCase := floatMinCase).
        clear floatMinCase.
        pose proof orExtra as floatMinCase.
        specialize (floatMinCase ((floatMin <= lb1 + lb2)%R) ((floatMin <= 0 - ub1 + (0 - ub2))%R) partialFloatMinCase).
        specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H H1 H0 H2).
        pose proof plusRoundingTruth as plusRoundingTruth.
        pose proof floatMaxBoundHelper as floatMaxBound2.
        specialize (floatMaxBound2 lb1 lb2 floatMax error resultGe0 floatMaxGt0 errorGt0). 
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
        rewrite H4.
        clear H5.
        clear plusRoundingTruth2.
        assert (plusRoundingTruth2:= H4).
        clear H4.
        clear plusResultStmt.
        clear H3.
        clear plusRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear floatMinCase floatMaxBound1 floatMaxBound2 HeqroundedValue
              plusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2 x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
        unfold error in *.
        unfold Rabs in *.
        pose proof errorLessThan1 as errorLessThan1.
        unfold error in *.
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
      
    (*getting the relative error proof*)
    (*
        remember (x1 + x2)%R as realResult. 
        destruct (Rge_dec realResult floatMin) .
        {
`          pose proof relative_error as relative_error.
          remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp.
          
          specialize (relative_error radix2 round_fexp). 
          rewrite Heqround_fexp in relative_error.
          specialize (relative_error validFexpProof  (custom_emin)%Z custom_prec  precThm (round_mode mode_NE)).
          specialize (relative_error (valid_rnd_N choiceDef) (x1+x2)%R).
          
          intros.
          pose proof orExtra as absPremise.
          specialize (absPremise  (realResult >= floatMin)%R  (realResult <= (0 - floatMin))%R r0).
          pose proof abs as absProof.
          specialize (absProof realResult floatMin absPremise).
          rewrite HeqrealResult in absProof.
          unfold floatMin in absProof.
          specialize (relative_error absProof).
          (*getting the relative error proof*)
          

          pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
          specialize (relErrorBasedOnFloatMinTruthPlus x1 x2 lb1 lb2 ub1 ub2).
          destruct expr1Bound.
          destruct expr2Bound.
          pose proof or_introl.
          
          intros.
          assert (floatMinCase1 := floatMinCase).
          clear floatMinCase.
          pose proof orExtra as floatMinCase. 
          specialize (floatMinCase (floatMin <= lb1 + lb2)%R  (floatMin <= 0 - ub1 + (0 - ub2))%R floatMinCase1).
          clear floatMinCase1.
          specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H H1 H0 H2).

          
          pose proof plusRoundingTruth3 as plusRoundingTruth3.
          specialize (plusRoundingTruth3 x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 ).
          apply validFloat2 in floatToRealProof1.
          apply validFloat2 in floatToRealProof2.
          rewrite <- floatToRealProof1 in plusRoundingTruth3.
          rewrite <- floatToRealProof2 in plusRoundingTruth3.
          rewrite HeqrealResult in absPremise.
          specialize (plusRoundingTruth3 absPremise H H1 floatMaxBound1 floatMaxBound2 H0 H2).
          


          pose proof plusRoundingTruth2 as plusRoundingTruth2.
          rewrite floatToRealProof1 in plusRoundingTruth3.
          rewrite floatToRealProof2 in plusRoundingTruth3.
          specialize (plusRoundingTruth2 x x0 x1 x2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 plusRoundingTruth3).
          revert plusResultStmt. intros plusResultStmt.
          rewrite <- floatToRealProof1 in plusRoundingTruth3,plusRoundingTruth2.
          rewrite <- floatToRealProof2 in plusRoundingTruth3,plusRoundingTruth2.
          

          remember ( round radix2
                           (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                           (round_mode mode_NE)
                           (x1 +x2)) as roundedValue. 
          clear relErrorBasedOnFloatMinTruthPlus.
          
          rewrite <- plusResultStmt in plusRoundingTruth2.
          unfold B2R in plusRoundingTruth2.
          decompose [and] plusRoundingTruth2.
          rewrite  H4.
          pose proof errorGt0.
          clear H4 H3 H5 plusRoundingTruth2 plusRoundingTruth3 plusResultStmt floatMinCase floatMaxBound1 floatMaxBound2 HeqroundedValue floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2 e0 e x3 x4 x4 x5 x0 expr1 expr2 tr fState b m r.
          pose proof errorLessThan1.
          unfold error in *.
          unfold Rabs in *.
          clear Heqround_fexp absPremise absProof r0.
          destruct Rcase_abs; destruct Rcase_abs;
          psatz R.
        }
        {
          apply Rnot_ge_gt in n.
          Check bpow.
          Check ln_beta
          Lemma subNormal: forall x:R,  (x > R0)%R -> (x < floatMin)%R ->  (ln_beta radix2 x <= custom_emin)%Z.
            intros.
            unfold floatMin in *.
            assert (H1 := H).
            pose proof ln_beta_le_bpow.
            apply Rgt_not_eq in H.
            specialize (H2 radix2 x custom_emin H).
            

            Lemma abs2: forall x0 y : R, (x0 > 0)%R -> (x0 < y)%R -> (Rabs x0 < y)%R.
              intros. unfold Rabs. destruct Rcase_abs. 
              psatz R.
              psatz R.
            Qed.

            intros.
            pose proof abs2.
            specialize (H3 x (bpow radix2 custom_emin) H1 H0).
            specialize (H2 H3).
            apply H2.
          Qed.
          
          intros.
          pose proof subNormal.
          specialize (H (x1+x2)%R).
          Definition el2 (r : radix) (x : R) (lbp : ln_beta_prop r x) : 
            (x <> 0%R -> (bpow r (ln_beta_val r x lbp - 1) <= Rabs x < bpow r (ln_beta_val r x lbp)))%R := let '(Build_ln_beta_prop _ pf) := lbp in pf.
          generalize (el2 radix2 (x1+x2)%R (ln_beta radix2 (x1+x2))).
          intros.

          Lemma realBound : forall lb1 lb2 ub1 ub2 x1 x2, (lb1 <= x1 <= ub1 )%R ->
                                                          (lb2 <= x2 <= ub2)%R -> 
                                                          (lb1 + lb2 >=0)%R -> (x1 + x2 >=0)%R.
          Proof. intros. psatz R. Qed.
          pose proof realBound as realBound.
          specialize (realBound lb1 lb2 ub1 ub2 x1 x2 expr1Bound expr2Bound resultGe0).
          SearchAbout bpow. 
          Check bpow_lt.
          Lemma ltFminImpLtFmax : forall x, (x < floatMin -> x < floatMax)%R.
            Proof.
              intros. unfold floatMin, floatMax in *. pose proof bpow_lt. pose proof custom_emaxGtCustom_emin. specialize (H0 radix2 custom_emin custom_emax).  apply Z.gt_lt in H1. specialize (H0 H1). 
clear H1. psatz R. Qed.
            
            intros.
            SearchAbout ((_>_) -> (_<_))%R.
            apply Rgt_lt in n.
            assert (resultLtFmin:= n).
            apply ltFminImpLtFmax in n.
            assert (resultLtFmax :=n);clear n.
            specialize (resultLtFmax ).

            
            destruct (Rle_lt_or_eq_dec R0 (x1+x2)%R).
            {
              apply Rge_le in realBound.
              apply realBound.
            }
            {
              apply Rlt_gt in r0.
              rewrite HeqrealResult in resultLtFmin.
              apply Rgt_lt in resultLtFmin.
              specialize (H r0 resultLtFmin).
              Lemma helper: forall x1 x2:R, (x1+x2 > 0)%R -> (x1 + x2)%R <> R0.
                intros.
                psatz R.
              Qed.
              assert (resGt0 := r0).
              apply helper in r0.
              specialize (H0 r0).
              SearchAbout ({_ <= _} + {_ > _ })%Z.
              destruct (Coqlib.zle (ln_beta radix2 (x1 + x2)) (FLT_exp (3 - custom_emax - custom_prec) custom_prec (ln_beta radix2 (x1 + x2)))).
              
              pose proof round_bounded_small_pos as round_bound.
              specialize (round_bound radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) 
                                      (round_mode mode_NE) (valid_rnd_N choiceDef) (x1+x2)%R  (ln_beta radix2 (x1 + x2)) l) .
              
              Lemma helper1 : forall x y1 y2, (x > 0)%R ->(y1 <= Rabs x < y2  -> y1 <= x < y2)%R.  
                intros. unfold Rabs in *. destruct Rcase_abs. 
                psatz R. psatz R.
              Qed.
              intros.
              pose proof helper1 as helper1.
              
              specialize (helper1 (x1+x2)%R (bpow radix2 ((ln_beta radix2 (x1 + x2)) - 1)) (bpow radix2 (ln_beta radix2 (x1 + x2))) resGt0 H0).
              specialize (round_bound helper1).
              pose proof plusRoundingTruth2.
              Lemma powRelation : forall x y z, (x <= y)%Z -> (y<z)%Z -> (x<z)%Z.  
                intros. lia. Qed.
              intros.
              pose proof custom_emaxGtCustom_emin.
              SearchAbout ((_ > _) -> ( _ < _) )%Z.
              apply Z.gt_lt in H2.
              specialize (powRelation (ln_beta radix2 (x1 + x2)) custom_emin custom_emax H H2).
              intros.
              pose proof bpow_lt.
              specialize (H4 radix2 (ln_beta radix2 (x1 + x2)) custom_emax H3).
              Check relative_error.
              (*need to start from here. need to prove that in round_bound evalution to both things in the or condition, will have the result being less than the maximum float Value*)
              destruct (Zle_dec (ln_beta radix2 (x1 + x2)) (FLT_exp (3 - custom_emax - custom_prec) custom_prec (ln_beta radix2 (x1 + x2)))).
              specialize (round_bound helper1).
              apply helper2 in H0.
              intros.
              specialize (helper1 (x1+x2)%R (bpow radix2 (ln - 1)) (bpow radix2 ln) resGt0 H0).
              
              intros.
            SearchAbout bpow.
            
            generalize ().
          }

                   
                   

          remember (ln_beta radix2 (x1+x2)%R).
          SearchAbout ln_beta.
          apply ln_beta_unique in Heql.
          compute in H.
          

          pose proof round_bounded_small_pos as.
     *)

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
          assert (resultGe0 := H7).
          clear H4 H2 H1 H3 H H5 H0 H7 H6 H9 IHexpr1 IHexpr2.
          unfold Semantics.eval_comp in *.
          simpl in floatMinCase.
          simpl in expr1Bound.
          simpl in expr2Bound.
          simpl in floatMaxBound1.
          simpl in resultGe0.
          simpl.
          remember (eval_term (lb x4) st st) as lb1.
          remember (eval_term (lb x5) st st) as lb2.
          remember (eval_term (ub x5) st st) as ub2.
          remember (eval_term (ub x4) st st) as ub1.
          clear Hequb1 Hequb2 Heqlb1 Heqlb2.
          pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
          specialize (relErrorBasedOnFloatMinTruthPlus x1 x2 lb1 lb2 ub1 ub2).
          destruct expr1Bound.
          destruct expr2Bound.
          pose proof or_introl.
          
          intros.
          assert (floatMinCase1 := floatMinCase).
          clear floatMinCase.
          pose proof orExtra2 as floatMinCase. 
          specialize (floatMinCase (floatMin <= lb1 + lb2)%R  (floatMin <= 0 - ub1 + (0 - ub2))%R floatMinCase1).
          clear floatMinCase1.
          specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H H1 H0 H2).
          pose proof plusRoundingTruth as plusRoundingTruth.
          pose proof floatMaxBoundHelper2 as floatMaxBound2.
          specialize (floatMaxBound2 ub1 ub2 floatMax error resultGe0 floatMaxGt0 errorGt0).
          
          specialize (plusRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 floatMinCase H H1 floatMaxBound2 floatMaxBound1 H0 H2).
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
            assert (floatMinCase1 := H2).
            assert (floatMinCase2 := H6).
            assert (floatMaxBound1 := H7).
            assert (resultGe0 := H8).
            clear H4 H2 H1 H3 H H5 H0 H7 H8 H10 H6 IHexpr1 IHexpr2.
            unfold Semantics.eval_comp in *.
            simpl in floatMinCase1.
            simpl in floatMinCase2.
            simpl in expr1Bound.
            simpl in expr2Bound.
            simpl in floatMaxBound1.
            simpl in resultGe0.
            simpl.
            remember (eval_term (lb x4) st st) as lb1.
            remember (eval_term (lb x5) st st) as lb2.
            remember (eval_term (ub x5) st st) as ub2.
            remember (eval_term (ub x4) st st) as ub1.
            clear Hequb1 Hequb2 Heqlb1 Heqlb2.
            destruct (Rge_dec (x1+x2)%R floatMin).
            {
              assert (floatMinCase3 := r0).
              clear r0.
              (* relative_error*)
              pose proof relative_error as relative_error.
              specialize (relative_error radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) validFexpProof (custom_emin)%Z custom_prec precThm (round_mode mode_NE) (valid_rnd_N choiceDef) (x1 + x2)%R).
              intros.
              
              pose proof absHelper as absProof.
              pose proof posResInf as posResInf.
              destruct expr1Bound.
              destruct expr2Bound.
              assert (x1lb := H).
              assert (x1ub := H0).
              assert (x2lb := H1).
              assert (x2ub := H2).
              clear H H0 H1 H2.
              SearchAbout (_<=_->_>=_)%R.
              apply Rle_ge in x1lb.
              apply Rle_ge in x2lb.
              specialize (posResInf lb1 lb2 x1 x2 x1lb x2lb resultGe0).
              specialize (absProof (x1+x2)%R floatMin posResInf floatMinCase3).
              specialize (relative_error absProof).
              (* relative_error *)
              pose proof plusRoundingTruth3 as plusRoundingTruth3.
              specialize (plusRoundingTruth3 x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 ).
              pose proof orExtra as floatMinPremise.
              specialize (floatMinPremise (x1 + x2 >= floatMin)%R (x1 + x2 <= 0 - floatMin)%R floatMinCase3).
              apply Rge_le in x1lb.
              apply Rge_le in x2lb.
              specialize (plusRoundingTruth3 floatMinPremise x1lb x2lb floatMaxBound1).
              pose proof floatMaxBoundHelper as floatMaxBound2.
              specialize (floatMaxBound2 lb1 lb2 floatMax error resultGe0 floatMaxGt0 errorGt0).
              specialize (plusRoundingTruth3 floatMaxBound2 x1ub x2ub).
              pose proof plusRoundingTruth2 as plusRoundingTruth2.
              specialize (plusRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2
                         plusRoundingTruth3).
              rewrite <- plusResultStmt in plusRoundingTruth2.
              remember ( B2R custom_prec custom_emax
                         (B754_finite custom_prec custom_emax b m e e0)).
              simpl in Heqr0.
              rewrite Heqr0 in plusRoundingTruth2.
              destruct plusRoundingTruth2.
              clear r0 Heqr0.
              assert (bplusCorrectStmt := H).
              assert (resultFiniteTruth := H0).
              clear H H0.
              rewrite (bplusCorrectStmt).
              clear bplusCorrectStmt resultFiniteTruth plusRoundingTruth3 absProof floatMinPremise floatMinCase1 floatMinCase2 floatMinCase3 floatMaxBound1 floatMaxBound2.
              apply validFloat2 in floatToRealProof1.
              apply validFloat2 in floatToRealProof2.
              rewrite <- floatToRealProof1.
              rewrite <- floatToRealProof2.
              Lemma boundUsingRelativeErrorProof : forall lb1 lb2 ub1 ub2 x1 x2, 
                  (lb1 <= x1 ->
                  x1 <= ub1 -> 
                  lb2 <= x2 ->
                  x2 <= ub2 -> 
                  lb1 + lb2 >= 0 ->
                  (Rabs
                     (round radix2
                            (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                            (round_mode mode_NE) (x1 + x2) - 
                      (x1 + x2)) <
                   bpow radix2 (- custom_prec + 1) * Rabs (x1 + x2))%R 

                  ->
                  
                  0 <=
                  round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                        (round_mode mode_NE)
                        (x1 + x2) <=
                  (ub1 + ub2) * (1 + error))%R.
                intros.
                remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
         (round_mode mode_NE) (x1 + x2))%R as roundedValue.
                pose proof errorGt0 as errorGt0.
                pose proof errorLessThan1 as errorLessThan1.
                clear HeqroundedValue.
                unfold error in *.
                unfold Rabs in *. destruct Rcase_abs; destruct Rcase_abs;
                psatz R. Qed.
              intros.
              pose proof boundUsingRelativeErrorProof as boundUsingRelativeErrorProof.
              specialize (boundUsingRelativeErrorProof lb1 lb2 ub1 ub2 x1 x2 x1lb x1ub x2lb x2ub resultGe0 relative_error).
              apply boundUsingRelativeErrorProof.
            }
            {
              apply Rnot_ge_lt in n.
              Check relative_error.
              generalize (el2 radix2 (x1+x2)%R (ln_beta radix2 (x1+x2))).
              intros ln_beta_premise. 
              
              intros. 
              intros.
              pose proof absImp as absImp.
              pose proof posResInf as posResInf.
              destruct expr1Bound.
              destruct expr2Bound.
              assert (x1lb := H).
              assert (x1ub := H0).
              assert (x2lb := H1).
              assert (x2ub := H2).
              clear H H0 H1 H2.
              apply Rle_ge in x1lb.
              apply Rle_ge in x2lb.
              specialize (posResInf lb1 lb2 x1 x2 x1lb x2lb resultGe0).
              apply Rge_le in posResInf.
              Check Rle_lt_or_eq_dec.
              destruct (Rle_lt_or_eq_dec 0 (x1+x2)%R).
              {
                apply posResInf.
              }
              {
                pose proof subNormal as subNormalProof. 
                apply Rlt_gt in r0.
                specialize (subNormalProof (x1+x2)%R r0 n).
                remember (ln_beta radix2 (x1 + x2)) as ex.
                pose proof gt0ImpNE0 as gt0ImpNE0.
                specialize (gt0ImpNE0 (x1+x2)%R r0).
                specialize (ln_beta_premise gt0ImpNE0).
                Check bpow_lt.
                pose proof bpow_le as bpow_le.
                specialize (bpow_le radix2 ex custom_emin subNormalProof).
                pose proof plusRoundingTruth2.
                

                intros.
                pose proof floatMaxProofRounding.
                specialize (H0 (x1 +x2)%R ex ln_beta_premise subNormalProof n r0).
                apply validFloat2 in floatToRealProof1.
                apply validFloat2 in floatToRealProof2.
                
                specialize (H x x0 x1 x2 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                rewrite <- floatToRealProof1 in H.
                rewrite <- floatToRealProof2 in H.
                destruct H0.
                specialize (H H1).
                destruct H.
                rewrite <- plusResultStmt in H.
                unfold B2R in H.
                rewrite H.
                remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                (round_mode mode_NE) (x1 + x2)) as roundedValue.
                destruct H0.
                {
                  unfold FLT_exp in H0.
                  destruct (Z_le_gt_dec (ex - custom_prec) (3 - custom_emax - custom_prec)%Z).
                  {
                    pose proof zMaxProof as zMaxProof.
                    specialize (zMaxProof (ex - custom_prec)%Z (3 - custom_emax - custom_prec)%Z l).
                    rewrite zMaxProof in *.
                    clear zMaxProof.  
                    
                    pose proof customEminMinValue as customEminMinValue.
                    SearchAbout (_ > _ -> _ < _)%Z.
                    apply Z.gt_lt in customEminMinValue.
                    pose proof bpow_lt.
                    specialize (H3 radix2 (3 - custom_emax - custom_prec)%Z custom_emin customEminMinValue).
                    unfold floatMin in *.
                    unfold error, custom_emin,custom_emax, custom_prec in *.
                    pose proof bpow_gt_0 as bpowGt0_1.
                    specialize (bpowGt0_1 radix2 (- prec + 1)%Z)%R.
                    clear H H2 H1 l customEminMinValue ln_beta_premise floatToRealProof1 floatToRealProof2 absImp posResInf.
                    split.
                    pose proof bpow_gt_0 as bpow_gt_0_2.
                    specialize (bpow_gt_0_2 radix2 (3-emax-prec)%Z).
                    psatz R.
                    psatz R.
                  }
                  {
                    pose proof zMaxProof as zMaxProof.
                    intros.
                    apply zlt_le in g.
                    apply Z.ge_le in g.
                    specialize (zMaxProof (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z g).
                    SearchAbout Z.max.
                    pose proof Z.max_comm.
                    specialize (H3 (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z).
                    rewrite <- H3 in H0.
                    rewrite zMaxProof in *.
                    clear zMaxProof H3 g.
                    intros.
                    specialize (exCustomPrec ex subNormalProof custom_precGe1).
                    intros.
                    pose proof bpow_lt.
                    specialize (H4 radix2 (ex-custom_prec)%Z custom_emin H3).
                    pose proof bpow_gt_0.
                    specialize (H5 radix2 (ex - prec)%Z ).
                    pose proof bpow_gt_0.
                    specialize (H6 radix2 (- prec +1)%Z).
                    unfold floatMin, error, custom_emin,custom_emax, custom_prec in *.
                    psatz R.
                    
                  }
                }
                {
                  destruct H0.
                  {
                    unfold floatMin in *.
                    pose proof bpow_gt_0.
                    specialize (H3 radix2 custom_emin).
                    unfold error in *.
                    pose proof bpow_gt_0.
                    specialize (H4 radix2 (-custom_prec +1)%Z).
                    psatz R.
                  }
                  {
                    unfold floatMin in *.
                    pose proof bpow_gt_0.
                    specialize (H3 radix2 custom_emin).
                    unfold error in *.
                    pose proof bpow_gt_0.
                    specialize (H4 radix2 (-custom_prec +1)%Z).
                    pose proof bpow_gt_0.
                    specialize (H5 radix2 (ex -1 )%Z).
                    pose proof bpow_gt_0.
                    specialize (H6 radix2 (ex)%Z ).
                    psatz R.
                  }
                }
              }
              {
                pose proof plusRoundingTruth2.
                pose proof round_0 as round_0.
                specialize (round_0 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef)).
                
                pose proof zeroLtFloatMax.
                specialize (H0 (round radix2
                                      (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                      (round_mode mode_NE) 0) round_0).
                apply validFloat2 in floatToRealProof1.
                apply validFloat2 in floatToRealProof2.
                unfold floatMax in *.
                specialize (H x x0 x1 x2 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                rewrite <- floatToRealProof1 in H.
                rewrite <- floatToRealProof2 in H.
                rewrite <- e1 in H.
                specialize (H H0).              
                rewrite <- plusResultStmt in H.
                unfold B2R in H.
                rewrite round_0 in *.
                destruct H.
                rewrite H.
                unfold floatMin in *.
                pose proof bpow_gt_0.
                specialize (H2 radix2 custom_emin).
                unfold error in *.
                pose proof bpow_gt_0.
                specialize (H3 radix2 (-custom_prec +1)%Z).
                psatz R.
              }
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
            assert (floatMinCase1 := H2).
            assert (floatMaxBound1 := H6).
            assert (resultGe0 := H7).
            clear H1 H2 H3 H6 H7 H9 H IHexpr1 IHexpr2.
            unfold Semantics.eval_comp in *.
            simpl in *.
            remember (eval_term (lb x4) st st) as lb1.
            remember (eval_term (lb x5) st st) as lb2.
            remember (eval_term (ub x5) st st) as ub2.
            remember (eval_term (ub x4) st st) as ub1.
            clear Hequb1 Hequb2 Heqlb1 Heqlb2.
            destruct (Rle_dec floatMin (x1+x2)%R).
            {
              psatz R.
            }
            {
              SearchAbout (~(_<=_) -> (_>_))%R.
              apply Rnot_le_gt in n.
              pose proof floatMaxProofRounding as floatMaxProofRounding.
              generalize (el2 radix2 (x1+x2)%R (ln_beta radix2 (x1+x2)%R)).
              intros.
              destruct (Rle_lt_or_eq_dec 0 (x1+x2)%R).
              {
                psatz R.
              }
              {
                assert (resultNe0 := r0).                
                apply RMicromega.Rlt_neq in resultNe0.
                assert (ln_beta_premise :=H).
                clear H.
                specialize (ln_beta_premise resultNe0).
                remember (ln_beta radix2 (x1 + x2)) as ex.
                specialize (floatMaxProofRounding (x1 + x2)%R ex ln_beta_premise).
                pose proof subNormal as subNormalProof.
                apply Rlt_gt in r0.
                apply Rgt_lt in n.
                specialize (subNormalProof (x1+x2)%R r0 n).
                rewrite <- Heqex in subNormalProof.
                specialize (floatMaxProofRounding subNormalProof n r0).
                destruct floatMaxProofRounding.
                pose proof plusRoundingTruth2 as plusRoundingTruth2.
                apply validFloat2 in floatToRealRelationForExpr1.
                apply validFloat2 in floatToRealRelationForExpr2.
                specialize (plusRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2).
                rewrite <- floatToRealRelationForExpr1 in plusRoundingTruth2.
                rewrite <- floatToRealRelationForExpr2 in plusRoundingTruth2.
                specialize (plusRoundingTruth2 H1).
                destruct plusRoundingTruth2.
                rewrite <- plusResultStmt in H2.
                unfold B2R in H2.
                rewrite H2 in *.
                remember ( round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                 (round_mode mode_NE) (x1 + x2)) as roundedValue.
                destruct H.
                {
                  unfold FLT_exp in H.
                 
                  intros.
                  pose proof roundedValLessThanFloatMin.
                  specialize (H6 ex subNormalProof).
                  unfold FLT_exp in H6.
                  pose proof bpow_gt_0.
                  specialize (H7 radix2 (Z.max (ex - custom_prec) (3 - custom_emax - custom_prec))).
                  psatz R.
                }  
                {
                  destruct H.
                  {
                    unfold floatMin.
                    pose proof bpow_gt_0.
                    specialize (H6 radix2 custom_emin).
                    psatz R.
                  }
                  {
                    pose proof bpow_le.
                    specialize (H6 radix2 ex custom_emin subNormalProof).
                    pose proof bpow_gt_0.
                    specialize (H7 radix2 (ex-1)%Z).
                    unfold floatMin.
                    psatz R.
                  }

                }
              }
              {

                 pose proof plusRoundingTruth2.
                 
                pose proof round_0 as round_0.
                specialize (round_0 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef)).
                pose proof zeroLtFloatMax.
                specialize (H2 (round radix2
                                      (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                      (round_mode mode_NE) 0) round_0).
                apply validFloat2 in floatToRealProof1.
                apply validFloat2 in floatToRealProof2.
                unfold floatMax in *.
                specialize (H1 x x0 x1 x2 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                rewrite <- floatToRealProof1 in H1.
                rewrite <- floatToRealProof2 in H1.
                rewrite <- e1 in H1.
                specialize (H1 H2).              
                rewrite <- plusResultStmt in H1.
                unfold B2R in H1.
                rewrite round_0 in *.
                destruct H1.
                rewrite H1.
                unfold floatMin in *.
                pose proof bpow_gt_0.
                specialize (H6 radix2 custom_emin).
                unfold error in *.
                psatz R.
              }
            }
          }
          {
            intuition.
          }
          }
        }
      }
    }
  } 
  {
    
    simpl. unfold getBound.
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
    revert H5.
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
      intros H.
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
        assert (floatMaxBound1 := H7).
        assert (resultGe0 := H2).
        clear H4 H2 H1 H3 H H5  H0 H9 H6 IHexpr1 IHexpr2.
        unfold Semantics.eval_comp in *.
        simpl in floatMinCase.
        simpl in expr1Bound.
        simpl in expr2Bound.
        simpl in floatMaxBound1.
        simpl in resultGe0.
        simpl.
        remember (eval_term (lb x4) st st) as lb1.
        remember (eval_term (lb x5) st st) as lb2.
        remember (eval_term (ub x5) st st) as ub2.
        remember (eval_term (ub x4) st st) as ub1.
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
        specialize (extraFloatMinCase ((lb1 >= ub2)%R //\\ (floatMin <= lb1 - ub2))%R ((ub1 <= lb2)%R //\\ (floatMin <= lb2 - ub1))%R ).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H H1 H0 H2).
        pose proof minusRoundingTruth as minusRoundingTruth.
        Lemma andExtra : forall (p1 p2:Prop), p1  -> p2 ->   p1 //\\ p2.
          intros.
          intuition.
        Qed.
        intros.
        pose proof andExtra as andExtra.
        specialize (andExtra (lb1 >= ub2 //\\ floatMin <= lb1 - ub2)%R ((ub1 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        
        
        pose proof orExtra as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2 
                      (((lb1 >= ub2) //\\ (floatMin <= lb1 - ub2)) //\\ ((ub1 - lb2) * (1 + error) < floatMax)) (((ub1 <= lb2)%R //\\
                                                                                                              (floatMin <= lb2 - ub1)) //\\ ((ub2 - lb1) * (1 + error) < floatMax))).
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
        clear  floatMinCase floatMaxBound1 HeqroundedValue minusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  H7  x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
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
              psatz R.
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
              psatz R.
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
        {
          split.
          {
            z3 solve_dbg.
            psatz R.
           }
          destruct Rcase_abs.
          z3 solve_dbg.
          psatz R.
          z3 solve_dbg.
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
        assert (floatMaxBound1 := H7).
        assert (resultGe0 := H2).
         clear H4 H2 H1 H3 H H5  H0 H9 H6 IHexpr1 IHexpr2.
       unfold Semantics.eval_comp in *.
         simpl in floatMinCase.
        simpl in expr1Bound.
        simpl in expr2Bound.
        simpl in floatMaxBound1.
        simpl in resultGe0.
        simpl.
        remember (eval_term (lb x4) st st) as lb1.
        remember (eval_term (lb x5) st st) as lb2.
        remember (eval_term (ub x5) st st) as ub2.
        remember (eval_term (ub x4) st st) as ub1.
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
        specialize (extraFloatMinCase ((lb1 >= ub2)%R //\\ (floatMin <= lb1 - ub2)%R) ((ub1 <= lb2)%R //\\ (floatMin <= lb2 - ub1))%R ).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H H1 H0 H2).
        pose proof minusRoundingTruth as minusRoundingTruth.
       
        intros.
        pose proof andExtra as andExtra.
        specialize (andExtra (ub1 <= lb2 //\\ floatMin <= lb2 - ub1)%R ((ub2 - lb1) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
      
          
        pose proof orExtra2 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2 
                      (((lb1 >= ub2) //\\ (floatMin <= lb1 - ub2)) //\\ ((ub1 - lb2) * (1 + error) < floatMax)) (((ub1 <= lb2)%R //\\
  (floatMin <= lb2 - ub1)) //\\ ((ub2 - lb1) * (1 + error) < floatMax))).
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
        assert (minusRoundingTruth2
:= H4).
        clear H4.
        clear minusResultStmt.
        clear H3.
        clear minusRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear  floatMinCase floatMaxBound1 HeqroundedValue minusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  H7  x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
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
              psatz R.
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
              psatz R.
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
              psatz R.
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
              psatz R.
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
      assert (minusResultStmt := H9).
      assert (floatToRealRelationForExpr1:= H2).
      assert (floatToRealRelationForExpr2:= H3).
      clear H f Heqo0 H0 H1 H8 f_des Heqo' H9 H10 .
      assert (floatToRealProof1:= H2).
      assert (floatToRealProof2:= H3).
      clear H2 H3.
      unfold denote_singleBoundTerm in *.
      intros H.
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
        assert (floatMaxBound1 := H7).
        assert (resultGe0 := H2).
        clear H4 H2 H1 H3 H H5 H0 H6 H7 IHexpr1 IHexpr2.
        unfold Semantics.eval_comp in *.
        simpl in floatMinCase.
        simpl in expr1Bound.
        simpl in expr2Bound.
        simpl in floatMaxBound1.
        simpl in resultGe0.
        simpl.
        remember (eval_term (lb x4) st st) as lb1.
        remember (eval_term (lb x5) st st) as lb2.
        remember (eval_term (ub x5) st st) as ub2.
        remember (eval_term (ub x4) st st) as ub1.
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
        specialize (extraFloatMinCase ((lb1 >= ub2)%R //\\ (floatMin <= lb1 - ub2))%R ((ub1 <= lb2)%R //\\ (floatMin <= lb2 - ub1))%R ).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H H1 H0 H2).
        pose proof minusRoundingTruth as minusRoundingTruth.


        intros.
        pose proof andExtra as andExtra.
        specialize (andExtra (lb1 >= ub2 //\\ floatMin <= lb1 - ub2)%R ((ub1 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        pose proof orExtra as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2
                      (((lb1 >= ub2) //\\ (floatMin <= lb1 - ub2)) //\\ ((ub1 - lb2) * (1 + error) < floatMax)) (((ub1 <= lb2)%R //\\
                                                                                                              (floatMin <= lb2 - ub1)) //\\ ((ub2 - lb1) * (1 + error) < floatMax))).
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
        Print Bminus_correct.
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
        clear floatMinCase floatMaxBound1 HeqroundedValue minusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2 H9 x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
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
              psatz R.
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
              psatz R.
              
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
          assert (floatMaxBound1 := H7).
          assert (resultGe0 := H2).
          clear H4 H2 H1 H3 H H5 H0 H6 H9 IHexpr1 IHexpr2.
          unfold Semantics.eval_comp in *.
          simpl in floatMinCase.
          simpl in expr1Bound.
          simpl in expr2Bound.
          simpl in floatMaxBound1.
          simpl in resultGe0.
          simpl.
          remember (eval_term (lb x4) st st) as lb1.
          remember (eval_term (lb x5) st st) as lb2.
          remember (eval_term (ub x5) st st) as ub2.
          remember (eval_term (ub x4) st st) as ub1.
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
          specialize (extraFloatMinCase ((lb1 >= ub2)%R //\\ (floatMin <= lb1 - ub2)%R) ((ub1 <= lb2)%R //\\ (floatMin <= lb2 - ub1))%R ).
          specialize (extraFloatMinCase floatMinCase).
          specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H H1 H0 H2).
          pose proof minusRoundingTruth as minusRoundingTruth.
          intros.
          pose proof andExtra as andExtra.
          specialize (andExtra (ub1 <= lb2 //\\ floatMin <= lb2 - ub1)%R ((ub2 - lb1) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
          pose proof orExtra2 as extraFloatMinCase2.
          simpl in andExtra.
          simpl in extraFloatMinCase2.
          Local Open Scope R_scope.
          specialize (extraFloatMinCase2
                        (((lb1 >= ub2) //\\ (floatMin <= lb1 - ub2)) //\\ ((ub1 - lb2) * (1 + error) < floatMax)) (((ub1 <= lb2)%R //\\
                                                                                                                (floatMin <= lb2 - ub1)) //\\ ((ub2 - lb1) * (1 + error) < floatMax))).
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
          clear floatMinCase floatMaxBound1 HeqroundedValue minusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2 H7 x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
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
                psatz R.
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
                psatz R.
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
                psatz R.
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
                psatz R.
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
          {
             {
               intuition.
             }
          }
        }
      }  
    }
  }
  {
    simpl. unfold getBound.
    intros.
    assert (Heqo':=Heqo).
    apply resultImplicationsMult in Heqo.
    Require Import ExtLib.Tactics.
    forward_reason. destruct H2; destruct H3.
    specialize (IHexpr1 _ _ H2 H0).
    specialize (IHexpr2 _ _ H3 H1).
    2: eexists; eauto.
    eapply Forall_forall. intros.
    revert H5.
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
      assert (multResultStmt := H9).
      assert (floatToRealRelationForExpr1:= H2).
      assert (floatToRealRelationForExpr2:= H3).
      clear H f Heqo0 H0 H1 H8 f_des Heqo' H9 H10 .
      assert (floatToRealProof1:= H2).
      assert (floatToRealProof2:= H3).
      clear H2 H3.
      unfold denote_singleBoundTerm in *.
      intros H.
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
        assert (resultGe1 := H7).
        assert (resultGe2 := H8).
        clear H4 H2 H1 H3 H H5 H0 H10 H6 IHexpr1 IHexpr2.
        unfold Semantics.eval_comp in *.
        simpl in floatMinCase.
        simpl in expr1Bound.
        simpl in expr2Bound.
        simpl in floatMaxBound1.
        simpl in resultGe1.
        simpl in resultGe2.
        simpl.
        remember (eval_term (lb x4) st st) as lb1.
        remember (eval_term (lb x5) st st) as lb2.
        remember (eval_term (ub x5) st st) as ub2.
        remember (eval_term (ub x4) st st) as ub1.
        clear Hequb1 Hequb2 Heqlb1 Heqlb2.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        specialize (relErrorBasedOnFloatMinTruthMult x1 x2 lb1 lb2 ub1 ub2).
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        intros.
        intros.
        pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= lb1 * lb2)%R (lb1 >= 0)%R (lb2 >= 0)%R).
        
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        Lemma orExtra3 : forall p1 p2 p3 p4: Prop, p1 -> p1 \\// p2 \\// p3 \\// p4.
          intros; intuition. Qed.
        pose proof orExtra3 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R //\\ (lb1 >= 0)%R //\\ (lb2 >= 0)%R)  ((floatMin <= (0 - ub1) * (0 - ub2))%R //\\ (ub1 < 0)%R //\\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R //\\(lb1 >= 0)%R //\\ (ub2 < 0)%R )  ((floatMin <= (0 - ub1) * lb2)%R //\\ (ub1 < 0)%R //\\ (lb2 >= 0)%R) ).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H H1 H0 H2).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
       
         intros.
        specialize (andExtra ((floatMin <= lb1 * lb2)%R //\\ (lb1 >= 0)%R //\\ (lb2 >= 0))%R (ub1 * ub2 * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        pose proof orExtra3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 //\\
                        lb1 >= 0 //\\
                        lb2 >= 0) //\\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) //\\
                      ub1 < 0 //\\
                      ub2 < 0) //\\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) //\\
                      lb1 >= 0 //\\
                      ub2 < 0) //\\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 //\\
                      ub1 < 0 //\\
                      lb2 >= 0) //\\ (0 - lb1) * ub2 * (1 + error) < floatMax)).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).
        specialize (multRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H H1 H0 H2).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        revert multResultStmt. intros multResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x *
                          B2R custom_prec custom_emax x0)) as roundedValue.
        simpl in multRoundingTruth2.
        simpl in multResultStmt.
        rewrite <- multResultStmt in multRoundingTruth2.
        simpl in multRoundingTruth2.
        decompose [and] multRoundingTruth2.
        rewrite H4.
        clear H5.
        clear multRoundingTruth2.
        assert (multRoundingTruth2:= H4).
        clear H4.
        clear multResultStmt.
        clear H3.
        clear multRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear H7 H8 floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
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
                
                clear -r r0 resultGe1 resultGe2 H H1. 
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
              {
                clear -r r0 resultGe1 resultGe2 H H1. 
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
              split.
              {
                clear -H3 r relErrorBasedOnFloatMinTruthMult H4 resultGe1 resultGe2 H H1 .
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
              {
                clear -H3 r resultGe1 resultGe2 H H0 H1 H2.
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
          {
            split.
            {
              clear -H3 relErrorBasedOnFloatMinTruthMult resultGe1 resultGe2 r H H1 .
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
            {
              clear -r0 resultGe1 resultGe2 H H1. 
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
            {
              clear -H3 resultGe1 resultGe2 relErrorBasedOnFloatMinTruthMult r H H0 H1 H2.
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
           assert (resultGe1 := H7).
           assert (resultGe2 := H8).
           clear H4 H2 H1 H3 H H5 H10 H0 H6 IHexpr1 IHexpr2.
           unfold Semantics.eval_comp in *.
           simpl in floatMinCase.
           simpl in expr1Bound.
           simpl in expr2Bound.
           simpl in floatMaxBound1.
           simpl in resultGe1.
           simpl in resultGe2.
           simpl.
           remember (eval_term (lb x4) st st) as lb1.
           remember (eval_term (lb x5) st st) as lb2.
           remember (eval_term (ub x5) st st) as ub2.
           remember (eval_term (ub x4) st st) as ub1.
           clear Hequb1 Hequb2 Heqlb1 Heqlb2.
           pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
           specialize (relErrorBasedOnFloatMinTruthMult x1 x2 lb1 lb2 ub1 ub2).
           destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        intros.
        intros.
        pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= (0 - ub1) * (0 - ub2))%R (ub1 < 0)%R (ub2 < 0)%R).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        pose proof orExtra3 as extraFloatMinCase.
        specialize (extraFloatMinCase  ((floatMin <= (0 - ub1) * (0 - ub2))%R //\\ (ub1 < 0)%R //\\ (ub2 < 0)%R) ((floatMin <= lb1 * lb2)%R //\\ (lb1 >= 0)%R //\\ (lb2 >= 0)%R)  ((floatMin <= lb1 * (0 - ub2))%R //\\(lb1 >= 0)%R //\\ (ub2 < 0)%R )  ((floatMin <= (0 - ub1) * lb2)%R //\\ (ub1 < 0)%R //\\ (lb2 >= 0)%R) ).
        specialize (extraFloatMinCase floatMinCase).
        Lemma diffOR : forall (p1 p2 p3 p4 : Prop), p1 \\// p2 \\// p3 \\// p4 -> p2 \\// p1 \\// p3 \\// p4.
          intuition.
        Qed.
        pose proof diffOR as diffOR.
        specialize ( diffOR ((floatMin <= (0 - ub1) * (0 - ub2))%R //\\ (ub1 < 0)%R //\\ (ub2 < 0)%R) ((floatMin <= lb1 * lb2)%R //\\ (lb1 >= 0)%R //\\ (lb2 >= 0)%R) ((floatMin <= lb1 * (0 - ub2))%R //\\ (lb1 >= 0)%R //\\ (ub2 < 0)%R) ((floatMin <= (0 - ub1) * lb2)%R //\\ (ub1 < 0)%R //\\ (lb2 >= 0)%R)).
        apply diffOR in extraFloatMinCase.
        clear diffOR.
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H H1 H0 H2).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= (0 - ub1) * (0 - ub2))%R //\\ (ub1 < 0)%R //\\ (ub2 < 0)%R) ((0 - lb1) * (0 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        pose proof orExtra3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2
                       ((floatMin <= (0 - ub1) * (0 - ub2) //\\
                      ub1 < 0 //\\
                      ub2 < 0) //\\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)                     
                      ((floatMin <= lb1 * lb2 //\\
                        lb1 >= 0 //\\
                        lb2 >= 0) //\\ ub1 * ub2 * (1 + error) < floatMax)
                      
                      ((floatMin <= lb1 * (0 - ub2) //\\
                      lb1 >= 0 //\\
                      ub2 < 0) //\\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 //\\
                      ub1 < 0 //\\
                      lb2 >= 0) //\\ (0 - lb1) * ub2 * (1 + error) < floatMax)).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).

        pose proof diffOR as diffOR.
        specialize ( diffOR 
                       ((floatMin <= (0 - ub1) * (0 - ub2) //\\ ub1 < 0 //\\ ub2 < 0) //\\ (0 - lb1) * (0 - lb2) * (1 + error) < floatMax) 
                       ((floatMin <= lb1 * lb2 //\\ lb1 >= 0 //\\ lb2 >= 0) //\\ ub1 * ub2 * (1 + error) < floatMax) 
                       ((floatMin <= lb1 * (0 - ub2) //\\ lb1 >= 0 //\\ ub2 < 0) //\\ ub1 * (0 - lb2) * (1 + error) < floatMax) 
                       ((floatMin <= (0 - ub1) * lb2 //\\ ub1 < 0 //\\ lb2 >= 0) //\\ (0 - lb1) * ub2 * (1 + error) < floatMax) )%R.

        

        apply diffOR in extraFloatMinCase2.
        clear diffOR.


        specialize (multRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H H1 H0 H2).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        revert multResultStmt. intros multResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x *
                          B2R custom_prec custom_emax x0)) as roundedValue.
        simpl in multRoundingTruth2.
        simpl in multResultStmt.
        rewrite <- multResultStmt in multRoundingTruth2.
        simpl in multRoundingTruth2.
        decompose [and] multRoundingTruth2.
        rewrite H4.
        clear H5.
        clear multRoundingTruth2.
        assert (multRoundingTruth2:= H4).
        clear H4.
        clear multResultStmt.
        clear H3.
        clear multRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear H7 H8 floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
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
                clear -resultGe1 resultGe2 r r0 H0 H2. 
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
            {
              split.
              {
                clear -H3 resultGe1 resultGe2 r relErrorBasedOnFloatMinTruthMult H4 H0 H2. 
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
           assert (resultGe1 := H7).
           assert (resultGe2 := H8).
           clear H4 H2 H1 H3 H H5 H10 H0 H6 IHexpr1 IHexpr2.
           unfold Semantics.eval_comp in *.
           simpl in floatMinCase.
           simpl in expr1Bound.
           simpl in expr2Bound.
           simpl in floatMaxBound1.
           simpl in resultGe1.
           simpl in resultGe2.
           simpl.
           remember (eval_term (lb x4) st st) as lb1.
           remember (eval_term (lb x5) st st) as lb2.
           remember (eval_term (ub x5) st st) as ub2.
           remember (eval_term (ub x4) st st) as ub1.
           clear Hequb1 Hequb2 Heqlb1 Heqlb2.
           pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
           specialize (relErrorBasedOnFloatMinTruthMult x1 x2 lb1 lb2 ub1 ub2).
           destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        intros.
        intros.
        pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= lb1 * (0 - ub2))%R (lb1 >= 0)%R  (ub2 < 0)%R ).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        Lemma orExtra3_3 : forall p1 p2 p3 p4: Prop, p3 -> p1 \\// p2 \\// p3 \\// p4.
          intros; intuition. Qed.
        pose proof orExtra3_3 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R //\\ (lb1 >= 0)%R //\\ (lb2 >= 0)%R) ((floatMin <= (0 - ub1) * (0 - ub2))%R //\\ (ub1 < 0)%R //\\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R //\\ (lb1 >= 0)%R //\\ (ub2 < 0)%R)  ((floatMin <= (0 - ub1) * lb2)%R //\\ (ub1 < 0)%R //\\ (lb2 >= 0)%R)).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H H1 H0 H2).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= lb1 * (0 - ub2))%R //\\ (lb1 >= 0)%R //\\ (ub2 < 0)%R) (ub1 * (0 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1).
       
        Local Open Scope R_scope.
       
        pose proof orExtra3_3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 //\\
                        lb1 >= 0 //\\
                        lb2 >= 0) //\\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) //\\
                      ub1 < 0 //\\
                      ub2 < 0) //\\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) //\\
                      lb1 >= 0 //\\
                      ub2 < 0) //\\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 //\\
                      ub1 < 0 //\\
                      lb2 >= 0) //\\ (0 - lb1) * ub2 * (1 + error) < floatMax)).

        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).


        specialize (multRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H H1 H0 H2).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        revert multResultStmt. intros multResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x *
                          B2R custom_prec custom_emax x0)) as roundedValue.
        simpl in multRoundingTruth2.
        simpl in multResultStmt.
        rewrite <- multResultStmt in multRoundingTruth2.
        simpl in multRoundingTruth2.
        decompose [and] multRoundingTruth2.
        rewrite H4.
        clear H5.
        clear multRoundingTruth2.
        assert (multRoundingTruth2:= H4).
        clear H4.
        clear multResultStmt.
        clear H3.
        clear multRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear H7 H8 floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
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
                psatz R.
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
                psatz R.
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
           assert (resultGe1 := H7).
           assert (resultGe2 := H8).
           clear H4 H2 H1 H3 H H5 H10 H0 H6 IHexpr1 IHexpr2.
           unfold Semantics.eval_comp in *.
           simpl in floatMinCase.
           simpl in expr1Bound.
           simpl in expr2Bound.
           simpl in floatMaxBound1.
           simpl in resultGe1.
           simpl in resultGe2.
           simpl.
           remember (eval_term (lb x4) st st) as lb1.
           remember (eval_term (lb x5) st st) as lb2.
           remember (eval_term (ub x5) st st) as ub2.
           remember (eval_term (ub x4) st st) as ub1.
           clear Hequb1 Hequb2 Heqlb1 Heqlb2.
           pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
           specialize (relErrorBasedOnFloatMinTruthMult x1 x2 lb1 lb2 ub1 ub2).
           destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        intros.
        intros.
        pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= (0 - ub1) * lb2)%R (ub1 < 0)%R (lb2 >= 0)%R ).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        Lemma orExtra3_4 : forall p1 p2 p3 p4: Prop, p4 -> p1 \\// p2 \\// p3 \\// p4.
          intros; intuition. Qed.
        pose proof orExtra3_4 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R //\\ (lb1 >= 0)%R //\\ (lb2 >= 0)%R) ((floatMin <= (0 - ub1) * (0 - ub2))%R //\\ (ub1 < 0)%R //\\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R //\\ (lb1 >= 0)%R //\\ (ub2 < 0)%R)  ((floatMin <= (0 - ub1) * lb2)%R //\\ (ub1 < 0)%R //\\ (lb2 >= 0)%R)).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H H1 H0 H2).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= (0 - ub1) * lb2)%R //\\ (ub1 < 0)%R //\\ (lb2 >= 0)%R) ((0 - lb1) * ub2 * (1 + error) < floatMax)%R floatMinCase floatMaxBound1).
       
        Local Open Scope R_scope.

        pose proof orExtra3_4 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 //\\
                        lb1 >= 0 //\\
                        lb2 >= 0) //\\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) //\\
                      ub1 < 0 //\\
                      ub2 < 0) //\\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) //\\
                      lb1 >= 0 //\\
                      ub2 < 0) //\\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 //\\
                      ub1 < 0 //\\
                      lb2 >= 0) //\\ (0 - lb1) * ub2 * (1 + error) < floatMax)).

        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).


        specialize (multRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H H1 H0 H2).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        revert multResultStmt. intros multResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x *
                          B2R custom_prec custom_emax x0)) as roundedValue.
        simpl in multRoundingTruth2.
        simpl in multResultStmt.
        rewrite <- multResultStmt in multRoundingTruth2.
        simpl in multRoundingTruth2.
        decompose [and] multRoundingTruth2.
        rewrite H4.
        clear H5.
        clear multRoundingTruth2.
        assert (multRoundingTruth2:= H4).
        clear H4.
        clear multResultStmt.
        clear H3.
        clear multRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear H7 H8 floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
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
                psatz R.
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
                psatz R.
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
          {
            inversion H0.
          }
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
      assert (multResultStmt := H9).
      assert (floatToRealRelationForExpr1:= H2).
      assert (floatToRealRelationForExpr2:= H3).
      clear H f Heqo0 H0 H1 H8 f_des Heqo' H9 H10 .
      assert (floatToRealProof1:= H2).
      assert (floatToRealProof2:= H3).
      clear H2 H3.
      unfold denote_singleBoundTerm in *.
      intros H.
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
        assert (resultGe1 := H7).
        assert (resultGe2 := H8).
        clear H4 H2 H1 H3 H H5 H0 H10 H6 IHexpr1 IHexpr2.
        unfold Semantics.eval_comp in *.
        simpl in floatMinCase.
        simpl in expr1Bound.
        simpl in expr2Bound.
        simpl in floatMaxBound1.
        simpl in resultGe1.
        simpl in resultGe2.
        simpl.
        remember (eval_term (lb x4) st st) as lb1.
        remember (eval_term (lb x5) st st) as lb2.
        remember (eval_term (ub x5) st st) as ub2.
        remember (eval_term (ub x4) st st) as ub1.
        clear Hequb1 Hequb2 Heqlb1 Heqlb2.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        specialize (relErrorBasedOnFloatMinTruthMult x1 x2 lb1 lb2 ub1 ub2).
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        intros.
        intros.
        pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= lb1 * lb2)%R (lb1 >= 0)%R (lb2 >= 0)%R).
        
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        pose proof orExtra3 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R //\\ (lb1 >= 0)%R //\\ (lb2 >= 0)%R)  ((floatMin <= (0 - ub1) * (0 - ub2))%R //\\ (ub1 < 0)%R //\\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R //\\(lb1 >= 0)%R //\\ (ub2 < 0)%R )  ((floatMin <= (0 - ub1) * lb2)%R //\\ (ub1 < 0)%R //\\ (lb2 >= 0)%R) ).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H H1 H0 H2).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
        
        intros.
        specialize (andExtra ((floatMin <= lb1 * lb2)%R //\\ (lb1 >= 0)%R //\\ (lb2 >= 0))%R (ub1 * ub2 * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        pose proof orExtra3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 //\\
                        lb1 >= 0 //\\
                        lb2 >= 0) //\\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) //\\
                        ub1 < 0 //\\
                        ub2 < 0) //\\
                       (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) //\\
                        lb1 >= 0 //\\
                        ub2 < 0) //\\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 //\\
                         ub1 < 0 //\\
                         lb2 >= 0) //\\ (0 - lb1) * ub2 * (1 + error) < floatMax)).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).
        specialize (multRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H H1 H0 H2).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        revert multResultStmt. intros multResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x *
                          B2R custom_prec custom_emax x0)) as roundedValue.
        simpl in multRoundingTruth2.
        simpl in multResultStmt.
        rewrite <- multResultStmt in multRoundingTruth2.
        simpl in multRoundingTruth2.
        decompose [and] multRoundingTruth2.
        rewrite H4.
        clear H5.
        clear multRoundingTruth2.
        assert (multRoundingTruth2:= H4).
        clear H4.
        clear multResultStmt.
        clear H3.
        clear multRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear H7 H8 floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
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
              
              clear -r r0 resultGe1 resultGe2 H H1. 
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
            {
              clear -r r0 resultGe1 resultGe2 H H1. 
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
            split.
            {
              clear -H3 r relErrorBasedOnFloatMinTruthMult H4 resultGe1 resultGe2 H H1 .
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
            {
              clear -H3 r resultGe1 resultGe2 H H0 H1 H2.
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
        {
          split.
          {
            clear -H3 relErrorBasedOnFloatMinTruthMult resultGe1 resultGe2 r H H1 .
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
          {
            clear -r0 resultGe1 resultGe2 H H1. 
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
          {
            clear -H3 resultGe1 resultGe2 relErrorBasedOnFloatMinTruthMult r H H0 H1 H2.
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
          assert (resultGe1 := H7).
          assert (resultGe2 := H8).
          clear H4 H2 H1 H3 H H5 H10 H0 H6 IHexpr1 IHexpr2.
          unfold Semantics.eval_comp in *.
          simpl in floatMinCase.
          simpl in expr1Bound.
          simpl in expr2Bound.
          simpl in floatMaxBound1.
          simpl in resultGe1.
          simpl in resultGe2.
          simpl.
          remember (eval_term (lb x4) st st) as lb1.
          remember (eval_term (lb x5) st st) as lb2.
          remember (eval_term (ub x5) st st) as ub2.
          remember (eval_term (ub x4) st st) as ub1.
          clear Hequb1 Hequb2 Heqlb1 Heqlb2.
          pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
          specialize (relErrorBasedOnFloatMinTruthMult x1 x2 lb1 lb2 ub1 ub2).
          destruct expr1Bound.
          destruct expr2Bound.
          pose proof or_introl.
          intros.
          intros.
          pose proof conjoin2 as conjoin2.
          specialize (conjoin2 (floatMin <= (0 - ub1) * (0 - ub2))%R (ub1 < 0)%R (ub2 < 0)%R).
          specialize (conjoin2 floatMinCase resultGe1 resultGe2).
          clear floatMinCase.
          assert (floatMinCase:=conjoin2).
          clear conjoin2.
          intros.
          pose proof orExtra3 as extraFloatMinCase.
          specialize (extraFloatMinCase  ((floatMin <= (0 - ub1) * (0 - ub2))%R //\\ (ub1 < 0)%R //\\ (ub2 < 0)%R) ((floatMin <= lb1 * lb2)%R //\\ (lb1 >= 0)%R //\\ (lb2 >= 0)%R)  ((floatMin <= lb1 * (0 - ub2))%R //\\(lb1 >= 0)%R //\\ (ub2 < 0)%R )  ((floatMin <= (0 - ub1) * lb2)%R //\\ (ub1 < 0)%R //\\ (lb2 >= 0)%R) ).
          specialize (extraFloatMinCase floatMinCase).
          pose proof diffOR as diffOR.
          specialize ( diffOR ((floatMin <= (0 - ub1) * (0 - ub2))%R //\\ (ub1 < 0)%R //\\ (ub2 < 0)%R) ((floatMin <= lb1 * lb2)%R //\\ (lb1 >= 0)%R //\\ (lb2 >= 0)%R) ((floatMin <= lb1 * (0 - ub2))%R //\\ (lb1 >= 0)%R //\\ (ub2 < 0)%R) ((floatMin <= (0 - ub1) * lb2)%R //\\ (ub1 < 0)%R //\\ (lb2 >= 0)%R)).
          apply diffOR in extraFloatMinCase.
          clear diffOR.
          specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H H1 H0 H2).
          pose proof multRoundingTruth as multRoundingTruth.
          intros.
          pose proof andExtra as andExtra.
          intros.
          specialize (andExtra ((floatMin <= (0 - ub1) * (0 - ub2))%R //\\ (ub1 < 0)%R //\\ (ub2 < 0)%R) ((0 - lb1) * (0 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
          pose proof orExtra3 as extraFloatMinCase2.
          simpl in andExtra.
          simpl in extraFloatMinCase2.
          Local Open Scope R_scope.
          specialize (extraFloatMinCase2
                        ((floatMin <= (0 - ub1) * (0 - ub2) //\\
                          ub1 < 0 //\\
                          ub2 < 0) //\\
                         (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)                     
                        ((floatMin <= lb1 * lb2 //\\
                          lb1 >= 0 //\\
                          lb2 >= 0) //\\ ub1 * ub2 * (1 + error) < floatMax)
                        
                        ((floatMin <= lb1 * (0 - ub2) //\\
                          lb1 >= 0 //\\
                          ub2 < 0) //\\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                        (( floatMin <= (0 - ub1) * lb2 //\\
                           ub1 < 0 //\\
                           lb2 >= 0) //\\ (0 - lb1) * ub2 * (1 + error) < floatMax)).
          simpl in extraFloatMinCase2.
          specialize (extraFloatMinCase2 andExtra).

          pose proof diffOR as diffOR.
          specialize ( diffOR 
                         ((floatMin <= (0 - ub1) * (0 - ub2) //\\ ub1 < 0 //\\ ub2 < 0) //\\ (0 - lb1) * (0 - lb2) * (1 + error) < floatMax) 
                         ((floatMin <= lb1 * lb2 //\\ lb1 >= 0 //\\ lb2 >= 0) //\\ ub1 * ub2 * (1 + error) < floatMax) 
                         ((floatMin <= lb1 * (0 - ub2) //\\ lb1 >= 0 //\\ ub2 < 0) //\\ ub1 * (0 - lb2) * (1 + error) < floatMax) 
                         ((floatMin <= (0 - ub1) * lb2 //\\ ub1 < 0 //\\ lb2 >= 0) //\\ (0 - lb1) * ub2 * (1 + error) < floatMax) )%R.

          

          apply diffOR in extraFloatMinCase2.
          clear diffOR.


          specialize (multRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H H1 H0 H2).
          pose proof multRoundingTruth2 as multRoundingTruth2.
          specialize (multRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 multRoundingTruth).
          revert multResultStmt. intros multResultStmt.
          apply validFloat2 in floatToRealProof1.
          apply validFloat2 in floatToRealProof2.
          rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
          rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
          remember ( round radix2
                           (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                           (round_mode mode_NE)
                           (B2R custom_prec custom_emax x *
                            B2R custom_prec custom_emax x0)) as roundedValue.
          simpl in multRoundingTruth2.
          simpl in multResultStmt.
          rewrite <- multResultStmt in multRoundingTruth2.
          simpl in multRoundingTruth2.
          decompose [and] multRoundingTruth2.
          rewrite H4.
          clear H5.
          clear multRoundingTruth2.
          assert (multRoundingTruth2:= H4).
          clear H4.
          clear multResultStmt.
          clear H3.
          clear multRoundingTruth.
          rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
          rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
          rewrite <- floatToRealProof2 in HeqroundedValue.
          rewrite <- floatToRealProof1 in HeqroundedValue.
          pose proof errorGt0.
          clear H7 H8 floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
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
                clear -resultGe1 resultGe2 r r0 H0 H2. 
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
            {
              split.
              {
                clear -H3 resultGe1 resultGe2 r relErrorBasedOnFloatMinTruthMult H4 H0 H2. 
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
            assert (resultGe1 := H7).
            assert (resultGe2 := H8).
            clear H4 H2 H1 H3 H H5 H10 H0 H6 IHexpr1 IHexpr2.
            unfold Semantics.eval_comp in *.
            simpl in floatMinCase.
            simpl in expr1Bound.
            simpl in expr2Bound.
            simpl in floatMaxBound1.
            simpl in resultGe1.
            simpl in resultGe2.
            simpl.
            remember (eval_term (lb x4) st st) as lb1.
            remember (eval_term (lb x5) st st) as lb2.
            remember (eval_term (ub x5) st st) as ub2.
            remember (eval_term (ub x4) st st) as ub1.
            clear Hequb1 Hequb2 Heqlb1 Heqlb2.
            pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
            specialize (relErrorBasedOnFloatMinTruthMult x1 x2 lb1 lb2 ub1 ub2).
            destruct expr1Bound.
            destruct expr2Bound.
            pose proof or_introl.
            intros.
            intros.
            pose proof conjoin2 as conjoin2.
            specialize (conjoin2 (floatMin <= lb1 * (0 - ub2))%R (lb1 >= 0)%R  (ub2 < 0)%R ).
            specialize (conjoin2 floatMinCase resultGe1 resultGe2).
            clear floatMinCase.
            assert (floatMinCase:=conjoin2).
            clear conjoin2.
            intros.
            pose proof orExtra3_3 as extraFloatMinCase.
            specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R //\\ (lb1 >= 0)%R //\\ (lb2 >= 0)%R) ((floatMin <= (0 - ub1) * (0 - ub2))%R //\\ (ub1 < 0)%R //\\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R //\\ (lb1 >= 0)%R //\\ (ub2 < 0)%R)  ((floatMin <= (0 - ub1) * lb2)%R //\\ (ub1 < 0)%R //\\ (lb2 >= 0)%R)).
            specialize (extraFloatMinCase floatMinCase).
            specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H H1 H0 H2).
            pose proof multRoundingTruth as multRoundingTruth.
            intros.
            pose proof andExtra as andExtra.
            intros.
            specialize (andExtra ((floatMin <= lb1 * (0 - ub2))%R //\\ (lb1 >= 0)%R //\\ (ub2 < 0)%R) (ub1 * (0 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1).
            
            Local Open Scope R_scope.
            
            pose proof orExtra3_3 as extraFloatMinCase2.
            simpl in andExtra.
            simpl in extraFloatMinCase2.
            specialize (extraFloatMinCase2
                          ((floatMin <= lb1 * lb2 //\\
                            lb1 >= 0 //\\
                            lb2 >= 0) //\\ ub1 * ub2 * (1 + error) < floatMax)
                          ((floatMin <= (0 - ub1) * (0 - ub2) //\\
                            ub1 < 0 //\\
                            ub2 < 0) //\\
                           (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                          ((floatMin <= lb1 * (0 - ub2) //\\
                            lb1 >= 0 //\\
                            ub2 < 0) //\\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                          (( floatMin <= (0 - ub1) * lb2 //\\
                             ub1 < 0 //\\
                             lb2 >= 0) //\\ (0 - lb1) * ub2 * (1 + error) < floatMax)).

            simpl in extraFloatMinCase2.
            specialize (extraFloatMinCase2 andExtra).


            specialize (multRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H H1 H0 H2).
            pose proof multRoundingTruth2 as multRoundingTruth2.
            specialize (multRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 multRoundingTruth).
            revert multResultStmt. intros multResultStmt.
            apply validFloat2 in floatToRealProof1.
            apply validFloat2 in floatToRealProof2.
            rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
            rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
            remember ( round radix2
                             (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                             (round_mode mode_NE)
                             (B2R custom_prec custom_emax x *
                              B2R custom_prec custom_emax x0)) as roundedValue.
            simpl in multRoundingTruth2.
            simpl in multResultStmt.
            rewrite <- multResultStmt in multRoundingTruth2.
            simpl in multRoundingTruth2.
            decompose [and] multRoundingTruth2.
            rewrite H4.
            clear H5.
            clear multRoundingTruth2.
            assert (multRoundingTruth2:= H4).
            clear H4.
            clear multResultStmt.
            clear H3.
            clear multRoundingTruth.
            rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
            rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
            rewrite <- floatToRealProof2 in HeqroundedValue.
            rewrite <- floatToRealProof1 in HeqroundedValue.
            pose proof errorGt0.
            clear H7 H8 floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
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
                  psatz R.
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
                  psatz R.
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
              assert (resultGe1 := H7).
              assert (resultGe2 := H8).
              clear H4 H2 H1 H3 H H5 H10 H0 H6 IHexpr1 IHexpr2.
              unfold Semantics.eval_comp in *.
              simpl in floatMinCase.
              simpl in expr1Bound.
              simpl in expr2Bound.
              simpl in floatMaxBound1.
              simpl in resultGe1.
              simpl in resultGe2.
              simpl.
              remember (eval_term (lb x4) st st) as lb1.
              remember (eval_term (lb x5) st st) as lb2.
              remember (eval_term (ub x5) st st) as ub2.
              remember (eval_term (ub x4) st st) as ub1.
              clear Hequb1 Hequb2 Heqlb1 Heqlb2.
              pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
              specialize (relErrorBasedOnFloatMinTruthMult x1 x2 lb1 lb2 ub1 ub2).
              destruct expr1Bound.
              destruct expr2Bound.
              pose proof or_introl.
              intros.
              intros.
              pose proof conjoin2 as conjoin2.
              specialize (conjoin2 (floatMin <= (0 - ub1) * lb2)%R (ub1 < 0)%R (lb2 >= 0)%R ).
              specialize (conjoin2 floatMinCase resultGe1 resultGe2).
              clear floatMinCase.
              assert (floatMinCase:=conjoin2).
              clear conjoin2.
              intros.
              pose proof orExtra3_4 as extraFloatMinCase.
              specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R //\\ (lb1 >= 0)%R //\\ (lb2 >= 0)%R) ((floatMin <= (0 - ub1) * (0 - ub2))%R //\\ (ub1 < 0)%R //\\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R //\\ (lb1 >= 0)%R //\\ (ub2 < 0)%R)  ((floatMin <= (0 - ub1) * lb2)%R //\\ (ub1 < 0)%R //\\ (lb2 >= 0)%R)).
              specialize (extraFloatMinCase floatMinCase).
              specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H H1 H0 H2).
              pose proof multRoundingTruth as multRoundingTruth.
              intros.
              pose proof andExtra as andExtra.
              intros.
              specialize (andExtra ((floatMin <= (0 - ub1) * lb2)%R //\\ (ub1 < 0)%R //\\ (lb2 >= 0)%R) ((0 - lb1) * ub2 * (1 + error) < floatMax)%R floatMinCase floatMaxBound1).
              
              Local Open Scope R_scope.

              pose proof orExtra3_4 as extraFloatMinCase2.
              simpl in andExtra.
              simpl in extraFloatMinCase2.
              specialize (extraFloatMinCase2
                            ((floatMin <= lb1 * lb2 //\\
                              lb1 >= 0 //\\
                              lb2 >= 0) //\\ ub1 * ub2 * (1 + error) < floatMax)
                            ((floatMin <= (0 - ub1) * (0 - ub2) //\\
                              ub1 < 0 //\\
                              ub2 < 0) //\\
                             (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                            ((floatMin <= lb1 * (0 - ub2) //\\
                              lb1 >= 0 //\\
                              ub2 < 0) //\\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                            (( floatMin <= (0 - ub1) * lb2 //\\
                               ub1 < 0 //\\
                               lb2 >= 0) //\\ (0 - lb1) * ub2 * (1 + error) < floatMax)).

              simpl in extraFloatMinCase2.
              specialize (extraFloatMinCase2 andExtra).


              specialize (multRoundingTruth x x0 lb1 lb2 ub1 ub2 x1 x2 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H H1 H0 H2).
              pose proof multRoundingTruth2 as multRoundingTruth2.
              specialize (multRoundingTruth2 x x0 x1 x2 floatToRealProof1 floatToRealProof2 multRoundingTruth).
              revert multResultStmt. intros multResultStmt.
              apply validFloat2 in floatToRealProof1.
              apply validFloat2 in floatToRealProof2.
              rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
              rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
              remember ( round radix2
                               (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                               (round_mode mode_NE)
                               (B2R custom_prec custom_emax x *
                                B2R custom_prec custom_emax x0)) as roundedValue.
              simpl in multRoundingTruth2.
              simpl in multResultStmt.
              rewrite <- multResultStmt in multRoundingTruth2.
              simpl in multRoundingTruth2.
              decompose [and] multRoundingTruth2.
              rewrite H4.
              clear H5.
              clear multRoundingTruth2.
              assert (multRoundingTruth2:= H4).
              clear H4.
              clear multResultStmt.
              clear H3.
              clear multRoundingTruth.
              rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
              rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
              rewrite <- floatToRealProof2 in HeqroundedValue.
              rewrite <- floatToRealProof1 in HeqroundedValue.
              pose proof errorGt0.
              clear H7 H8 floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x3 x4 x4 x5 x x0 expr1 expr2 tr fState b r.
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
                    psatz R.
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
                    psatz R.
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
            {
              inversion H0.
            }
          }
        }
      }
    }
  }
  {

 Lemma floatConstValidityProof : forall f, isFloatConstValid f -> None = floatToReal f -> False. 
        intros. 
        unfold isFloatConstValid in *.
        destruct f.
        { unfold floatToReal in *.
          simpl in *.
          inversion H0.
        }
        {
          intuition.
        }
        {
          intuition.
        }
        {
          unfold floatToReal in *.
          simpl in *.
          inversion H0.
        }
       Qed.
   apply Forall_forall.
  intros.
  unfold denote_singleBoundTermNew. 
  intuition.
  destruct expr. 
  {
    unfold bound_term in *.
    simpl in *.
    destruct H0.
    {
      rewrite <-H0 in H1.
      simpl in H1.
      unfold isVarValid in H1.
      specialize (H1 fState).
      rewrite <- Heqo in H1.
      revert H1 Heqo0.
      apply floatConstValidityProof.
    }   
    {
      intuition.
    }
  }
  {
    unfold bound_term in *.
    simpl in *.
    destruct H0.
    {
      subst.
      simpl in *.
      decompose [and] H1.
      inversion Heqo.
      rewrite <-H6 in H5.
      revert H5 Heqo0.
      apply floatConstValidityProof.
    }
    {
      destruct H0. 
      {
        subst.
        simpl in *.
        unfold Semantics.eval_comp in *.
        simpl in *.
        decompose [and] H1.
      inversion Heqo.
      rewrite <-H6 in H5.
      revert H5 Heqo0.
      apply floatConstValidityProof.
     
    }
      {
        intuition.
        }
  }
    }
  {
    unfold bound_term in *.
    simpl in *.
    destruct H0.
    {
      subst.
      simpl in *.
      inversion Heqo.
      rewrite <- H2 in H1.
      revert H1 Heqo0.
      apply floatConstValidityProof.
     

    }
    {
      intuition.
    }
  }
  {
      
       
       Lemma plusResultValidityProof : forall expr1 expr2 fState f, plusResultValidity expr1 expr2 -> (Some f = lift2 
                                                                                                                  (Bplus custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                                                                                                         custom_nan mode_NE) (eval_NowTerm fState expr1)
                                                                                                                  (eval_NowTerm fState expr2)) -> None = floatToReal f ->False.
         intros.

         unfold plusResultValidity in *.
         specialize (H fState).
         rewrite <- H0 in H.
         revert H H1.
         apply floatConstValidityProof.
       Qed.
           Lemma minusResultValidityProof : forall expr1 expr2 fState f, minusResultValidity expr1 expr2 -> (Some f = lift2 
                                                                                                                  (Bminus custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                                                                                                         custom_nan mode_NE) (eval_NowTerm fState expr1)
                                                                                                                  (eval_NowTerm fState expr2)) -> None = floatToReal f ->False.
         intros.
         unfold minusResultValidity in *.
         specialize (H fState).
         rewrite <- H0 in H.
         revert H H1.
         apply floatConstValidityProof.
       Qed.
            Lemma multResultValidityProof : forall expr1 expr2 fState f, multResultValidity expr1 expr2 -> (Some f = lift2 
                                                                                                                  (Bmult custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                                                                                                         custom_nan mode_NE) (eval_NowTerm fState expr1)
                                                                                                                  (eval_NowTerm fState expr2)) -> None = floatToReal f ->False.
         intros.
         unfold multResultValidity in *.
         specialize (H fState).
         rewrite <- H0 in H.
         revert H H1.
         apply floatConstValidityProof.
       Qed.
       simpl in *.    
       eapply In_cross_In in H0.
       forward_reason.
       simpl in *.
       destruct H3.
       {
         unfold simpleBound in *.
         subst.
         simpl in *.
         decompose [and] H1.
         revert H9 Heqo Heqo0.
         apply plusResultValidityProof.  
       }
       {
         destruct H3.
         {
           unfold simpleBound4 in *.
           subst.
           simpl in *.
           decompose [and] H1.
           revert H9 Heqo Heqo0.
           apply plusResultValidityProof.  
         }
         {
           destruct H3.
           {
             unfold simpleBound9 in *.
             subst.
             simpl in *.
             decompose [and] H1.
             revert H10 Heqo Heqo0.
             apply plusResultValidityProof.  
           }
           {
             destruct H3.
             {
               unfold simpleBound10 in *.
               subst.
               simpl in *.
               decompose [and] H1.
               revert H9 Heqo Heqo0.
               apply plusResultValidityProof.  
             }
             {
               intuition.
             }
           }
         }
       }
  }
  {
     simpl in *.    
       eapply In_cross_In in H0.
       forward_reason.
       simpl in *.
       destruct H3.
       {
         subst.
         simpl in *.
         decompose [and] H1.
         revert H9 Heqo Heqo0.
         apply minusResultValidityProof.  
       }
       {
         destruct H3.
         {
           subst.
           simpl in *.
           decompose [and] H1.
           revert H9 Heqo Heqo0.
           apply minusResultValidityProof.  
         }
         {
           intuition.  
         }
       }
  }
  {
    simpl in *.    
       eapply In_cross_In in H0.
       forward_reason.
       simpl in *.
       destruct H3.

       {
         subst.
         simpl in *.
         decompose [and] H1.
         revert H10 Heqo Heqo0.
         apply multResultValidityProof.  
       }
       {
         destruct H3.
         {
           subst.
           simpl in *.
           decompose [and] H1.
           revert H10 Heqo Heqo0.
           apply multResultValidityProof.  
         }
         {
            destruct H3.
       {
         subst.
         simpl in *.
         decompose [and] H1.
         revert H10 Heqo Heqo0.
         apply multResultValidityProof.  
       }
       {
         destruct H3.
         {
           subst.
           simpl in *.
           decompose [and] H1.
           revert H10 Heqo Heqo0.
           apply multResultValidityProof.  
         }  
         { intuition. }
         }
}          
}         
}
       }

Qed.
 *)
  Admitted.
