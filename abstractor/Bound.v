Require Import Coq.micromega.Psatz.
Require Import Coq.Reals.Raxioms.
Require Import Coq.micromega.Psatz.
Require Import compcert.flocq.Core.Fcore_defs.

Require Import compcert.lib.Integers.
Require Import Coq.Reals.Rdefinitions.
Require Import List.
Import ListNotations.
Require Import Logic.Syntax.
Require Import Logic.Semantics.
Require Import Logic.Lib.
Require Import Logic.Automation.
Require Import compcert.flocq.Appli.Fappli_IEEE.
Require Import compcert.flocq.Appli.Fappli_IEEE_bits.
Require Import compcert.flocq.Core.Fcore_Raux.
Require Import Source.
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

Record singleBoundTerm : Type := mkSBT {lb : fstate -> R;
                                 ub : fstate -> R ; 
                                 premise : fstate -> Prop}. 

(*used for addition when the result is positive and multiplication when both the arguments are positive*)

(* Definition bd := mkSBT (RealT R0) (RealT R0) (RealT R0 > RealT R0) .*)
Require Import Charge.Logics.ILInsts.

(* need "arithable" typeclass with addition, subtraction, multipliction, division
   make Terms arithable, as well as real numbers and stuff
 *)
Class Arithable (T : Type) : Type :=
  { a_plus : T -> T -> T;
    a_minus : T -> T -> T;
    a_mult : T -> T -> T
  }.

Class ArithableX (T : Type) (aT : Arithable T) : Type :=
  { (*exp : T -> T;*)
    ax_sin : T -> T;
    ax_cos : T -> T;
    ax_inv : T -> T
  }.

Class Comparable (A L : Type) : Type :=
  {
    c_eq  : A -> A -> L;
    (*ac_neq : A -> A -> L;*)
    c_lt  : A -> A -> L;
    c_le  : A -> A -> L;
    c_gt  : A -> A -> L;
    c_ge  : A -> A -> L
  }.

Instance Arithable_Term : Arithable Term :=
  { a_plus := PlusT;
    a_minus := MinusT;
    a_mult := MultT
  }.

Instance ArithableX_Term : ArithableX Term _ :=
  { ax_sin := SinT;
    ax_cos := CosT;
    ax_inv := InvT
  }.

Instance Comparable_Term : Comparable Term Formula :=
  { c_eq a b := Comp a b Eq;
    c_lt a b := Comp a b Lt;
    c_le a b := Comp a b Le;
    c_gt a b := Comp a b Gt;
    c_ge a b := Comp a b Ge
  }.

Instance Arithable_R : Arithable R :=
  { a_plus := Rplus;
    a_minus := Rminus;
    a_mult := Rmult
  }.

Instance ArithableX_R : ArithableX R _ :=
  { ax_sin := Rtrigo_def.sin;
    ax_cos := Rtrigo_def.cos;
    ax_inv := Rinv
  }.

Instance Comparable_R : Comparable R Prop :=
  { c_eq a b := eq a b;
    c_lt a b := Rlt a b;
    c_le a b := Rle a b;
    c_gt a b := Rgt a b;
    c_ge a b := Rge a b
  }.

Instance Comparable_RT : Comparable R Type :=
  { c_eq a b := eq a b;
    c_lt a b := Rlt a b;
    c_le a b := Rle a b;
    c_gt a b := Rgt a b;
    c_ge a b := Rge a b
  }.

Instance Arithable_Nat : Arithable nat :=
  { a_plus := Peano.plus;
    a_minus := Peano.minus;
    a_mult := Peano.mult
  }.

Instance Comparable_Nat : Comparable nat Prop :=
  { c_eq a b := eq a b;
    c_lt a b := lt a b;
    c_le a b := le a b;
    c_gt a b := gt a b;
    c_ge a b := ge a b
  }.

Unset Printing Notations.

Instance Arithable_Z : Arithable Z :=
  {
    a_plus := Z.add;
    a_minus := Z.sub;
    a_mult := Z.mul
  }.

Check (1 < 1)%Z.

Instance Comparable_Z : Comparable Z Prop :=
  {
    c_eq a b := eq a b;
    c_lt a b := Z.lt a b;
    c_le a b := Z.le a b;
    c_gt a b := Z.gt a b;
    c_ge a b := Z.ge a b
  }.

Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Applicative.

(*
Instance arithable_Lift'
         (T1 : Type) (T2 : Type)
         (aT1 : Arithable T1) : Arithable (T2 -> T1) :=
  {
    plus a b := (fun c => plus (a c) (b c));
    minus a b := (fun c => minus (a c) (b c));
    mult a b := (fun c => mult (a c) (b c))
  }.
*)

Definition Arithable_Applicative
         (A : Type) (F : Type -> Type)
         (aA : Arithable A) (apF : Applicative F) : Arithable (F A) :=
  {|
    a_plus a b := ap (ap (pure a_plus) a) b;
    a_minus a b := ap (ap (pure a_minus) a) b;
    a_mult a b := ap (ap (pure a_mult) a) b
  |}.

Instance Arithable_Lift
         (A T : Type) (aA : Arithable A) : Arithable (T -> A) :=
  Arithable_Applicative A (Fun T) aA (Applicative_Fun T).

Definition g := (a_plus (fun (_ : nat) => 4) (fun (_ : nat) => 5)).

Definition ArithableX_Applicative
           (A : Type) (F : Type -> Type)
           (aA : Arithable A)
           (axA : ArithableX A aA) (apF : Applicative F)
  : ArithableX (F A) (Arithable_Applicative A F aA apF) :=
  {|
    ax_inv := ap (pure ax_inv);
    ax_sin := ap (pure ax_sin);
    ax_cos := ap (pure ax_cos)
  |}.

Instance ArithableX_Lift (A T : Type) (aA : Arithable A) (axA : ArithableX A aA)
  : ArithableX (T -> A) (Arithable_Lift A T aA) :=
  ArithableX_Applicative A (Fun T) aA axA (Applicative_Fun T).

Definition Comparable_Applicative
           (A L : Type) (F : Type -> Type) (cAL : Comparable A L) (apF : Applicative F) : Comparable (F A) (F L) :=
  {|
    c_eq a b := ap (ap (pure c_eq) a) b;
    c_lt a b := ap (ap (pure c_lt) a) b;
    c_le a b := ap (ap (pure c_le) a) b;
    c_gt a b := ap (ap (pure c_gt) a) b;
    c_ge a b := ap (ap (pure c_ge) a) b
  |}.

Instance Comparable_Lift (A T L : Type) (cAL : Comparable A L) :
  Comparable (T -> A) (T -> L) :=
  Comparable_Applicative A L (Fun T) cAL (Applicative_Fun T).

(* Notations using arithable *)
Notation "x + y" := (a_plus x y) : arithable_scope.
Notation "x - y" := (a_minus x y) : arithable_scope.
Notation "x * y" := (a_mult x y) : arithable_scope.

(* Notations using arithableX *)
Notation "/ x" := (ax_inv x) : arithable_scope.

(* Notations using comparable *)
(* TODO: give these explicit levels? *)
Notation "x = y"  := (c_eq x y) : arithable_scope.
Notation "x < y"  := (c_lt x y) : arithable_scope.
Notation "x <= y" := (c_le x y) : arithable_scope.
Notation "x > y"  := (c_gt x y) : arithable_scope.
Notation "x >= y" := (c_ge x y) : arithable_scope.

(* another useful ILogic operator, bi-implication *)
Definition lbiimpl {L : Type} {iloL : ILogicOps L} (P Q : L) :=
  (P -->> Q) //\\ (Q -->> P).

Notation "a <<-->> b" := (lbiimpl a b) (at level 90).

Definition bd := mkSBT (fun _ => R0) (fun _ => R0) (lfalse).

Local Open Scope arithable_scope.

Definition simpleBound 
           (triple1 triple2:singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R))  
           (fla: fstate -> Prop) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple1) (lb triple2)) * (fun _ => R1 - error)) 
        ((combFunc (ub triple1) (ub triple2)) * (fun _ => R1 + error)) 
        fla. 

(*used for subtraction when the result is positive*)
Definition simpleBound2 
           (triple1 triple2:singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R))  
           (fla:fstate -> Prop) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple1)  (ub triple2)) * (fun _ => R1 - error)) 
        ((combFunc (ub triple1) (lb triple2)) * (fun _ => R1 + error)) 
        fla. 

(*used for multiplication - when both the arguments is negative*)
Definition simpleBound3 
           (triple1 triple2:singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R))  
           (fla:fstate -> Prop) : 
  singleBoundTerm := 
  mkSBT ((combFunc (ub triple1)  (ub triple2)) * (fun _ => R1 - error)) 
        ((combFunc (lb triple1) (lb triple2)) * (fun _ => R1 + error)) 
        fla.

(*used for addition - negative result*)
Definition simpleBound4 
           (triple1 triple2:singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R))  
           (fla:fstate -> Prop) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple1)  (lb triple2)) * (fun _ => R1 + error)) 
        ((combFunc (ub triple1) (ub triple2)) * (fun _ => R1 - error)) 
        fla.

(*used for subtraction when the result is negative*)
Definition simpleBound5 
           (triple1 triple2:singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R))  
           (fla:fstate -> Prop) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple1)  (ub triple2)) * (fun _ => R1 + error)) 
        ((combFunc (ub triple1) (lb triple2)) * (fun _ => R1 - error)) 
        fla.

(*used for multiplication - when one of the arguments is negative*)
Definition simpleBound6 
           (triple1 triple2:singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R))  
           (fla:fstate -> Prop) : 
  singleBoundTerm := 
  mkSBT ((combFunc (ub triple1)  (lb triple2)) * (fun _ => R1 + error)) 
        ((combFunc (lb triple1) (ub triple2)) * (fun _ => R1 - error)) 
        fla.

(*used for multiplication - when one of the arguments is negative*)
Definition simpleBound7 
           (triple1 triple2:singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R))  
           (fla:fstate -> Prop) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple1)  (ub triple2)) * (fun _ => R1 + error)) 
        ((combFunc (ub triple1) (lb triple2)) * (fun _ => R1 - error)) 
        fla.

(*used for multiplication - when one of the arguments is negative*)
Definition simpleBound8 
           (triple1 triple2:singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R))  
           (fla:fstate -> Prop) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple1)  (ub triple2)) * (fun _ => R1 + error)) 
        ((combFunc (ub triple1) (lb triple2)) * (fun _ => R1 + error)) 
        fla.

(*used for additon - when lb1 + lb2 < floatMin*)
Definition simpleBound9
           (triple1 triple2:singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R))  
           (fla:fstate -> Prop) : 
  singleBoundTerm := 
  mkSBT (fun _ => 0%R)
        ((combFunc (ub triple1) (ub triple2)) * (fun _ => R1 + error)) 
        fla.

Definition floatMax:= bpow radix2 custom_emax.
Definition floatMin := bpow radix2 custom_emin%Z.

(*used for addition when ub1 + ub2 < floatMin*)
Definition simpleBound10
           (triple1 triple2:singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R))  
           (fla:fstate -> Prop) : 
  singleBoundTerm := 
  mkSBT (fun _ => 0%R) (fun _ => floatMin)
        fla.

(*used for subtraction - when lb1 + lb2 is greater than -floatMin*)
Definition simpleBound11
           (triple1 triple2:singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R))  
           (fla:fstate -> Prop) : 
  singleBoundTerm := 
  mkSBT ((combFunc (lb triple1)  (lb triple2)) * (fun _ => R1 + error)) (fun _ => 0%R)
        fla.

Definition isFloatConstValid (f:binary_float custom_prec custom_emax) : Prop 
  := match f with 
       | B754_zero _ => True
       | B754_infinity _=> False
       | B754_nan _ _=> False
       | B754_finite _ _ _ _=> True
     end.


Definition plusResultValidity (t1 t2 : NowTerm) (fState : fstate):  Prop:= 
      (
          let result := (lift2
                           (Bplus custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                  custom_nan mode_NE) (eval_NowTerm fState t1) (eval_NowTerm fState t2)) 
          in match result with 
                | Some f => isFloatConstValid f 
                | None => False
             end).

Definition minusResultValidity (t1 t2 : NowTerm) (fState : fstate) : Prop := 
      (
          let result := (lift2
                           (Bminus custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                  custom_nan mode_NE) (eval_NowTerm fState t1) (eval_NowTerm fState t2)) 
          in match result with 
                | Some f => isFloatConstValid f 
                | None => False
              end).

Definition multResultValidity (t1 t2 : NowTerm) (fState : fstate) : Prop := 
      (
          let result := (lift2
                           (Bmult custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                  custom_nan mode_NE) (eval_NowTerm fState t1) (eval_NowTerm fState t2)) 
          in match result with 
                | Some f => isFloatConstValid f 
                | None => False
             end).

Check eval_term.

(* "lift over float state" *)
Definition lofst (r : R) : fstate -> R :=
  fun _ => r.


Definition floatToReal (f:binary_float custom_prec custom_emax) : option R :=
  match f with 
    | B754_zero _ =>  Some (B2R _ _ f)
    | B754_infinity _ => None
    | B754_nan _ _ => None
    | _ => Some (B2R _ _ f)
    end.



Definition validFloat (f : binary_float custom_prec custom_emax) : Prop :=
  exists r, (eq (Some r) (floatToReal f)).


Definition combineTriplePlus (triple triple2 : singleBoundTerm) (t1 t2 : NowTerm):=
  ((simpleBound triple triple2 a_plus 
                (premise triple //\\
                 premise triple2 //\\ 
                 ((lofst floatMin <= lb triple + lb triple2)) //\\ 
                 ((ub triple + ub triple2)*(lofst (1+error)) < lofst floatMax) //\\
                 (lb triple + lb triple2 >= lofst R0) //\\ 
                 (fun fState => exists f, (Some f = eval_NowTerm fState t1 /\ validFloat f)) //\\
                 (fun fState => exists f, (Some f = eval_NowTerm fState t2 /\ validFloat f))
   ))
     :: (simpleBound4 triple triple2 a_plus 
                      (premise triple //\\ 
                       premise triple2 //\\ 
                       (lofst floatMin <= ((lofst 0 - ub triple) + (lofst 0 - ub triple2))) //\\
                       (((lofst 0 - lb triple + (lofst 0 - lb triple2))*(lofst (1+error))) < lofst floatMax) //\\ 
                       (ub triple + ub triple2 < lofst R0)  //\\ 
                 (fun fState => exists f, (Some f = eval_NowTerm fState t1 /\ validFloat f)) //\\
                 (fun fState => exists f, (Some f = eval_NowTerm fState t2 /\ validFloat f))
))
     :: (simpleBound9 triple triple2 a_plus 
                      (premise triple //\\ 
                       premise triple2 //\\
                       (lb triple + lb triple2 < lofst floatMin) //\\ 
                       (ub triple + ub triple2 >= lofst floatMin) //\\ 
                       ((ub triple + ub triple2)*(lofst (1+error)) < lofst floatMax) //\\ 
                       (lb triple + lb triple2 >= lofst R0)//\\ 
                 (fun fState => exists f, (Some f = eval_NowTerm fState t1 /\ validFloat f)) //\\
                 (fun fState => exists f, (Some f = eval_NowTerm fState t2 /\ validFloat f))
))
     :: (simpleBound10 triple triple2 a_plus
                      (premise triple //\\ 
                       premise triple2 //\\
                       (ub triple + ub triple2 < lofst floatMin) //\\ 
                       ((ub triple + ub triple2)*(lofst (1+error)) < lofst floatMax) //\\ 
                       (lb triple + lb triple2 >= lofst R0) //\\ 
                 (fun fState => exists f, (Some f = eval_NowTerm fState t1 /\ validFloat f)) //\\
                 (fun fState => exists f, (Some f = eval_NowTerm fState t2 /\ validFloat f))
)) 
     :: List.nil). 

(*
    (((ub triple - ub triple2 >= floatMin) //\\ (lb triple - lb triple2 >=floatMin) //\\ (ub triple2 - lb triple >= floatMin)) \/
                                         ((ub triple2 - ub triple >= floatMin) //\\ (lb triple - lb triple2 >=floatMin)) \/
                                         ((ub triple - ub triple2 >= floatMin) /\ (lb triple2 - lb triple >= floatMin)) \/
                                         ((ub triple2 - ub triple >=floatMin) /\ (ub triple - lb triple2 >=floatMin) /\ (lb triple2 - lb triple >= floatMin)) ) /\
*)
Definition combineTripleMinus (triple triple2 : singleBoundTerm) (t1 t2:NowTerm):=
  ((simpleBound2 triple triple2 a_minus 
                 (premise triple //\\ 
                  premise triple2  //\\ 
                  (lb triple >= ub triple2) //\\
                 (lofst floatMin <= lb triple - ub triple2) //\\ 
                ((ub triple - lb triple2)*(lofst (1+error)) < lofst floatMax)//\\
                (fun fState => exists f, (Some f = eval_NowTerm fState t1 /\ validFloat f))//\\
                 (fun fState => exists f, (Some f = eval_NowTerm fState t2 /\ validFloat f))))
     :: (simpleBound5 triple triple2 a_minus 
                      (premise triple //\\ 
                       premise triple2 //\\
                       (ub triple <= lb triple2) //\\
                       (lofst floatMin <= lb triple2 - ub triple) //\\
                       ((ub triple2 - lb triple)*(lofst (1+error)) < lofst floatMax) //\\
                       (fun fState => exists f, (Some f = eval_NowTerm fState t1 /\ validFloat f))//\\
                 (fun fState => exists f, (Some f = eval_NowTerm fState t2 /\ validFloat f))))
                       :: List.nil).
   
Definition combineTripleMult (triple triple2 : singleBoundTerm) (t1 t2:NowTerm):=
  ((simpleBound triple triple2 a_mult 
                (premise triple //\\ 
                 premise triple2 //\\ 
                 (lofst floatMin <= lb triple * lb triple2) //\\ 
                 ((ub triple * ub triple2)*(lofst (1+error)) < lofst floatMax) //\\ 
                 (lb triple >= lofst R0) //\\ (lb triple2 >= lofst R0) //\\ 
                (fun fState => exists f, (Some f = eval_NowTerm fState t1 /\ validFloat f))//\\
                 (fun fState => exists f, (Some f = eval_NowTerm fState t2 /\ validFloat f))))
    :: (simpleBound3 triple triple2 a_mult
                      (premise triple //\\ 
                       premise triple2 //\\ 
                       (lofst floatMin <= (lofst 0 - ub triple) * (lofst 0 - ub triple2)) //\\ 
                       (((lofst 0 - lb triple) * (lofst 0 - lb triple2))*(lofst (1+error)) < lofst floatMax) //\\ 
                       (ub triple < lofst R0) //\\ (ub triple2 < lofst R0) //\\ 
                       (fun fState => exists f, (Some f = eval_NowTerm fState t1 /\ validFloat f))//\\
                 (fun fState => exists f, (Some f = eval_NowTerm fState t2 /\ validFloat f))))
          :: (simpleBound6 triple triple2 a_mult
                      (premise triple //\\ 
                       premise triple2 //\\ 
                       (lofst floatMin <= (lb triple) * (lofst 0 - (ub triple2))) //\\ 
                       ((ub triple * (lofst 0 - lb triple2))*(lofst (1+error)) < lofst floatMax) //\\ 
                       (lb triple >= lofst R0) //\\  (ub triple2 < lofst R0) //\\ (fun fState => exists f, (Some f = eval_NowTerm fState t1 /\ validFloat f))//\\
                 (fun fState => exists f, (Some f = eval_NowTerm fState t2 /\ validFloat f)))) 
                      ::  (simpleBound7 triple triple2 a_mult 
                                        (premise triple //\\ 
                                         premise triple2 //\\ 
                                         (lofst floatMin <= (lofst 0 - ub triple) * lb triple2) //\\ 
                                         (((lofst 0 - lb triple) * (ub triple2))*(lofst (1+error)) < lofst floatMax) //\\ 
                                         (ub triple < lofst R0) //\\  (lb triple2 >= lofst R0) //\\ (fun fState => exists f, (Some f = eval_NowTerm fState t1 /\ validFloat f))//\\
                 (fun fState => exists f, (Some f = eval_NowTerm fState t2 /\ validFloat f)))) :: List.nil).   
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
          List.In x (cross f ls rs) <<-->>
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

    Check simpleBound4.

Definition plusMinusfoldBoundListWithTriple 
           (list:list singleBoundTerm) 
           (triple: singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R)) 
           (simpleBoundFunc1 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              ((fstate -> R) -> (fstate -> R) -> (fstate -> R)) -> 
                              (fstate -> Prop) -> 
                              singleBoundTerm) 
           (simpleBoundFunc2 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              ((fstate -> R) -> (fstate -> R) -> (fstate -> R)) -> 
                              (fstate -> Prop) -> 
                              singleBoundTerm) 
  := 

  fold_right (fun triple2 curList => ((simpleBoundFunc1 triple triple2 combFunc 
                                                      (premise triple //\\ 
                                                       premise triple2 //\\ 
                                                       ((lofst floatMin <= lb triple + lb triple2) \\// (lofst floatMin <= ((lofst 0 - lb triple) + (lofst 0 - lb triple2))) \\// ((lb triple + lb triple = lofst 0) //\\ (ub triple + ub triple = lofst 0))) //\\ 
                                                       (ub triple + ub triple2 < lofst floatMax) //\\
                                                             ((lofst 0 - ub triple) + (lofst 0 - ub triple2) < lofst floatMax) //\\ 
                                                       (lb triple + lb triple2 >= lofst R0)))
                                       :: ((simpleBoundFunc2 triple triple2 combFunc 
                                                            (premise triple //\\ 
                                                             premise triple2 //\\ 
                                                            ((lofst floatMin <= lb triple + lb triple2) \\// (lofst floatMin <= ((lofst 0 - lb triple) + (lofst 0 - lb triple2))) \\// ((lb triple + lb triple = lofst 0) //\\ (ub triple + ub triple = lofst 0))) //\\ 
                                                             (ub triple + ub triple2 < lofst floatMax) //\\
                                                             ((lofst 0 - ub triple) + (lofst 0 - ub triple2) < lofst floatMax) //\\ 
                                                             (ub triple + ub triple2 < lofst R0))) ::
                                             curList))) List.nil list. 
Print Scopes.

Locate nat.

Definition multfoldBoundListWithTriple 
           (list:list singleBoundTerm) 
           (triple: singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R)) 
           (simpleBoundFunc1 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              ((fstate -> R) -> (fstate -> R) -> (fstate -> R)) -> 
                              (fstate -> Prop) -> 
                              singleBoundTerm) 
           (simpleBoundFunc2 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              ((fstate -> R) -> (fstate -> R) -> (fstate -> R)) -> 
                              (fstate -> Prop) -> 
                              singleBoundTerm) 
           (simpleBoundFunc3 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              ((fstate -> R) -> (fstate -> R) -> (fstate -> R)) -> 
                              (fstate -> Prop) -> 
                              singleBoundTerm) 
           (simpleBoundFunc4 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              ((fstate -> R) -> (fstate -> R) -> (fstate -> R)) -> 
                              (fstate -> Prop) -> 
                              singleBoundTerm) 
  := 

    fold_right (
        fun triple2 curList => (simpleBoundFunc1 triple triple2 combFunc  (premise triple //\\ 
                                                                           premise triple2 //\\ 
                                                                           ((lofst floatMin <= lb triple + lb triple2) \\// (lofst floatMin <= ((lofst 0 - lb triple) + (lofst 0 - lb triple2))) \\// ((lb triple + lb triple = lofst 0) //\\ (ub triple + ub triple = lofst 0)))//\\
                                                                           (ub triple + ub triple2 < lofst floatMax) //\\  
                                                                           ((lofst 0 - ub triple) + (lofst 0 - ub triple2) < lofst floatMax) //\\
                                                                           (lb triple >= lofst R0) //\\ (lb triple2 >= lofst R0)))
                                 :: ((simpleBoundFunc2 triple triple2 combFunc 
                                                       (premise triple //\\ 
                                                        premise triple2 //\\ 
                                                        ((lofst floatMin <= lb triple + lb triple2) \\// (lofst floatMin <= ((lofst 0 - lb triple) + (lofst 0 - lb triple2))) \\// ((lb triple + lb triple = lofst 0) //\\ (ub triple + ub triple = lofst 0))) //\\ 
                                                        (ub triple + ub triple2 < lofst floatMax) //\\
                                                        ((lofst 0 - ub triple) + (lofst 0 - ub triple2) < lofst floatMax) //\\
                                                        (ub triple < lofst R0) //\\ (ub triple2 < lofst R0)))
                                       :: ((simpleBoundFunc3 triple triple2 combFunc 
                                                             (premise triple //\\ 
                                                              premise triple2 //\\ 
                                                              ((lofst floatMin <= lb triple + lb triple2) \\// (lofst floatMin <= ((lofst 0 - lb triple) + (lofst 0 - lb triple2))) \\// ((lb triple + lb triple = lofst 0) //\\ (ub triple + ub triple = lofst 0))) //\\ 
                                                              (ub triple + ub triple2 < lofst floatMax) //\\
                                                              ((lofst 0 - ub triple) + (lofst 0 - ub triple2) < lofst floatMax) //\\
                                                              (lb triple >= lofst R0) //\\ (ub triple2 < lofst R0)))
                                             :: ((simpleBoundFunc4 triple triple2 combFunc 
                                                                   (premise triple //\\ 
                                                                    premise triple2 //\\ 
                                                                    ((lofst floatMin <= lb triple + lb triple2) \\// (lofst floatMin <= ((lofst 0 - lb triple) + (lofst 0 - lb triple2))) \\// ((lb triple + lb triple = lofst 0) //\\ (ub triple + ub triple = lofst 0))) //\\ 
                                                                    ((ub triple + ub triple2 < lofst floatMax) //\\
                                                                     ((lofst 0 - ub triple) + (lofst 0 - ub triple2) < lofst floatMax)) //\\ 
                                                                    (ub triple < lofst R0) //\\ (lb triple2 >= lofst R0)))
                                                   ::   
                                                   curList)))) List.nil list. 

Definition plusMinusfoldListwithList 
           (list1 list2: list singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R)) 
           (simpleBoundFunc1 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              ((fstate -> R) -> (fstate -> R) -> (fstate -> R)) -> 
                              (fstate -> Prop) -> 
                              singleBoundTerm )
           (simpleBoundFunc2 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              ((fstate -> R) -> (fstate -> R) -> (fstate -> R)) -> 
                              (fstate -> Prop) -> 
                              singleBoundTerm )
           
  : list singleBoundTerm :=
 
  fold_right (fun triple list => list ++ (plusMinusfoldBoundListWithTriple list1 triple combFunc simpleBoundFunc1 simpleBoundFunc2)) List.nil list2.

Definition multfoldListwithList 
           (list1 list2: list singleBoundTerm) 
           (combFunc: (fstate -> R) -> (fstate -> R) -> (fstate -> R)) 
           (simpleBoundFunc1 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              ((fstate -> R) -> (fstate -> R) -> (fstate -> R)) -> 
                              (fstate -> Prop) -> 
                              singleBoundTerm )
           (simpleBoundFunc2 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              ((fstate -> R) -> (fstate -> R) -> (fstate -> R)) -> 
                              (fstate -> Prop) -> 
                              singleBoundTerm )
           (simpleBoundFunc3 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              ((fstate -> R) -> (fstate -> R) -> (fstate -> R)) -> 
                              (fstate -> Prop) -> 
                              singleBoundTerm )
           (simpleBoundFunc4 : singleBoundTerm -> 
                              singleBoundTerm -> 
                              ((fstate -> R) -> (fstate -> R) -> (fstate -> R)) -> 
                              (fstate -> Prop) -> 
                              singleBoundTerm )
           
  : list singleBoundTerm :=
 
  fold_right (fun triple list => list ++ (multfoldBoundListWithTriple list1 triple combFunc simpleBoundFunc1 simpleBoundFunc2 simpleBoundFunc3 simpleBoundFunc4)) List.nil list2.




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


Definition isVarValid (v:Var) (fState : fstate) : Prop 
  :=
    match (fstate_lookup fState v) with 
        | Some f => isFloatConstValid f
        | None => False
    end.

Print singleBoundTerm.

(* TODO: need to define lifting through AND and OR... *)
(* Local Close Scope HP_scope. *)
Local Open Scope arithable_scope.

(* "lift prop over float state" *)
Definition lpofst (P : Prop) : fstate -> Prop :=
  fun _ => P.

Definition natBound (n:nat): list singleBoundTerm :=

  [ (mkSBT (lofst ((INR n) *(1-error)) )
           (lofst ((INR n) * (1+error)))
           (lpofst ((floatMin <= (INR n)) //\\ (INR n >= 0%R) //\\  ((INR n)* (1%R+error) <  (floatMax)) ))) ;
    (mkSBT (lofst ((INR n) * (1+error)))
           (lofst ((INR n)*(1-error)))
           (lpofst ((floatMin <= (0%R - INR n)) //\\ (INR n < 0%R) //\\  ((0%R - INR n)* (1%R+error) <  (floatMax)) )  ))].



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
                ) in (mkSBT lb ub (premise //\\ lpofst resultValidPremise))
           )
       end) ::  (addPlusResultValidity t t1 t2) 
  | Nil => Nil
  end.

(* Total version of fstate_lookup that returns 0 if the variable can't be
   found in the variable map, or has an exceptional value.
   (The premise in the SBT will capture the condition that neither of these will happen) *)
Definition fstate_lookup_force (fst : fstate) (v : Var) : R :=
  match fstate_lookup fst v with
  | Some f => FloatToR f
  | None => 0%R
  end.

Fixpoint bound_term (x:NowTerm)  : (list singleBoundTerm):= 
  match x with
    | VarNowN var =>  [mkSBT (fun fst => fstate_lookup_force fst var) (fun fst => fstate_lookup_force fst var) (fun fst => isVarValid var fst)]
    | NatN n =>  natBound n
    | FloatN f => [mkSBT (fun _ => B2R _ _ f) (fun _ => B2R _ _ f) (fun _ => isFloatConstValid f)]
    | PlusN t1 t2 => cross (fun bd1 bd2 => combineTriplePlus bd1 bd2 t1 t2) (bound_term t1) (bound_term t2)
    | MinusN t1 t2 => cross (fun bd1 bd2 => combineTripleMinus bd1 bd2 t1 t2) (bound_term t1) (bound_term t2)
    | MultN t1 t2 =>  cross (fun bd1 bd2 => combineTripleMult bd1 bd2 t1 t2) (bound_term t1) (bound_term t2)
  end.

Local Close Scope HP_scope.
Definition foldBoundProp (evalExpr:option (binary_float custom_prec custom_emax)) (fst:fstate) :=
  match evalExpr with 
  | Some evalExpr =>  
    match floatToReal evalExpr with 
    | Some realEvalExpr => 
      (fun (triple:singleBoundTerm) (prop:Prop) =>
         (prop //\\ 
          ((premise triple fst) 
           -->> (lb triple fst) <= 
              realEvalExpr <= 
              (ub triple fst))%R))
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

 (*
Definition denote_singleBoundTermNew (fst:fstate) (s:singleBoundTerm) : Prop*(R -> float -> Prop) :=
  ((premise s fst),  fun r f => floatToReal f = Some r -> (lb s fst) <= r <= (ub s fst) /\ isFloatConstValid f)%R.*)
(*Definition denote_singleBoundTermNew (fst:fstate) (s:singleBoundTerm) : Prop*(forall f r, floatToReal f = Some r -> Prop) :=
  ((premise s fst), fun f r p =>  (lb s fst) <= r <= (ub s fst) /\ isFloatConstValid f)%R.*)

Definition denote_singleBoundTermNew (fst:fstate) (s:singleBoundTerm) : Prop*(R->Prop) :=
  ((premise s fst), fun f => (lb s fst) <= f <= (ub s fst))%R.


(* Previous version; I'm not completely convinced new version does the right thing. --M *)
(* More convinced now. --M *)
(*
Definition denote_singleBoundTermNew (st:state) (s:singleBoundTerm) : Prop*(R->Prop) :=
  let tr := traceFromState st in                                              
  let s1 := Stream.hd tr in
  let s2 := Stream.hd (Stream.tl tr) in
  ((eval_formula (premise s) tr, fun f => eval_term (lb s) s1 s2 <= f <= eval_term (ub s) s1 s2)%R).*)



Definition denote_singleBoundTerm (f : R) (fst : fstate) (s : singleBoundTerm) (fl:float): Prop :=
  ((premise s fst)
   -> (lb s fst) <= f <= (ub s fst))%R.

(* Again, not sure about this one --M *)

(*
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
end.*)


Definition boundDef' (expr : NowTerm) (fst : fstate) : Prop :=
  match eval_NowTerm fst expr with
  | Some evalAsF =>

    List.Forall
      (fun term : singleBoundTerm =>
         premise term fst ->
         match floatToReal evalAsF with
         | Some r => ((lb term fst <= r <= ub term fst)%R /\ isFloatConstValid evalAsF)
         | None => False
         end) (bound_term expr)

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

Lemma and_proof : forall x1 x2 : Prop, x1 //\\ x2 -->> x1.
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

Check lb.

Lemma fold_right_subList_inferring: forall a x lst fst, fold_right (fun (triple : singleBoundTerm) (prop : Prop) =>
         prop //\\
         ((premise triple fst) -->>
          ((lb triple fst) <= x <=
           (ub triple fst))%R)) True (a::lst) -->> fold_right (fun (triple : singleBoundTerm) (prop : Prop) =>
         prop //\\
         ((premise triple fst) -->>
          ((lb triple fst) <= x <=
           (ub triple fst)))%R) True lst   //\\  ((premise a fst) -->>
       ((lb a fst) <= x <=
        (ub a fst))%R).
intros.
simpl in *.
tlaIntuition.
Qed.

(* TODO there is a small chance I re-parenthesized this one wrong... --M *)
Lemma fold_right_combine : forall fst lst a x,   fold_right
         (fun (triple : singleBoundTerm) (prop : Prop) =>
          prop //\\
          ((premise triple fst) -->>
           ((lb triple fst) <= x <=
            (ub triple fst))%R)) True lst //\\ 
             ((premise a fst) -->>
       ((lb a fst) <= x <=
        (ub a fst))%R) -->>   fold_right (fun (triple : singleBoundTerm) (prop : Prop) =>
          prop //\\
          ((premise triple fst) -->>
           ((lb triple fst) <= x <=
            (ub triple fst))%R)) True (a::lst).

intros.
simpl in *.
intuition.
Qed.

Lemma fold_right_combine_opp :   forall fst lst a x,  fold_right (fun (triple : singleBoundTerm) (prop : Prop) =>
          prop //\\
          ((premise triple fst) -->>
           ((lb triple fst) <= x <=
            (ub triple fst))%R)) True (a::lst) -->> fold_right
         (fun (triple : singleBoundTerm) (prop : Prop) =>
          prop //\\
          ((premise triple fst) -->>
           ((lb triple fst) <= x <=
            (ub triple fst))%R)) True lst //\\ 
             (premise a fst) -->>
       ((lb a fst) <= x <=
        (ub a fst))%R.
intros.
simpl in *.
intuition.
Qed.


Lemma fold_right_inferr_sublist : forall lst1 lst2 fst x, fold_right
        (fun (triple : singleBoundTerm) (prop : Prop) =>
         prop //\\
         ((premise triple fst) -->>
          ((lb triple fst) <= x <=
           (ub triple fst))%R)) True
        (lst1 ++ lst2) -->> fold_right
     (fun (triple : singleBoundTerm) (prop : Prop) =>
      prop //\\
      ((premise triple fst) -->>
       ((lb triple fst) <= x <=
        (ub triple fst))%R)) True lst2 //\\ fold_right
     (fun (triple : singleBoundTerm) (prop : Prop) =>
      prop //\\
      ((premise triple fst) -->>
       ((lb triple fst) <= x <=
        (ub triple fst))%R)) True lst1.
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


Lemma fold_right_two_list :forall lst1 lst2 x fst, 
                      fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop //\\
                ((premise triple fst) -->>
                 ((lb triple fst) <= x <=
                  (ub triple fst)))%R) True
               (lst1 ++ lst2) -->>   (fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop //\\
                ((premise triple fst) -->>
                 ((lb triple fst) <= x <=
                  (ub triple fst))%R)) True
               lst1) //\\ (fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop //\\
                ((premise triple fst) -->>
                 ((lb triple fst) <= x <=
                  (ub triple fst))%R)) True
               lst2) .
  intros.
  split.
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
tlaIntuition.
apply fold_right_inferr_sublist in H.
breakAbstraction.
intuition.
Qed.


  Lemma list3Commutative: forall (a:singleBoundTerm) lst1 lst2, ((a :: lst1) ++ lst2) = a :: (lst1 ++ lst2).
    intros.
    simpl.
    reflexivity.
    Qed.

Lemma fold_right_two_list_opp :forall lst1 lst2 x fst, 
                       (fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop //\\
                ((premise triple fst) -->>
                 ((lb triple fst) <= x <=
                  (ub triple fst))%R)) True
               lst1) //\\ (fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop //\\
                ((premise triple fst) -->>
                 ((lb triple fst) <= x <=
                  (ub triple fst))%R)) True
               lst2) -->> fold_right
               (fun (triple : singleBoundTerm) (prop : Prop) =>
                prop //\\
                ((premise triple fst) -->>
                 ((lb triple fst) <= x <=
                  (ub triple fst))%R)) True
               (lst1 ++ lst2).
  breakAbstraction.
  intros.
  decompose [and] H.
  induction lst1.
  simpl in *.
  intuition.
  rewrite  list3Commutative.
  apply fold_right_combine.
  generalize (fold_right_subList_inferring); intro Hfrsi.
  breakAbstraction. apply Hfrsi in H0.
  decompose [and] H0.
  apply IHlst1 in H2.
  split.
  apply H2.
  apply H3.
  split.
  intuition.
  intuition.
  Qed.
  
 Lemma deNowifyPlus : forall t1 t2, denowify t1 + denowify t2 = denowify (PlusN t1 t2).
intros.
induction t1;
induction t2;
repeat simpl; reflexivity.
Qed.

Local Close Scope HP_scope.
 Require Import compcert.flocq.Prop.Fprop_relative.


Lemma simpleTruth : true = true.
intuition.
Qed.             Lemma truth : true = true.
intuition.
Qed.

Lemma rltProof2 : forall r1 r2,  (r1 < r2)%R -> ( Rlt_bool r1 r2 = true). 
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
           /\ Some f2 = eval_NowTerm fState expr2
                                       /\ validFloat f1 /\ validFloat f2.
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
           /\ Some f2 = eval_NowTerm fState expr2
                                       /\ validFloat f1 /\ validFloat f2.
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
           /\ Some f2 = eval_NowTerm fState expr2
                                       /\ validFloat f1 /\ validFloat f2.
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
Require Import Logic.ArithFacts.
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

Lemma minus: forall x, (eq (1- x) (-x +1)) %Z. 
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
                (Rabs r1 >= r2 -> r1 >= r2 \/ -r1 >= r2)%R. 
            Proof.
              intros.
              unfold Rabs in *. simpl.
              destruct Rcase_abs; psatz R.
            Qed.
            
Lemma absoluteValLt : forall (r1 r2:R) , 
                (Rabs r1 < r2 -> r1 < r2 \/ -r1 < r2)%R. 
Proof.
  intros.
  unfold Rabs in *. simpl.
  destruct Rcase_abs; psatz R. 
Qed.





Declare ML Module "z3Tactic".
(*((ub2 >= lb1) /\ 
      (ub1 >= lb2) /\ 
      (((ub1 - ub2 >= floatMin) /\ (lb1 - lb2 >=floatMin) /\ (ub2 - lb1 >= floatMin)) \/
       ((ub2 - ub1 >= floatMin) /\ (lb1 - lb2 >=floatMin)) \/
       ((ub1 - ub2 >= floatMin) /\ (lb2 - lb1 >= floatMin)) \/
       ((ub2 - ub1 >=floatMin) /\ (ub1 - lb2 >=floatMin) /\ (lb2 - lb1 >= floatMin)) ))*)
Lemma minusfloatMinBoundProof:  forall (x1 x2 lb1 lb2 ub1 ub2:R), 
    (((lb1 >= ub2) /\ (floatMin <= lb1 - ub2)) \/ 
     ((ub1 <= lb2) /\(floatMin <= lb2 - ub1))
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


Lemma multfloatMinBoundProof:  forall (x1 x2 lb1 lb2 ub1 ub2:R), 
    (((floatMin <= lb1 * lb2) /\  (lb1 >= R0) /\ (lb2 >= R0))
    \/ (floatMin <= (0 - ub1) * (0 - ub2) /\ (ub1 < R0) /\ (ub2 < R0)) 
    \/ (floatMin <= lb1 * (0 - ub2) /\ (lb1 >= R0) /\  (ub2 < R0)) 
    \/ (floatMin <= (0 - ub1) * lb2 /\ (ub1 < R0) /\  (lb2 >= R0)) -> lb1 <= x1 -> lb2 <= x2 -> x1 <= ub1 -> x2 <= ub2 -> (Rabs (x1 * x2) >= floatMin))%R. 
Proof.
  breakAbstraction.
  intros;
  pose proof floatMinGt0;
  unfold Rabs;
  destruct Rcase_abs;
  destruct H;
  psatz R.
Qed.

Lemma lbAndUbSumIsZero : forall (lb1 lb2 ub1 ub2 x1 x2: R), ((lb1 + lb2)%R = 0%R /\ (ub1 + ub2)%R = 0%R) ->  (lb1 <= x1 <= ub1)%R ->  (lb2 <= x2 <= ub2)%R -> (x1 + x2 = 0)%R.
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
    ((((floatMin <= lb1 * lb2) /\  (lb1 >= R0) /\ (lb2 >= R0)) 
\/ (floatMin <= (0 - ub1) * (0 - ub2) /\ (ub1 < R0) /\ (ub2 < R0))
\/ (floatMin <= lb1 * (0 - ub2) /\ (lb1 >= R0) /\  (ub2 < R0)) 
\/ (floatMin <= (0 - ub1) * lb2 /\ (ub1 < R0) /\  (lb2 >= R0)))
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
      \/ (floatMin <= 0 - ub1 + (0 - ub2)) -> 
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
                                                                              ( (((lb1 >= ub2)  /\  (floatMin <= lb1 - ub2)) /\  ((ub1 - lb2)*(1+error) < floatMax)) \/ 
                                                                                (((ub1 <= lb2)  /\  (floatMin <= lb2 - ub1)) /\  ((ub2 - lb1)*(1+error) < floatMax)) 
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
                           ((p1 /\ p2) /\ p3) \/ ((p4 /\ p5) /\ p6) -> (p1 /\ p2 ) \/ (p4 /\ p5).
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
    destruct Rcase_abs;
      destruct Rcase_abs;
      destruct Rcase_abs; destruct H1';
      unfold error in *; unfold floatMax in *;
      psatz R.
    
  }
  {
    inversion H.
  }
  {
    inversion H.
  }

  destruct f2.
  {
    
    simpl in H1.
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
    simpl in H1.
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
      psatz R.
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
    simpl in H1,H1'.
    destruct Rcase_abs;
      destruct Rcase_abs;
      destruct Rcase_abs;
      unfold error,floatMax in *;
      psatz R.
  }    
Qed.  
  Lemma abs: forall x y, (x >= y \/ x <= (0-y) -> y <= Rabs x)%R.
  Proof.
    breakAbstraction.
    intros.
         destruct H;unfold Rabs;destruct Rcase_abs; breakAbstraction; psatz R;psatz R. 
        Qed.

        Lemma orExtra : forall (p1 p2:Prop), p1 -> p1 \/ p2.
          breakAbstraction.
        intros.
        intuition.
      Qed.
Lemma plusRoundingTruth3 : forall (f1 f2: float)  (lb1 lb2 ub1 ub2 x1 x2:R), 
    (
      Some x1 = (floatToReal f1) -> 
      Some x2 = (floatToReal f2) ->
      (
        x1 + x2 >= floatMin \/ x1 + x2 <= (0-floatMin)
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
      destruct Rcase_abs; destruct Rcase_abs; destruct Rcase_abs;
      psatz R.
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

    destruct Rcase_abs; destruct Rcase_abs; destruct Rcase_abs;
    unfold error in *;
    unfold floatMax in *;
    psatz R.
    
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
  destruct Rcase_abs; destruct Rcase_abs; destruct Rcase_abs;
  unfold error in *;
  unfold floatMax in *;
  psatz R.

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
        (floatMin <= lb1 + lb2) \/ 
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
    
    (((floatMin <= lb1 * lb2) /\  (lb1 >= R0) /\ (lb2 >= R0)) /\ ((ub1 * ub2)*(1+error) < floatMax)) 

    \/ ((floatMin <= (0 - ub1) * (0 - ub2) /\ (ub1 < R0) /\ (ub2 < R0)) /\ (((0 - lb1) * (0 - lb2))*(1+error) < floatMax))

    \/   ((floatMin <= lb1 * (0 - ub2) /\ (lb1 >= R0) /\  (ub2 < R0)) /\ ((ub1 * (0 - lb2))*(1+error) < floatMax)) 

    \/   ((floatMin <= (0 - ub1) * lb2 /\ (ub1 < R0) /\  (lb2 >= R0)) /\ (((0 - lb1) * (ub2))*(1+error) < floatMax)) ->
    
    
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
          (p1 /\ p2 /\ p3) /\ p4
          \/ (p5 /\ p6 /\ p7) /\ p8 
          \/ (p9 /\ p10 /\ p11) /\ p12
          \/ ( p13 /\ p14 /\ p15) /\ p16 
          ->
          (p1 /\ p2 /\ p3)
          \/ (p5 /\ p6 /\ p7)
          \/ (p9 /\ p10 /\ p11)
          \/ (p13 /\ p14 /\ p15).
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
                decompose [and] H1.
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
               
                decompose [and] H1.
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
              decompose [and] H1.
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
                decompose [and] H1.
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
                decompose [and] H1.
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
              decompose [and] H1.
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
                decompose [and] H1.
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
                  decompose [and] H1.
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
                  decompose [and] H1.
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
              decompose [and] H1.
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
              decompose [and] H1.
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
                decompose [and] H1.
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
                decompose [and] H1.
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
              decompose [and] H1.
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
                decompose [and] H1.
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
                  decompose [and] H1.
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
                  decompose [and] H1.
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
               decompose [and] H1.
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
               decompose [and] H1.
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
                   decompose [and] H1.
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
                   decompose [and] H1.
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
              destruct H1. 
              {
                  decompose [and] H1.
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
                  decompose [and] H1.
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
              decompose [and] H1.
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
              decompose [and] H1.
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
              decompose [and] H1.
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
              decompose [and] H1.
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
              decompose [and] H1.
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
                decompose [and] H1.
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
                  decompose [and] H1.
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
                    decompose [and] H1.
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
              decompose [and] H1.
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
                decompose [and] H1.
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
                  decompose [and] H1.
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
                  decompose [and] H1.
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
               decompose [and] H1.
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
                 decompose [and] H1.
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
                   decompose [and] H1.
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
                   decompose [and] H1.
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
              decompose [and] H1.
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
                decompose [and] H1.
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
                  decompose [and] H1.
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
                  decompose [and] H1.
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
               decompose [and] H1.
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
                 decompose [and] H1.
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
                   decompose [and] H1.
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
                   decompose [and] H1.
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
               decompose [and] H1.
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
                 decompose [and] H1.
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
                   decompose [and] H1.
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
                   decompose [and] H1.
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
    
    (B2R custom_prec custom_emax (Bplus custom_prec custom_emax  custom_precGt0 custom_precLtEmax custom_nan mode_NE f1 f2) =round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (B2R custom_prec custom_emax f1 + B2R custom_prec custom_emax f2)  /\   is_finite custom_prec custom_emax (Bplus custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_NE f1 f2) = true)%R. 
Proof.
  intros.
  pose proof Bplus_correct.
  Set Printing Notations.
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
Print Bminus_correct.
Lemma minusRoundingTruth2 : forall (f1 f2: float)  (r1 r2:R) ,  Some r1 = (floatToReal f1) -> 
                                                                       Some r2 = (floatToReal f2) ->   
                                                                       
                                                                       ((Rabs (round radix2 (FLT_exp (3-custom_emax- custom_prec) custom_prec ) (round_mode mode_NE) (B2R custom_prec custom_emax f1 - B2R custom_prec custom_emax f2))) 
                                                                        <  (bpow radix2 custom_emax))%R -> 
                                                                       (B2R custom_prec custom_emax (Bminus custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_NE f1 f2) =round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (B2R custom_prec custom_emax f1 - B2R custom_prec custom_emax f2)  /\   is_finite custom_prec custom_emax (Bminus custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_NE f1 f2) = true)%R.

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
                                                                      (B2R custom_prec custom_emax (Bmult custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_NE f1 f2) =round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (B2R custom_prec custom_emax f1 * B2R custom_prec custom_emax f2)  /\   is_finite custom_prec custom_emax (Bmult custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_NE f1 f2) = true)%R.

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
    ((floatMin <= INR n /\ INR n >= 0) \/ (floatMin <= 0 -(INR n) /\ INR n < 0) -> floatMin <= Rabs (INR n))%R.
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
      (floatMin <= INR n)%R /\ (INR n >= 0)%R \/
       (floatMin <= 0 - INR n)%R /\ (INR n < 0)%R
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
      (((floatMin <= INR n)%R /\ (INR n >= 0)%R /\  ((INR n)* (1+error) <  (floatMax))%R) \/
       ((floatMin <= 0 - INR n)%R /\ (INR n < 0)%R /\  ((0 -(INR n))* (1+error) <  (floatMax))) 

       ->
       
       (Rabs 
          (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (Z2R (Z.of_nat n))) 
   < (bpow radix2 custom_emax)))%R.
                               
Proof.
  intros.
  pose proof relErrorTruthNat as relErrorTruthNat.
  Lemma orProof: forall (p1 p2 p3 p4 p5 p6 : Prop), (p1 /\ p2 /\ p3) \/ (p4 /\ p5 /\ p6) -> (p1 /\ p2) \/ (p4 /\ p5).
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


Lemma natRoundingTruth2 : forall (f:float)  (n:nat),
    Some f = Some (nat_to_float n)->
    (Rabs 
       (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (Z2R (Z.of_nat n))) 
     < (bpow radix2 custom_emax))%R ->
    B2R custom_prec custom_emax (Fappli_IEEE_extra.BofZ custom_prec custom_emax custom_precGt0 custom_precLtEmax (Z.of_nat n)) =
    round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (Z2R (Z.of_nat n)) /\ is_finite custom_prec custom_emax
                  (Fappli_IEEE_extra.BofZ custom_prec custom_emax
                     custom_precGt0 custom_precLtEmax 
                     (Z.of_nat n)) = true.                         

Proof.       
  intros.
  pose proof Fappli_IEEE_extra.BofZ_correct as Z2Rcorrect.
  Set Printing Notations.
  
  specialize (Z2Rcorrect custom_prec custom_emax custom_precGt0 custom_precLtEmax (Z.of_nat n)).
  apply rltProof2 in H0.
  rewrite H0 in Z2Rcorrect.
  decompose [and] Z2Rcorrect.
  split.
  intuition.
  intuition.
Qed.

(* Unused now. --M *)
(*
 Lemma denote_singleBoundTermsEquality : forall (expr : NowTerm) (fState : fstate),
   (*related fState (Stream.hd (traceFromState st)) ->*)
   match eval_NowTerm fState expr with
   | Some evalAsF =>
           List.Forall
             (fun term : singleBoundTerm =>
              let (premise0, pred) := denote_singleBoundTermNew fState term in
              premise0 -> match floatToReal evalAsF with 
                            | Some f => pred f
                            | None => True
                          end) (bound_term expr)

   | None => True
   end ->   
   (*related fState (Stream.hd (traceFromState st)) ->*)
   match eval_NowTerm fState expr with
   | Some evalAsF =>
     match floatToReal evalAsF with 
       | Some f => 
           List.Forall
          (denote_singleBoundTerm f fState)   (bound_term expr)
       | None => True
     end
   | None => True
   end.
   
    unfold denote_singleBoundTermNew.
    unfold denote_singleBoundTerm.
    Lemma boundTermProof : forall fState expr,  
        match eval_NowTerm fState expr with
          | Some evalAsF =>
            List.Forall
              (fun term : singleBoundTerm =>
                 (premise term fState) ->
                 match floatToReal evalAsF with
                   | Some f =>
                     ((lb term fState) <= f <=
                      (ub term fState))%R
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
                     (premise s fState) ->
                     ((lb s fState)  <= f <=
                      (ub s fState))%R) 
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

    apply boundTermProof.
    apply H.
 Qed.
 *)

(* Sub-lemmas and helper definistions used in bound_proof' *)

Lemma conjoin : forall (p1 p2:Prop), p1 -> p2 -> p1 /\ p2.
    intros.
    tlaIntuition.
Qed.

Lemma conjoin2 : forall (p1 p2 p3:Prop), p1 -> p2 -> p3 -> p1 /\ p2 /\ p3.
   intros.
   tlaIntuition.
Qed.


Lemma simplify2 : (round_mode mode_NE)  =  (Znearest (fun x : Z => negb (Zeven x))).
      simpl.
      reflexivity.
Qed.

Lemma orExtra2 : forall p1 p2 : Prop, p2 -> p1 \/ p2.
Proof.
  intros; tlaIntuition. Qed.

Lemma floatMaxBoundHelper : forall lb1 lb2 floatMax error, (lb1 + lb2 >= R0)%R -> (floatMax > 0)%R ->  (error > R0)%R -> ((0-lb1+(0-lb2))*(1+error)<floatMax)%R.
          intros. psatz R. Qed.

Lemma floatMaxBoundHelper2 : forall ub1 ub2 floatMax error, (ub1 + ub2 < R0)%R -> (floatMax > 0)%R ->  (error > R0)%R -> ((ub1 + ub2)*(1+error)<floatMax)%R.
             intros. psatz R. Qed.

Lemma absHelper: forall x y, (x>=0)%R -> (x>=y)%R -> (y<=(Rabs x))%R.
Proof.
  intros. unfold Rabs in *. destruct Rcase_abs; psatz R. Qed.

Lemma posResInf : forall lb1 lb2 x1 x2, (x1 >= lb1 -> x2 >= lb2 -> lb1 + lb2 >=0 -> x1 + x2 >= 0)%R.
Proof.
  intros. 
  psatz R. Qed.

Definition el2 (r : radix) (x : R) (lbp : ln_beta_prop r x) : 
                (x <> 0%R -> (bpow r (ln_beta_val r x lbp - 1) <= Rabs x < bpow r (ln_beta_val r x lbp)))%R := let '(Build_ln_beta_prop _ pf) := lbp in pf.

Lemma abs2: forall x0 y : R, (x0 > 0)%R -> (x0 < y)%R -> (Rabs x0 < y)%R.
Proof.
  intros. unfold Rabs. destruct Rcase_abs. 
  psatz R.
  psatz R.
Qed.

Lemma subNormal: forall x:R,  (x > R0)%R -> (x < floatMin)%R ->  (ln_beta radix2 x <= custom_emin)%Z.
Proof.
  intros.
  unfold floatMin in *.
  assert (H1 := H).
  pose proof ln_beta_le_bpow.
  apply Rgt_not_eq in H.
  specialize (H2 radix2 x custom_emin H).
  intros.
  pose proof abs2.
  specialize (H3 x (bpow radix2 custom_emin) H1 H0).
  specialize (H2 H3).
  apply H2.
Qed.

Lemma absImp : forall x, (x > 0)%R-> Rabs x = x.
Proof.
  intros. unfold Rabs. destruct Rcase_abs. psatz R. psatz R. Qed.

Lemma gt0ImpNE0 :forall x, (x>0 -> x<>0)%R.
                  intros. psatz R. Qed.

Lemma zMaxProof : forall x1 x2, (x1<=x2 -> Z.max x1 x2 = x2)%Z. 
intros. SearchAbout Z.max . pose proof Z.max_r. 
specialize (H0 x1 x2 H). apply H0.
Qed.

Lemma fexpEminGtEmax :  (3 - custom_emax - custom_prec < custom_emax)%Z.
pose proof precGe1. pose proof precLtEmax. unfold error,custom_emax, custom_prec in *. 
lia. 
Qed.

Lemma fexpEminGtEmax1 : forall ex,  (ex <= custom_emin -> (ex <= ex - custom_prec) -> ex - custom_prec < custom_emax)%Z.
intros. unfold custom_emin, custom_prec,custom_emax in *. 
pose proof precGe1. pose proof precLtEmax.
pose proof emaxGtEmin. lia.
Qed.
 Set Printing Notations.
Lemma floatMaxProofRounding : 
  forall x ex, (bpow radix2 (ex - 1) <= Rabs (x) < bpow radix2 ex)%R -> 
               (ex <= custom_emin)%Z ->
               (x < floatMin -> x > 0 ->                        
                (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) x = bpow radix2 ((FLT_exp (3 - custom_emax - custom_prec) custom_prec) ex) \/ round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) x = R0 \/ bpow radix2 (ex - 1)<= round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) x <= bpow radix2 ex) /\ Rabs (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) x) < bpow radix2 custom_emax)%R.
Proof.
  
  intros. 
  assert (gt0 := H2).                  
  apply gt0ImpNE0 in H2.
  pose proof bpow_le.
  specialize (H3 radix2 ex custom_emin H0).
  pose proof emaxGtEmin.
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
      destruct (Z_le_gt_dec (ex - custom_prec) (3 - custom_emax - custom_prec)%Z).
      {
        
        intros.
        pose proof zMaxProof as zMaxProof.
        specialize (zMaxProof (ex - custom_prec)%Z (3 - custom_emax - custom_prec)%Z l0).
        rewrite zMaxProof in *.
        
        clear zMaxProof l0 H6 Heqr. 
        pose proof errorGt0.
        unfold error in *.
        
        intros.
        pose proof fexpEminGtEmax as fexpEminGtEmax.
        pose proof bpow_lt.
        specialize (H7 radix2 (3 - custom_emax - custom_prec)%Z custom_emax fexpEminGtEmax).
        split. 
        constructor 1. apply H4.
        clear fexpEminGtEmax H H1 H6 l H2 H5.     
        pose proof bpow_gt_0.
        specialize (H radix2 (3 - custom_emax - custom_prec)%Z).
        pose proof bpow_gt_0.
        specialize (H1 radix2 custom_emax).
        unfold Rabs. destruct Rcase_abs. psatz R.   psatz R.
      }
      {
        pose proof zMaxProof as zMaxProof. 
        apply Z.gt_lt in g0.
        pose proof Z.lt_le_incl.
        
        specialize (H7 (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z g0).
        specialize (zMaxProof   (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z H7).
        rewrite Z.max_comm in zMaxProof.
        rewrite zMaxProof in *.
        
        clear zMaxProof g0 H7 H6 Heqr. 
        

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
    apply Z.gt_lt in g0.
    specialize (H4 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef) x ex g0 H).
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

Set Printing Notations.

Lemma floatMaxProof1 : forall x, 
    (x < floatMin ->
     x > 0 ->
     Rabs (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                 (round_mode mode_NE) x) < bpow radix2 custom_emax)%R.
Proof.
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
        pose proof bpow_gt_0.
        specialize (H radix2 (3 - custom_emax - custom_prec)%Z).
        pose proof bpow_gt_0.
        specialize (H1 radix2 custom_emax).
        unfold Rabs. destruct Rcase_abs. psatz R. psatz R.
      }
      {
        pose proof zMaxProof as zMaxProof. 
        apply Z.gt_lt in g0.
        pose proof Z.lt_le_incl.
        
        specialize (H7 (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z g0).
        specialize (zMaxProof   (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z H7).
        rewrite Z.max_comm in zMaxProof.
        rewrite zMaxProof in l, H4.
        
        clear zMaxProof g0 H7 H6 Heqr. 
        
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
    apply Z.gt_lt in g0.
    specialize (H4 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef) x ex g0 H1).
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

Lemma zlt_le : forall x1 x2, (x1 > x2 -> x1 >= x2)%Z.
                               intros.
                               lia.
Qed.

Lemma exCustomPrec : forall x, (x <= custom_emin ->  custom_prec >=1 -> x - custom_prec  < custom_emin)%Z. 
                                 intros. lia. 
Qed.                    

Lemma zeroLtFloatMax : forall x, (x = 0 -> Rabs x <floatMax)%R .
                                   intros.  unfold Rabs in *. destruct Rcase_abs; unfold floatMax in *;
                                                              pose proof bpow_gt_0;
                                                              specialize (H0 radix2 custom_emax);
                                                              psatz R.
Qed.                    

Lemma exHelper : forall x, (x <= custom_emin -> x - custom_prec <custom_emin)%Z. 
                             intros. unfold custom_prec, custom_emin in *.
                             pose proof precGe1.
                             lia.
Qed.

Lemma roundedValLessThanFloatMin: forall ex, ((ex <=custom_emin)%Z -> (bpow radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec ex) <= floatMin))%R.
Proof.
  intros.
  unfold FLT_exp. 
  destruct (Coqlib.zle (3 - custom_emax - custom_prec) (ex-custom_prec)).
  {
    SearchAbout Z.max.
    pose proof Z.max_l.
    specialize (H0 (ex-custom_prec)%Z (3 - custom_emax - custom_prec)%Z l).
    rewrite H0.
    unfold floatMin.
    
    specialize (exHelper ex H).
    intros.
    pose proof bpow_lt.
    specialize (H2 radix2 (ex - custom_prec)%Z custom_emin H1).
    psatz R.
  }
  {
    pose proof Z.max_r.
    SearchAbout (_>_ -> _ >= _)%Z.
    apply zlt_le in g0.
    apply Z.ge_le in g0.
    specialize (H0 (ex - custom_prec)%Z (3 - custom_emax - custom_prec)%Z g0).
    rewrite H0.
    unfold floatMin.
    unfold custom_emin,custom_prec, custom_emax in *.
    pose proof eminMinValue.
    admit.
  }
Qed.        

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
Proof.
  intros.
  remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                  (round_mode mode_NE) (x1 + x2))%R as roundedValue.
  pose proof errorGt0 as errorGt0.
  pose proof errorLessThan1 as errorLessThan1.
  clear HeqroundedValue.
  unfold error in *.
  unfold Rabs in *. destruct Rcase_abs; destruct Rcase_abs;
                    psatz R.
Qed.                           

Lemma andExtra : forall (p1 p2:Prop), p1  -> p2 ->   p1 /\ p2.
Proof.
                                                       simpl.
                                                       intros.
                                                       intuition.
Qed.       

Lemma orExtra3 : forall p1 p2 p3 p4: Prop, p1 -> p1 \/ p2 \/ p3 \/ p4.
Proof.
                                                   simpl ;intros; intuition. Qed.              

Lemma diffOR : forall (p1 p2 p3 p4 : Prop), p1 \/ p2 \/ p3 \/ p4 -> p2 \/ p1 \/ p3 \/ p4.
Proof.
                                                                        
                                                                      intuition.
Qed.                                      

Lemma orExtra3_3 : forall p1 p2 p3 p4: Prop, p3 -> p1 \/ p2 \/ p3 \/ p4.
Proof.

  intros; intuition. Qed.

Lemma floatConstValidityProof : forall f, isFloatConstValid f -> None = floatToReal f -> False.
Proof.

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

Lemma plusResultValidityProof : forall expr1 expr2 fState f, plusResultValidity expr1 expr2 fState -> (Some f = lift2 
                                                                                                           (Bplus custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                                                                                                  custom_nan mode_NE) (eval_NowTerm fState expr1)
                                                                                                           (eval_NowTerm fState expr2)) -> None = floatToReal f ->False.
Proof.
  intros.
  unfold plusResultValidity in *.
  rewrite <- H0 in H.
  revert H H1.
  apply floatConstValidityProof.
Qed.

Lemma minusResultValidityProof : forall expr1 expr2 fState f, minusResultValidity expr1 expr2 fState -> (Some f = lift2 
                                                                                                             (Bminus custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                                                                                                     custom_nan mode_NE) (eval_NowTerm fState expr1)
                                                                                                             (eval_NowTerm fState expr2)) -> None = floatToReal f ->False.
Proof.
  intros.
  unfold minusResultValidity in *.
  rewrite <- H0 in H.
  revert H H1.
  apply floatConstValidityProof.
Qed.

Lemma multResultValidityProof : forall expr1 expr2 fState f, multResultValidity expr1 expr2 fState -> (Some f = lift2 
                                                                                                           (Bmult custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                                                                                                  custom_nan mode_NE) (eval_NowTerm fState expr1)
                                                                                                           (eval_NowTerm fState expr2)) -> None = floatToReal f ->False.
Proof.
  intros.
  unfold multResultValidity in *.
  rewrite <- H0 in H.
  revert H H1.
  apply floatConstValidityProof.
Qed.       


(* The main lemma - correctness for floating-point bounds *)
Require Import ExtLib.Tactics.
Lemma bound_proof' : 
  forall (expr:NowTerm) (fState:fstate),
    boundDef' expr fState.
Proof.
  unfold boundDef'. 
  intros.
  Print eval_NowTerm.
  remember (eval_NowTerm fState (expr)). destruct o; trivial.
    eapply Forall_forall. intros.
    unfold denote_singleBoundTermNew. 
    intros. remember (floatToReal f).
    revert Heqo. revert Heqo0. revert f. revert H. revert H0. revert x. revert o.
   induction expr.
  (*remember (traceFromState st) as tr.*)
 
  {  
    simpl in *.    
    intuition.
    rewrite <- H1 in *.
    simpl in *.
    symmetry in Heqo.
    unfold fstate_lookup_force.
    rewrite Heqo.
    unfold floatToReal in Heqo0.
    red in H0.
    rewrite Heqo in H0.
    simpl in *.
    destruct o; trivial.   
    {
      destruct f; try congruence; inversion Heqo0.
      - simpl. psatz R.
      - simpl. psatz R.
    }
    {
      revert H0 Heqo0.
      apply floatConstValidityProof.
    }
  }

  {
    simpl in *.    
    intros.
    destruct H.
    {
      rewrite <- H in *.
      clear H.
      simpl in *.
      unfold lofst,lpofst in *.
      decompose [and] H0.
      clear H0.
       pose proof conjoin2 as premise.
       specialize (premise (floatMin <= INR n)%R (INR n >= 0)%R (INR n * (1 + error) < floatMax)%R H H2 H3).
       pose proof orExtra as orExtra1.
       specialize (orExtra1 ((floatMin <= INR n)%R /\
                             (INR n >= 0)%R /\ (INR n * (1 + error) < floatMax)%R) 
                            ((floatMin <=0 - INR n)%R /\
                             (INR n < 0)%R /\ ((0 - INR n) * (1 + error) < floatMax)%R) premise).
       pose proof natRoundingTruth as natRoundingTruth.
       specialize (natRoundingTruth n orExtra1).
       pose proof natRoundingTruth2 as natRoundingTruth2.
       specialize (natRoundingTruth2 f n  Heqo natRoundingTruth).
     
       pose proof conjoin as premise2.
       specialize (premise2 (floatMin <= INR n)%R (INR n >= 0)%R H H2).
       pose proof orExtra as orExtra2.
       specialize (orExtra2 ((floatMin <= INR n)%R /\ (INR n >= 0)%R) 
                            ((floatMin <= 0 - INR n)%R /\ (INR n < 0)%R) premise2).
       
       unfold floatToReal in *.
       unfold nat_to_float in *.
        destruct f eqn:f_des.
      {
        inversion Heqo0.
        inversion Heqo.
        unfold Fappli_IEEE_extra.b64_of_Z in H4.    
        rewrite <- H4 in natRoundingTruth2 at 1.
        simpl.
        unfold B2R in natRoundingTruth2.
        decompose [and] natRoundingTruth2.
        rewrite H1.
        clear natRoundingTruth2.
        clear natRoundingTruth.
        clear H3.        
        clear H1.
        pose proof relErrorTruthNat as relErrorTruthNat.
      
        specialize (relErrorTruthNat n orExtra2).
        
        intros.
        rewrite natToReal.
        remember (round radix2
                        (FLT_exp (3 - custom_emax  - custom_prec)
                                 custom_prec) (round_mode mode_NE) 
                        (INR n)) as roundedValue.
        clear HeqroundedValue.
        clear H5.
        clear premise premise2 orExtra2.
        simpl in H0.
        destruct H0.
        
        clear Heqo0 Heqo f_des orExtra1 H H4.
        unfold Rabs in *.
        
        pose proof errorGt0 as errorGt0.
        pose proof errorLessThan1 as errorLessThan1.
        unfold error in *.
        
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
          psatz R.
      }
      {
        inversion Heqo0.
        inversion Heqo.
        decompose [and] natRoundingTruth2.
        unfold is_finite in *.
        destruct (Fappli_IEEE_extra.BofZ custom_prec custom_emax custom_precGt0
           custom_precLtEmax (Z.of_nat n)) eqn:z_des.
        inversion Heqo.
        intuition.
        intuition.
        inversion Heqo.
      }
      {
        inversion Heqo0.
        inversion Heqo.
        decompose [and] natRoundingTruth2.
        unfold is_finite in *.
        destruct (Fappli_IEEE_extra.BofZ custom_prec custom_emax custom_precGt0
                                         custom_precLtEmax (Z.of_nat n)) eqn:z_des.
        inversion Heqo.
        intuition.
        intuition.
        inversion Heqo.
        
      }
      {
        inversion Heqo0.
        inversion Heqo.
        unfold Fappli_IEEE_extra.b64_of_Z in *.  
        rewrite <- H4 in natRoundingTruth2 at 1.
        unfold B2R in natRoundingTruth2.
        decompose [and] natRoundingTruth2.
        clear natRoundingTruth2.
        assert(natRoundingTruth2 := H1).
        simpl.
        rewrite natRoundingTruth2.
        clear natRoundingTruth2.
        clear natRoundingTruth.
        
        clear H1.
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
        clear Heqo0 Heqo f_des e0 orExtra1 H H0 H3 H4.
        unfold Rabs in *.
        
        pose proof errorGt0 as errorGt0.
        pose proof errorLessThan1 as errorLessThan1.
        unfold error in *.
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
          psatz R. 
      }
    }
    {
      destruct H.
      {
        rewrite <- H in *.
        clear H.
        simpl in *.
        unfold lofst,lpofst in *.
        decompose [and] H0.
        clear H0.
        pose proof conjoin2 as premise.
        specialize (premise (floatMin <= 0 - INR n)%R  (INR n < 0)%R ((0 - INR n) * (1 + error) < floatMax)%R H H2 H3).
        pose proof orExtra2 as orExtra1.
        specialize (orExtra1 ((floatMin <= INR n)%R /\
                            (INR n >= 0)%R /\ (INR n * (1 + error) < floatMax)%R) 
                           ((floatMin <= 0 - INR n)%R /\
                            (INR n < 0)%R /\ ((0 - INR n) * (1 + error) < floatMax)%R) premise).
        pose proof natRoundingTruth as natRoundingTruth.
        specialize (natRoundingTruth n orExtra1).
        pose proof natRoundingTruth2 as natRoundingTruth2.
        specialize (natRoundingTruth2 f n  Heqo natRoundingTruth).
        
        pose proof conjoin as premise2.
        specialize (premise2 (floatMin <= 0 - INR n)%R (INR n < 0)%R H H2).
        pose proof orExtra2 as orExtra2.
        specialize (orExtra2 ((floatMin <= INR n)%R /\ (INR n >= 0)%R) 
                           ((floatMin <=0 - INR n)%R /\ (INR n < 0)%R) premise2).
        
        unfold floatToReal in *.
        unfold nat_to_float in *.
        destruct f eqn:f_des.
        {
          inversion Heqo0.
          inversion Heqo.
          unfold Fappli_IEEE_extra.b64_of_Z in H4.    
          rewrite <- H4 in natRoundingTruth2 at 1.
          simpl.
          unfold B2R in natRoundingTruth2.
          decompose [and] natRoundingTruth2.
          rewrite H1.
          clear natRoundingTruth2.
          clear natRoundingTruth.
          clear H3.        
          clear H1.
          pose proof relErrorTruthNat as relErrorTruthNat.
          
          specialize (relErrorTruthNat n orExtra2).
          
          intros.
          rewrite natToReal.
          remember (round radix2
                          (FLT_exp (3 - custom_emax  - custom_prec)
                                   custom_prec) (round_mode mode_NE) 
                          (INR n)) as roundedValue.
          clear HeqroundedValue.
          clear H5.
          clear premise premise2 orExtra2.
          simpl in H0.
          destruct H0.
          
          clear Heqo0 Heqo f_des orExtra1 H H4.
          unfold Rabs in *.
          
          pose proof errorGt0 as errorGt0.
          pose proof errorLessThan1 as errorLessThan1.
          unfold error in *.
          
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
            psatz R.
        }
        {
          inversion Heqo0.
          inversion Heqo.
          decompose [and] natRoundingTruth2.
          unfold is_finite in *.
          destruct (Fappli_IEEE_extra.BofZ custom_prec custom_emax custom_precGt0
                                           custom_precLtEmax (Z.of_nat n)) eqn:z_des.
          inversion Heqo.
          intuition.
          intuition.
          inversion Heqo.
        }
        {
          inversion Heqo0.
          inversion Heqo.
          decompose [and] natRoundingTruth2.
          unfold is_finite in *.
          destruct (Fappli_IEEE_extra.BofZ custom_prec custom_emax custom_precGt0
                                           custom_precLtEmax (Z.of_nat n)) eqn:z_des.
          inversion Heqo.
          intuition.
          intuition.
          inversion Heqo.
          
        }
        {
          inversion Heqo0.
          inversion Heqo.
          unfold Fappli_IEEE_extra.b64_of_Z in *.  
          rewrite <- H4 in natRoundingTruth2 at 1.
          unfold B2R in natRoundingTruth2.
          decompose [and] natRoundingTruth2.
          clear natRoundingTruth2.
          assert(natRoundingTruth2 := H1).
          simpl.
          rewrite natRoundingTruth2.
          clear natRoundingTruth2.
          clear natRoundingTruth.
          
          clear H1.
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
          clear Heqo0 Heqo f_des e0 orExtra1 H H0 H3 H4.
          unfold Rabs in *.
          
          pose proof errorGt0 as errorGt0.
          pose proof errorLessThan1 as errorLessThan1.
          unfold error in *.
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
            psatz R. 
        }
      }
      {
        intuition.
      }
    }
  }
 
  { simpl in *. 
    intros.
    destruct H.
    {
      rewrite <- H in *.
      clear H.
      simpl in *.
      inversion Heqo.
      unfold floatToReal in *.
      unfold isFloatConstValid in *.
      destruct f.
      {
        simpl in *. 
        rewrite H1 in *.
        inversion Heqo0.
        simpl in *.
        intuition.
      }
      {
        inversion Heqo0.       
        subst.
        intuition.
      }
      {
        inversion Heqo0.
        subst. 
        intuition.
      }
      {
        inversion Heqo0.
        subst.
        intuition.
      }
    }
    {
      intuition.
    }
  }
  { 
    
    simpl in *.
    intros.
   
   
    eapply In_cross_In in H.
    simpl in H.
    forward_reason.
    destruct H2.
    {
      unfold simpleBound in *.
      rewrite <- H2 in *.
      clear H2.
      simpl in *.
      destruct H0.
      destruct H2.
      destruct H3.
      destruct H4.
      destruct H5.
      destruct H6.
      destruct H6.
      destruct H7.
      inversion Heqo.
      
      forward_reason.
      assert (floatToReal x2 = floatToReal x2).
      intuition.
      assert (floatToReal x3 = floatToReal x3).
      intuition.
      specialize (IHexpr1 (floatToReal x2) _ H0 H x2 H11 H6).
      specialize (IHexpr2 (floatToReal x3) _ H2 H1 x3 H12 H7).
      inversion H10.
      inversion H8.
      rewrite <- H13 in *.
      rewrite <- H14 in *.
      assert (floatToRealProof1 := H13).
      assert (floatToRealProof2 := H14).
      rewrite <- H6 in *.
      rewrite <- H7 in *.
      assert (validFloatArg1 := H10).
      assert (validFloatArg2 := H8).
      clear H11 H12 H6 H8 H0 H2 H H1 H9 H10 H13 H14 H7.
      
      unfold float_plus in *.
      destruct f eqn:f_des.
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H7).
        assert (expr1Bound := H0).
        assert (expr2Bound := H6).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe0 := H5).
        assert (plusResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthPlus x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        
        intros.
        assert (floatMinCase1 := floatMinCase).
        clear floatMinCase.
        pose proof orExtra as floatMinCase. 
        specialize (floatMinCase (floatMin <= lb1 + lb2)%R  (floatMin <= 0 - ub1 + (0 - ub2))%R floatMinCase1).
        clear floatMinCase1.
        specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H0 H2 H1 H3).
        pose proof plusRoundingTruth as plusRoundingTruth. 
        
        pose proof floatMaxBoundHelper as floatMaxBound2.
        specialize (floatMaxBound2 lb1 lb2 floatMax error resultGe0 floatMaxGt0 errorGt0).
        specialize (plusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 floatMinCase H0 H2 floatMaxBound1 floatMaxBound2 H1 H3).
        pose proof plusRoundingTruth2 as plusRoundingTruth2.
        specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 plusRoundingTruth).
        revert plusResultStmt. intros plusResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
        
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 +
                          B2R custom_prec custom_emax x3)) as roundedValue. 
        simpl in plusRoundingTruth2.
        simpl in plusResultStmt.
        rewrite <- plusResultStmt in plusRoundingTruth2.
        simpl in plusRoundingTruth2.
        decompose [and] plusRoundingTruth2.
        rewrite  H5.
        clear H6.

        clear plusRoundingTruth2.
        assert (plusRoundingTruth2:= H5).
        clear H5.
        clear plusResultStmt.
        clear H4.
        clear plusRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
        rewrite <- floatToRealProof2  in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.

        pose proof errorGt0.
        clear floatMinCase floatMaxBound1 floatMaxBound2 HeqroundedValue 
              plusRoundingTruth2  floatToRealProof1 floatToRealProof2  expr1 expr2 fState b o f_des Heqo0 H Heqlb1 Heqlb2 Hequb1 Hequb2 x0 x1 x b Heqo.
        
        unfold error in *.
        unfold Rabs in *.
        
        pose proof errorLessThan1 as errorLessThan1.
        unfold error in *.
        split.
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
        intuition.
      }
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H7).
        assert (expr1Bound := H0).
        assert (expr2Bound := H6).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe0 := H5).
        assert (plusResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthPlus x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        
        intros.
        assert (floatMinCase1 := floatMinCase).
        clear floatMinCase.
        pose proof orExtra as floatMinCase. 
        specialize (floatMinCase (floatMin <= lb1 + lb2)%R  (floatMin <= 0 - ub1 + (0 - ub2))%R floatMinCase1).
        clear floatMinCase1.
        specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H0 H2 H1 H3).
        pose proof plusRoundingTruth as plusRoundingTruth. 
        
        pose proof floatMaxBoundHelper as floatMaxBound2.
        specialize (floatMaxBound2 lb1 lb2 floatMax error resultGe0 floatMaxGt0 errorGt0).
        specialize (plusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 floatMinCase H0 H2 floatMaxBound1 floatMaxBound2 H1 H3).
        pose proof plusRoundingTruth2 as plusRoundingTruth2.
        specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 plusRoundingTruth).
        revert plusResultStmt. intros plusResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
        
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 +
                          B2R custom_prec custom_emax x3)) as roundedValue. 
        simpl in plusRoundingTruth2.
        simpl in plusResultStmt.
        rewrite <- plusResultStmt in plusRoundingTruth2.
        simpl in plusRoundingTruth2.
        decompose [and] plusRoundingTruth2.
        intuition.
      }
      {
         inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H7).
        assert (expr1Bound := H0).
        assert (expr2Bound := H6).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe0 := H5).
        assert (plusResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthPlus x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        
        intros.
        assert (floatMinCase1 := floatMinCase).
        clear floatMinCase.
        pose proof orExtra as floatMinCase. 
        specialize (floatMinCase (floatMin <= lb1 + lb2)%R  (floatMin <= 0 - ub1 + (0 - ub2))%R floatMinCase1).
        clear floatMinCase1.
        specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H0 H2 H1 H3).
        pose proof plusRoundingTruth as plusRoundingTruth. 
        
        pose proof floatMaxBoundHelper as floatMaxBound2.
        specialize (floatMaxBound2 lb1 lb2 floatMax error resultGe0 floatMaxGt0 errorGt0).
        specialize (plusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 floatMinCase H0 H2 floatMaxBound1 floatMaxBound2 H1 H3).
        pose proof plusRoundingTruth2 as plusRoundingTruth2.
        specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 plusRoundingTruth).
        revert plusResultStmt. intros plusResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
        
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 +
                          B2R custom_prec custom_emax x3)) as roundedValue. 
        simpl in plusRoundingTruth2.
        simpl in plusResultStmt.
        rewrite <- plusResultStmt in plusRoundingTruth2.
        simpl in plusRoundingTruth2.
        decompose [and] plusRoundingTruth2.
        intuition.
      }
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H7).
        assert (expr1Bound := H0).
        assert (expr2Bound := H6).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe0 := H5).
        assert (plusResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthPlus x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        
        intros.
        assert (floatMinCase1 := floatMinCase).
        clear floatMinCase.
        pose proof orExtra as floatMinCase. 
        specialize (floatMinCase (floatMin <= lb1 + lb2)%R  (floatMin <= 0 - ub1 + (0 - ub2))%R floatMinCase1).
        clear floatMinCase1.
        specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H0 H2 H1 H3).
        pose proof plusRoundingTruth as plusRoundingTruth. 
        
        pose proof floatMaxBoundHelper as floatMaxBound2.
        specialize (floatMaxBound2 lb1 lb2 floatMax error resultGe0 floatMaxGt0 errorGt0).
        specialize (plusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 floatMinCase H0 H2 floatMaxBound1 floatMaxBound2 H1 H3).
        pose proof plusRoundingTruth2 as plusRoundingTruth2.
        specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 plusRoundingTruth).
        revert plusResultStmt. intros plusResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
        
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 +
                          B2R custom_prec custom_emax x3)) as roundedValue. 
        simpl in plusRoundingTruth2.
        simpl in plusResultStmt.
        rewrite <- plusResultStmt in plusRoundingTruth2.
        simpl in plusRoundingTruth2.
        decompose [and] plusRoundingTruth2.
        rewrite  H5.
        clear H6.

        clear plusRoundingTruth2.
        assert (plusRoundingTruth2:= H5).
        clear H5.
        clear plusResultStmt.
        clear H4.
        clear plusRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
        rewrite <- floatToRealProof2  in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.

        pose proof errorGt0.
        clear floatMinCase floatMaxBound1 floatMaxBound2 HeqroundedValue 
              plusRoundingTruth2  floatToRealProof1 floatToRealProof2  expr1 expr2 fState b o f_des Heqo0 H Heqlb1 Heqlb2 Hequb1 Hequb2 x0 x1 x b Heqo.
        
        unfold error in *.
        unfold Rabs in *.
        
        pose proof errorLessThan1 as errorLessThan1.
        unfold error in *.
        split.
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
        intuition.
      }
    }   
    {
      destruct H2. 
      {
        unfold simpleBound in *.
        rewrite <- H2 in *.
        clear H2.
        simpl in *.
        destruct H0.
        destruct H2.
        destruct H3.
        destruct H4.
        destruct H5.
        destruct H6.
        destruct H6.
        destruct H7.
        inversion Heqo.
        
        forward_reason.
        assert (floatToReal x2 = floatToReal x2).
        intuition.
        assert (floatToReal x3 = floatToReal x3).
        intuition.
        specialize (IHexpr1 (floatToReal x2) _ H0 H x2 H11 H6).
        specialize (IHexpr2 (floatToReal x3) _ H2 H1 x3 H12 H7).
        inversion H10.
        inversion H8.
        rewrite <- H13 in *.
        rewrite <- H14 in *.
        assert (floatToRealProof1 := H13).
        assert (floatToRealProof2 := H14).
        rewrite <- H6 in *.
        rewrite <- H7 in *.
        assert (validFloatArg1 := H10).
        assert (validFloatArg2 := H8).
        clear H11 H12 H6 H8 H0 H2 H H1 H9 H10 H13 H14 H7.
        
        unfold float_plus in *.
        destruct f eqn:f_des.
        {
          inversion Heqo0.
          simpl in *.
          inversion Heqo.
          unfold lofst in *.
          destruct IHexpr1.
          destruct IHexpr2.
          assert (expr1Valid := H2).
          assert (expr2Valid := H7).
          assert (expr1Bound := H0).
          assert (expr2Bound := H6).
          assert (floatMinCase := H3).
          assert (floatMaxBound1 := H4). 
          assert (resultGe0 := H5).
          assert (plusResultStmt := H1).
          clear H2 H7 H0 H6 H3 H4 H5 H1.
          pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
          remember (lb x0 fState) as lb1.
          remember (lb x1 fState) as lb2.
          remember (ub x0 fState) as ub1.
          remember (ub x1 fState) as ub2.
          specialize (relErrorBasedOnFloatMinTruthPlus x4 x5 lb1 lb2 ub1 ub2 ).
          
          destruct expr1Bound.
          destruct expr2Bound.
          pose proof or_introl.
          
          intros.
          assert (floatMinCase1 := floatMinCase).
          clear floatMinCase.
          pose proof orExtra2 as floatMinCase. 
          specialize (floatMinCase (floatMin <= lb1 + lb2)%R  (floatMin <= 0 - ub1 + (0 - ub2))%R floatMinCase1).
          clear floatMinCase1.
          specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H0 H2 H1 H3).
          pose proof plusRoundingTruth as plusRoundingTruth. 
          
          pose proof floatMaxBoundHelper2 as floatMaxBound2.
          specialize (floatMaxBound2 ub1 ub2 floatMax error resultGe0 floatMaxGt0 errorGt0).
          specialize (plusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 floatMinCase H0 H2 floatMaxBound2 floatMaxBound1 H1 H3).
          pose proof plusRoundingTruth2 as plusRoundingTruth2.
          specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 plusRoundingTruth).
          revert plusResultStmt. intros plusResultStmt.
          apply validFloat2 in floatToRealProof1.
          apply validFloat2 in floatToRealProof2.
          rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
          rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
          
          remember ( round radix2
                           (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                           (round_mode mode_NE)
                           (B2R custom_prec custom_emax x2 +
                            B2R custom_prec custom_emax x3)) as roundedValue. 
          simpl in plusRoundingTruth2.
          simpl in plusResultStmt.
          rewrite <- plusResultStmt in plusRoundingTruth2.
          simpl in plusRoundingTruth2.
          decompose [and] plusRoundingTruth2.
          rewrite  H5.
          clear H6.

          clear plusRoundingTruth2.
          assert (plusRoundingTruth2:= H5).
          clear H5.
          clear plusResultStmt.
          clear H4.
          clear plusRoundingTruth.
          rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
          rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
          rewrite <- floatToRealProof2  in HeqroundedValue.
          rewrite <- floatToRealProof1 in HeqroundedValue.

          pose proof errorGt0.
          clear floatMinCase floatMaxBound1 floatMaxBound2 HeqroundedValue 
                plusRoundingTruth2  floatToRealProof1 floatToRealProof2  expr1 expr2 fState b o f_des Heqo0 H Heqlb1 Heqlb2 Hequb1 Hequb2 x0 x1 x b Heqo.
          
          unfold error in *.
          unfold Rabs in *.
          
          pose proof errorLessThan1 as errorLessThan1.
          unfold error in *.
          split.
          destruct Rcase_abs;destruct Rcase_abs;psatz R.
          intuition.
        }
        {
          inversion Heqo0.
          simpl in *.
          inversion Heqo.
          unfold lofst in *.
          destruct IHexpr1.
          destruct IHexpr2.
          assert (expr1Valid := H2).
          assert (expr2Valid := H7).
          assert (expr1Bound := H0).
          assert (expr2Bound := H6).
          assert (floatMinCase := H3).
          assert (floatMaxBound1 := H4). 
          assert (resultGe0 := H5).
          assert (plusResultStmt := H1).
          clear H2 H7 H0 H6 H3 H4 H5 H1.
          pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
          remember (lb x0 fState) as lb1.
          remember (lb x1 fState) as lb2.
          remember (ub x0 fState) as ub1.
          remember (ub x1 fState) as ub2.
          specialize (relErrorBasedOnFloatMinTruthPlus x4 x5 lb1 lb2 ub1 ub2 ).
          
          destruct expr1Bound.
          destruct expr2Bound.
          pose proof or_introl.
          
          intros.
          assert (floatMinCase1 := floatMinCase).
          clear floatMinCase.
          pose proof orExtra2 as floatMinCase. 
          specialize (floatMinCase (floatMin <= lb1 + lb2)%R  (floatMin <= 0 - ub1 + (0 - ub2))%R floatMinCase1).
          clear floatMinCase1.
          specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H0 H2 H1 H3).
          pose proof plusRoundingTruth as plusRoundingTruth. 
          
          pose proof floatMaxBoundHelper2 as floatMaxBound2.
          specialize (floatMaxBound2 ub1 ub2 floatMax error resultGe0 floatMaxGt0 errorGt0).
          specialize (plusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 floatMinCase H0 H2 floatMaxBound2 floatMaxBound1 H1 H3).
          pose proof plusRoundingTruth2 as plusRoundingTruth2.
          specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 plusRoundingTruth).
          revert plusResultStmt. intros plusResultStmt.
          apply validFloat2 in floatToRealProof1.
          apply validFloat2 in floatToRealProof2.
          rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
          rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
          
          remember ( round radix2
                           (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                           (round_mode mode_NE)
                           (B2R custom_prec custom_emax x2 +
                            B2R custom_prec custom_emax x3)) as roundedValue. 
          simpl in plusRoundingTruth2.
          simpl in plusResultStmt.
          rewrite <- plusResultStmt in plusRoundingTruth2.
          simpl in plusRoundingTruth2.
          decompose [and] plusRoundingTruth2.
          intuition.
        }
        {
          inversion Heqo0.
          simpl in *.
          inversion Heqo.
          unfold lofst in *.
          destruct IHexpr1.
          destruct IHexpr2.
          assert (expr1Valid := H2).
          assert (expr2Valid := H7).
          assert (expr1Bound := H0).
          assert (expr2Bound := H6).
          assert (floatMinCase := H3).
          assert (floatMaxBound1 := H4). 
          assert (resultGe0 := H5).
          assert (plusResultStmt := H1).
          clear H2 H7 H0 H6 H3 H4 H5 H1.
          pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
          remember (lb x0 fState) as lb1.
          remember (lb x1 fState) as lb2.
          remember (ub x0 fState) as ub1.
          remember (ub x1 fState) as ub2.
          specialize (relErrorBasedOnFloatMinTruthPlus x4 x5 lb1 lb2 ub1 ub2 ).
          
          destruct expr1Bound.
          destruct expr2Bound.
          pose proof or_introl.
          
          intros.
          assert (floatMinCase1 := floatMinCase).
          clear floatMinCase.
          pose proof orExtra2 as floatMinCase. 
          specialize (floatMinCase (floatMin <= lb1 + lb2)%R  (floatMin <= 0 - ub1 + (0 - ub2))%R floatMinCase1).
          clear floatMinCase1.
          specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H0 H2 H1 H3).
          pose proof plusRoundingTruth as plusRoundingTruth. 
          
          pose proof floatMaxBoundHelper2 as floatMaxBound2.
          specialize (floatMaxBound2 ub1 ub2 floatMax error resultGe0 floatMaxGt0 errorGt0).
          specialize (plusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 floatMinCase H0 H2 floatMaxBound2 floatMaxBound1 H1 H3).
          pose proof plusRoundingTruth2 as plusRoundingTruth2.
          specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 plusRoundingTruth).
          revert plusResultStmt. intros plusResultStmt.
          apply validFloat2 in floatToRealProof1.
          apply validFloat2 in floatToRealProof2.
          rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
          rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
          
          remember ( round radix2
                           (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                           (round_mode mode_NE)
                           (B2R custom_prec custom_emax x2 +
                            B2R custom_prec custom_emax x3)) as roundedValue. 
          simpl in plusRoundingTruth2.
          simpl in plusResultStmt.
          rewrite <- plusResultStmt in plusRoundingTruth2.
          simpl in plusRoundingTruth2.
          decompose [and] plusRoundingTruth2.
          intuition.
        }
        {
          inversion Heqo0.
          simpl in *.
          inversion Heqo.
          unfold lofst in *.
          destruct IHexpr1.
          destruct IHexpr2.
          assert (expr1Valid := H2).
          assert (expr2Valid := H7).
          assert (expr1Bound := H0).
          assert (expr2Bound := H6).
          assert (floatMinCase := H3).
          assert (floatMaxBound1 := H4). 
          assert (resultGe0 := H5).
          assert (plusResultStmt := H1).
          clear H2 H7 H0 H6 H3 H4 H5 H1.
          pose proof relErrorBasedOnFloatMinTruthPlus as relErrorBasedOnFloatMinTruthPlus.
          remember (lb x0 fState) as lb1.
          remember (lb x1 fState) as lb2.
          remember (ub x0 fState) as ub1.
          remember (ub x1 fState) as ub2.
          specialize (relErrorBasedOnFloatMinTruthPlus x4 x5 lb1 lb2 ub1 ub2 ).
          
          destruct expr1Bound.
          destruct expr2Bound.
          pose proof or_introl.
          
          intros.
          assert (floatMinCase1 := floatMinCase).
          clear floatMinCase.
          pose proof orExtra2 as floatMinCase. 
          specialize (floatMinCase (floatMin <= lb1 + lb2)%R (floatMin <= 0 - ub1 + (0 - ub2))%R    floatMinCase1).
          clear floatMinCase1.
          specialize (relErrorBasedOnFloatMinTruthPlus floatMinCase H0 H2 H1 H3).
          pose proof plusRoundingTruth as plusRoundingTruth. 
          
          pose proof floatMaxBoundHelper2 as floatMaxBound2.
          specialize (floatMaxBound2 ub1 ub2 floatMax error resultGe0 floatMaxGt0 errorGt0).
          specialize (plusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 floatMinCase H0 H2 floatMaxBound2 floatMaxBound1 H1 H3).
          pose proof plusRoundingTruth2 as plusRoundingTruth2.
          specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 plusRoundingTruth).
          revert plusResultStmt. intros plusResultStmt.
          apply validFloat2 in floatToRealProof1.
          apply validFloat2 in floatToRealProof2.
          rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
          rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
          
          remember ( round radix2
                           (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                           (round_mode mode_NE)
                           (B2R custom_prec custom_emax x2 +
                            B2R custom_prec custom_emax x3)) as roundedValue. 
          simpl in plusRoundingTruth2.
          simpl in plusResultStmt.
          rewrite <- plusResultStmt in plusRoundingTruth2.
          simpl in plusRoundingTruth2.
          decompose [and] plusRoundingTruth2.
          rewrite  H5.
          clear H6.

          clear plusRoundingTruth2.
          assert (plusRoundingTruth2:= H5).
          clear H5.
          clear plusResultStmt.
          clear H4.
          clear plusRoundingTruth.
          rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthPlus.
          rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthPlus.
          rewrite <- floatToRealProof2  in HeqroundedValue.
          rewrite <- floatToRealProof1 in HeqroundedValue.

          pose proof errorGt0.
          clear floatMinCase floatMaxBound1 floatMaxBound2 HeqroundedValue 
                plusRoundingTruth2  floatToRealProof1 floatToRealProof2  expr1 expr2 fState b o f_des Heqo0 H Heqlb1 Heqlb2 Hequb1 Hequb2 x0 x1 x b Heqo.
          
          unfold error in *.
          unfold Rabs in *.
          
          pose proof errorLessThan1 as errorLessThan1.
          unfold error in *.
          split.
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
          intuition.
        }
      }      
      {
        destruct H2.
        {
          unfold simpleBound in *.
          rewrite <- H2 in *.
          clear H2.
          simpl in *.
          destruct H0.
          destruct H2.
          destruct H3.
          destruct H4.
          destruct H5.
          destruct H6.
          destruct H7.
          destruct H7.
          destruct H8.
          
          
          forward_reason.
          assert (floatToReal x2 = floatToReal x2).
          intuition.
          assert (floatToReal x3 = floatToReal x3).
          intuition.
          specialize (IHexpr1 (floatToReal x2) _ H0 H x2 H11 H7).
          specialize (IHexpr2 (floatToReal x3) _ H2 H1 x3 H12 H8).
          clear H11. clear H12.
          inversion H10.
          inversion H9.
          rewrite <- H11 in *.
          rewrite <- H12 in *.
          assert (floatToRealProof1 := H11).
          assert (floatToRealProof2 := H12).
          rewrite <- H7 in *.
          rewrite <- H8 in *.
          inversion Heqo.
          unfold float_plus.
          assert (validFloatArg1 := H11).
          assert (validFloatArg2 := H9).
          unfold lofst in *.
          assert (floatMinCase1 := H3).
          assert (floatMinCase2 := H4).
          assert (floatMaxBound1 := H5).
          assert (resultGe0 := H6).
          inversion Heqo.
          clear Heqo.
          assert (plusResultStmt := H15).  
          clear H11 H12 H6 H8 H0 H2 H H1 H9 H10 H14 H7 H3 H4 H5 H15.
          destruct IHexpr1.
          destruct IHexpr2.
          assert (validArg1 := H0).
          assert (validArg2 := H2).
          assert (expr1Bound := H).
          assert (expr2Bound := H1).
          clear H H1 H0 H2.
          unfold float_plus in *.          
          destruct f eqn:f_des.
          {
            simpl in *.
            remember (lb x0 fState) as lb1.
            remember (lb x1 fState) as lb2.
            remember (ub x1 fState) as ub2.
            remember (ub x0 fState) as ub1.
            clear Hequb1 Hequb2 Heqlb1 Heqlb2.
            clear x0 x1 x.
            destruct (Rge_dec (x4+x5)%R floatMin).
            {
              assert (floatMinCase3 := r).
              clear r.
              (* relative_error*)
              pose proof relative_error as relative_error.
              specialize (relative_error radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) validFexpProof (custom_emin)%Z custom_prec precThm (round_mode mode_NE) (valid_rnd_N choiceDef) (x4 + x5)%R).

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
              apply Rle_ge in x1lb.
              apply Rle_ge in x2lb.
              SearchAbout (_ > 0 -> _ >= 0)%R.
              specialize (posResInf lb1 lb2 x4 x5 x1lb x2lb resultGe0).
              specialize (absProof (x4+x5)%R floatMin posResInf floatMinCase3).
              specialize (relative_error absProof).
              (* relative_error *)
              pose proof plusRoundingTruth3 as plusRoundingTruth3.
              specialize (plusRoundingTruth3 x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 ).
              pose proof orExtra as floatMinPremise.
              specialize (floatMinPremise (x4 + x5 >= floatMin)%R (x4 + x5 <= 0 - floatMin)%R floatMinCase3).
              apply Rge_le in x1lb.
              apply Rge_le in x2lb.
              specialize (plusRoundingTruth3 floatMinPremise x1lb x2lb floatMaxBound1).
              pose proof floatMaxBoundHelper as floatMaxBound2.
              specialize (floatMaxBound2 lb1 lb2 floatMax error resultGe0 floatMaxGt0 errorGt0).
              specialize (plusRoundingTruth3 floatMaxBound2 x1ub x2ub).
              pose proof plusRoundingTruth2 as plusRoundingTruth2.
              specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2
                         plusRoundingTruth3).
              rewrite <- plusResultStmt in plusRoundingTruth2.
              remember (  B2R custom_prec custom_emax
                         (B754_zero custom_prec custom_emax b)).


              simpl in Heqr.
              rewrite Heqr in plusRoundingTruth2.
              destruct plusRoundingTruth2.
              clear r Heqr.
              assert (bplusCorrectStmt := H).
              assert (resultFiniteTruth := H0).
              clear H H0.
              clear bplusCorrectStmt resultFiniteTruth plusRoundingTruth3 absProof floatMinPremise floatMinCase1 floatMinCase2 floatMinCase3 floatMaxBound1 floatMaxBound2.
              apply validFloat2 in floatToRealProof1.
              apply validFloat2 in floatToRealProof2.
              pose proof errorGt0.
              rewrite <- plusResultStmt in *.
              inversion Heqo0.
              split.
              psatz R.
              unfold isFloatConstValid in *.
              intuition.
            }
            {
               apply Rnot_ge_lt in n.
              
              generalize (el2 radix2 (x4+x5)%R (ln_beta radix2 (x4+x5))).
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
              specialize (posResInf lb1 lb2 x4 x5 x1lb x2lb resultGe0).
              apply Rge_le in posResInf.
              destruct (Rle_lt_or_eq_dec 0 (x4+x5)%R).
              {
                apply posResInf.
              }
              {
                pose proof subNormal as subNormalProof. 
                apply Rlt_gt in r.
                specialize (subNormalProof (x4+x5)%R r n).
                remember (ln_beta radix2 (x4 + x5)) as ex.
                
                pose proof gt0ImpNE0 as gt0ImpNE0.
                specialize (gt0ImpNE0 (x4+x5)%R r).
                specialize (ln_beta_premise gt0ImpNE0).
                pose proof bpow_le as bpow_le.
                specialize (bpow_le radix2 ex custom_emin subNormalProof).
                pose proof plusRoundingTruth2.
  
                intros.
                pose proof floatMaxProofRounding.
                specialize (H0 (x4 +x5)%R ex ln_beta_premise subNormalProof n r).
                assert (floatToRealRelationForExpr1 := floatToRealProof1).
                assert (floatToRealRelationForExpr2 := floatToRealProof2).
                apply validFloat2 in floatToRealProof1.
                apply validFloat2 in floatToRealProof2.
                
                specialize (H x2 x3 x4 x5 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                rewrite <- floatToRealProof1 in H.
                rewrite <- floatToRealProof2 in H.
                destruct H0.
                specialize (H H1).
                destruct H.
                rewrite <- plusResultStmt in H.
                unfold B2R in H.
                remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                (round_mode mode_NE) (x4 + x5)) as roundedValue.
                destruct H0.
                {
                  unfold FLT_exp in H0.
                  destruct (Z_le_gt_dec (ex - custom_prec) (3 - custom_emax - custom_prec)%Z).
                  {
                    pose proof zMaxProof as zMaxProof.
                    specialize (zMaxProof (ex - custom_prec)%Z (3 - custom_emax - custom_prec)%Z l).
                    rewrite zMaxProof in *.
                    clear zMaxProof.  
                    Print customEminMinValue.
                    pose proof customEminMinValue as customEminMinValue.
                    
                    apply Z.ge_le in customEminMinValue.
                    pose proof compcert.flocq.Core.Fcore_Raux.bpow_le.
                    specialize (H3 radix2 (3 - custom_emax - custom_prec)%Z custom_emin customEminMinValue).
                    unfold floatMin in *.
                    unfold error, custom_emin,custom_emax, custom_prec in *.
                    pose proof bpow_gt_0 as bpowGt0_1.
                    specialize (bpowGt0_1 radix2 (- prec + 1)%Z)%R.
                    clear H H2 H1 l customEminMinValue ln_beta_premise floatToRealProof1 floatToRealProof2 absImp posResInf.
                    unfold lofst in *.
                    inversion Heqo0.
                    split.
                    split.
                    pose proof bpow_gt_0 as bpow_gt_0_2.
                    specialize (bpow_gt_0_2 radix2 (3-emax-prec)%Z).
                   
                    psatz R.
                    psatz R.
                    rewrite <- plusResultStmt.
                    unfold isFloatConstValid.
                    intuition.
                  }
                  {
                    assert (g:=g0).
                    clear g0.
                    pose proof zMaxProof as zMaxProof.
                    
                    intros.
                    apply zlt_le in g.
                    apply Z.ge_le in g.
                    specialize (zMaxProof (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z g).
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
                    unfold lofst in *.
                    inversion Heqo0.
                    split.
                    psatz R.
                    rewrite <- plusResultStmt.
                    unfold isFloatConstValid.
                    intuition.
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
                    unfold lofst in *.
                    inversion Heqo0.
                    split.
                    psatz R.
                    rewrite <- plusResultStmt.
                    unfold isFloatConstValid.
                    intuition.
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
                    unfold lofst in *.
                    inversion Heqo0.
                    split.
                    psatz R.
                    rewrite <- plusResultStmt.
                    unfold isFloatConstValid.
                    intuition.
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
                assert (floatToRealRelationForExpr1 := floatToRealProof1).
                assert (floatToRealRelationForExpr2 := floatToRealProof2).
                apply validFloat2 in floatToRealProof1.
                apply validFloat2 in floatToRealProof2.
                unfold floatMax in *.
                specialize (H x2 x3 x4 x5 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                rewrite <- floatToRealProof1 in H.
                rewrite <- floatToRealProof2 in H.
                unfold floatMin in *.
                pose proof bpow_gt_0.
                specialize (H1 radix2 custom_emin).
                pose proof errorGt0.
                unfold lofst in *.
                inversion Heqo0.
                split.
                psatz R.
                rewrite <- plusResultStmt.
                unfold isFloatConstValid.
                intuition.
              }
            }
          }
          {
            remember (lb x0 fState) as lb1.
            remember (lb x1 fState) as lb2.
            remember (ub x1 fState) as ub2.
            remember (ub x0 fState) as ub1.
            clear Hequb1 Hequb2 Heqlb1 Heqlb2.
            clear x0 x1 x.
            destruct (Rge_dec (x4+x5)%R floatMin).
            {
              assert (floatMinCase3 := r).
              clear r.
              (* relative_error*)
              pose proof relative_error as relative_error.
              specialize (relative_error radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) validFexpProof (custom_emin)%Z custom_prec precThm (round_mode mode_NE) (valid_rnd_N choiceDef) (x4 + x5)%R).

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
              apply Rle_ge in x1lb.
              apply Rle_ge in x2lb.
              SearchAbout (_ > 0 -> _ >= 0)%R.
              specialize (posResInf lb1 lb2 x4 x5 x1lb x2lb resultGe0).
              specialize (absProof (x4+x5)%R floatMin posResInf floatMinCase3).
              specialize (relative_error absProof).
              (* relative_error *)
              pose proof plusRoundingTruth3 as plusRoundingTruth3.
              specialize (plusRoundingTruth3 x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 ).
              pose proof orExtra as floatMinPremise.
              specialize (floatMinPremise (x4 + x5 >= floatMin)%R (x4 + x5 <= 0 - floatMin)%R floatMinCase3).
              apply Rge_le in x1lb.
              apply Rge_le in x2lb.
              specialize (plusRoundingTruth3 floatMinPremise x1lb x2lb floatMaxBound1).
              pose proof floatMaxBoundHelper as floatMaxBound2.
              specialize (floatMaxBound2 lb1 lb2 floatMax error resultGe0 floatMaxGt0 errorGt0).
              specialize (plusRoundingTruth3 floatMaxBound2 x1ub x2ub).
              pose proof plusRoundingTruth2 as plusRoundingTruth2.
              specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2
                                             plusRoundingTruth3).
              decompose [and] plusRoundingTruth2.
              inversion Heqo0.
              rewrite <- plusResultStmt in H0.
              inversion H0.
            }
            {
              apply Rnot_ge_lt in n.
              
              generalize (el2 radix2 (x4+x5)%R (ln_beta radix2 (x4+x5))).
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
              specialize (posResInf lb1 lb2 x4 x5 x1lb x2lb resultGe0).
              apply Rge_le in posResInf.
              destruct (Rle_lt_or_eq_dec 0 (x4+x5)%R).
              {
                apply posResInf.
              }
              {
                pose proof subNormal as subNormalProof. 
                apply Rlt_gt in r.
                specialize (subNormalProof (x4+x5)%R r n).
                remember (ln_beta radix2 (x4 + x5)) as ex.
                
                pose proof gt0ImpNE0 as gt0ImpNE0.
                specialize (gt0ImpNE0 (x4+x5)%R r).
                specialize (ln_beta_premise gt0ImpNE0).
                pose proof bpow_le as bpow_le.
                specialize (bpow_le radix2 ex custom_emin subNormalProof).
                pose proof plusRoundingTruth2.
                intros.
                pose proof floatMaxProofRounding.
                specialize (H0 (x4 +x5)%R ex ln_beta_premise subNormalProof n r).
                assert (floatToRealRelationForExpr1 := floatToRealProof1).
                assert (floatToRealRelationForExpr2 := floatToRealProof2).
                apply validFloat2 in floatToRealProof1.
                apply validFloat2 in floatToRealProof2.
                
                specialize (H x2 x3 x4 x5 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                rewrite <- floatToRealProof1 in H.
                rewrite <- floatToRealProof2 in H.
                destruct H0.
                specialize (H H1).
                decompose [and] H.
                inversion Heqo0.
                rewrite <- plusResultStmt in *.
                simpl in *.
                intuition.
              }      
              {
                pose proof plusRoundingTruth2.
                pose proof round_0 as round_0.
                specialize (round_0 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef)).
                
                pose proof zeroLtFloatMax.
                specialize (H0 (round radix2
                                      (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                      (round_mode mode_NE) 0) round_0).
                assert (floatToRealRelationForExpr1 := floatToRealProof1).
                assert (floatToRealRelationForExpr2 := floatToRealProof2).
                apply validFloat2 in floatToRealProof1.
                apply validFloat2 in floatToRealProof2.
                unfold floatMax in *.
                specialize (H x2 x3 x4 x5 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                rewrite <- floatToRealProof1 in H.
                rewrite <- floatToRealProof2 in H.
                rewrite e in *.
                specialize (H H0).
                decompose [and] H.
                inversion Heqo0.
                simpl in *.
                unfold is_finite in *.
                rewrite <- plusResultStmt in *.
                intuition.
              }
            }
          }
          {
            
            remember (lb x0 fState) as lb1.
            remember (lb x1 fState) as lb2.
            remember (ub x1 fState) as ub2.
            remember (ub x0 fState) as ub1.
            clear Hequb1 Hequb2 Heqlb1 Heqlb2.
            clear x0 x1 x.
            destruct (Rge_dec (x4+x5)%R floatMin).
            {
              assert (floatMinCase3 := r).
              clear r.
              (* relative_error*)
              pose proof relative_error as relative_error.
              specialize (relative_error radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) validFexpProof (custom_emin)%Z custom_prec precThm (round_mode mode_NE) (valid_rnd_N choiceDef) (x4 + x5)%R).

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
              apply Rle_ge in x1lb.
              apply Rle_ge in x2lb.
              SearchAbout (_ > 0 -> _ >= 0)%R.
              specialize (posResInf lb1 lb2 x4 x5 x1lb x2lb resultGe0).
              specialize (absProof (x4+x5)%R floatMin posResInf floatMinCase3).
              specialize (relative_error absProof).
              (* relative_error *)
              pose proof plusRoundingTruth3 as plusRoundingTruth3.
              specialize (plusRoundingTruth3 x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 ).
              pose proof orExtra as floatMinPremise.
              specialize (floatMinPremise (x4 + x5 >= floatMin)%R (x4 + x5 <= 0 - floatMin)%R floatMinCase3).
              apply Rge_le in x1lb.
              apply Rge_le in x2lb.
              specialize (plusRoundingTruth3 floatMinPremise x1lb x2lb floatMaxBound1).
              pose proof floatMaxBoundHelper as floatMaxBound2.
              specialize (floatMaxBound2 lb1 lb2 floatMax error resultGe0 floatMaxGt0 errorGt0).
              specialize (plusRoundingTruth3 floatMaxBound2 x1ub x2ub).
              pose proof plusRoundingTruth2 as plusRoundingTruth2.
              specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2
                                             plusRoundingTruth3).
              decompose [and] plusRoundingTruth2.
              inversion Heqo0.
              rewrite <- plusResultStmt in H0.
              inversion H0.
            }
            {
              apply Rnot_ge_lt in n0.
              
              generalize (el2 radix2 (x4+x5)%R (ln_beta radix2 (x4+x5))).
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
              specialize (posResInf lb1 lb2 x4 x5 x1lb x2lb resultGe0).
              apply Rge_le in posResInf.
              destruct (Rle_lt_or_eq_dec 0 (x4+x5)%R).
              {
                apply posResInf.
              }
              {
                pose proof subNormal as subNormalProof. 
                apply Rlt_gt in r.
                specialize (subNormalProof (x4+x5)%R r n0).
                remember (ln_beta radix2 (x4 + x5)) as ex.
                
                pose proof gt0ImpNE0 as gt0ImpNE0.
                specialize (gt0ImpNE0 (x4+x5)%R r).
                specialize (ln_beta_premise gt0ImpNE0).
                pose proof bpow_le as bpow_le.
                specialize (bpow_le radix2 ex custom_emin subNormalProof).
                pose proof plusRoundingTruth2.
                intros.
                pose proof floatMaxProofRounding.
                specialize (H0 (x4 +x5)%R ex ln_beta_premise subNormalProof n0 r).
                assert (floatToRealRelationForExpr1 := floatToRealProof1).
                assert (floatToRealRelationForExpr2 := floatToRealProof2).
                apply validFloat2 in floatToRealProof1.
                apply validFloat2 in floatToRealProof2.
                
                specialize (H x2 x3 x4 x5 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                rewrite <- floatToRealProof1 in H.
                rewrite <- floatToRealProof2 in H.
                destruct H0.
                specialize (H H1).
                decompose [and] H.
                inversion Heqo0.
                rewrite <- plusResultStmt in *.
                simpl in *.
                intuition.
              }      
              {
                pose proof plusRoundingTruth2.
                pose proof round_0 as round_0.
                specialize (round_0 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef)).
                
                pose proof zeroLtFloatMax.
                specialize (H0 (round radix2
                                      (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                      (round_mode mode_NE) 0) round_0).
                assert (floatToRealRelationForExpr1 := floatToRealProof1).
                assert (floatToRealRelationForExpr2 := floatToRealProof2).
                apply validFloat2 in floatToRealProof1.
                apply validFloat2 in floatToRealProof2.
                unfold floatMax in *.
                specialize (H x2 x3 x4 x5 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                rewrite <- floatToRealProof1 in H.
                rewrite <- floatToRealProof2 in H.
                rewrite e in *.
                specialize (H H0).
                decompose [and] H.
                inversion Heqo0.
                simpl in *.
                unfold is_finite in *.
                rewrite <- plusResultStmt in *.
                intuition.
              }
            }
          }
          
          {
            simpl in *.
            remember (lb x0 fState) as lb1.
            remember (lb x1 fState) as lb2.
            remember (ub x1 fState) as ub2.
            remember (ub x0 fState) as ub1.
            clear Hequb1 Hequb2 Heqlb1 Heqlb2.
            clear x0 x1 x.
            destruct (Rge_dec (x4+x5)%R floatMin).
            {
              assert (floatMinCase3 := r).
              clear r.
              (* relative_error*)
              pose proof relative_error as relative_error.
              specialize (relative_error radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) validFexpProof (custom_emin)%Z custom_prec precThm (round_mode mode_NE) (valid_rnd_N choiceDef) (x4 + x5)%R).

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
              apply Rle_ge in x1lb.
              apply Rle_ge in x2lb.
              SearchAbout (_ > 0 -> _ >= 0)%R.
              specialize (posResInf lb1 lb2 x4 x5 x1lb x2lb resultGe0).
              specialize (absProof (x4+x5)%R floatMin posResInf floatMinCase3).
              specialize (relative_error absProof).
              (* relative_error *)
              pose proof plusRoundingTruth3 as plusRoundingTruth3.
              specialize (plusRoundingTruth3 x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 ).
              pose proof orExtra as floatMinPremise.
              specialize (floatMinPremise (x4 + x5 >= floatMin)%R (x4 + x5 <= 0 - floatMin)%R floatMinCase3).
              apply Rge_le in x1lb.
              apply Rge_le in x2lb.
              specialize (plusRoundingTruth3 floatMinPremise x1lb x2lb floatMaxBound1).
              pose proof floatMaxBoundHelper as floatMaxBound2.
              specialize (floatMaxBound2 lb1 lb2 floatMax error resultGe0 floatMaxGt0 errorGt0).
              specialize (plusRoundingTruth3 floatMaxBound2 x1ub x2ub).
               pose proof plusRoundingTruth2 as plusRoundingTruth2.
              specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2
                         plusRoundingTruth3).
              rewrite <- plusResultStmt in plusRoundingTruth2.
              remember ( B2R custom_prec custom_emax
                         (B754_finite custom_prec custom_emax b m e e0)).
              simpl in Heqr.
              rewrite Heqr in plusRoundingTruth2.
              destruct plusRoundingTruth2.
              clear r Heqr.
              assert (bplusCorrectStmt := H).
              assert (resultFiniteTruth := H0).
              clear H H0.
              inversion Heqo0.
              rewrite (bplusCorrectStmt).
              clear bplusCorrectStmt resultFiniteTruth plusRoundingTruth3 absProof floatMinPremise floatMinCase1 floatMinCase2 floatMinCase3 floatMaxBound1 floatMaxBound2.
              apply validFloat2 in floatToRealProof1.
              apply validFloat2 in floatToRealProof2.
              rewrite <- floatToRealProof1.
              rewrite <- floatToRealProof2.
              
              intros.
              pose proof boundUsingRelativeErrorProof as boundUsingRelativeErrorProof.
              specialize (boundUsingRelativeErrorProof lb1 lb2 ub1 ub2 x4 x5 x1lb x1ub x2lb x2ub resultGe0 relative_error).
              split.
              apply boundUsingRelativeErrorProof.
              unfold isFloatConstValid.
              rewrite <- plusResultStmt.
              intuition.
            }
            {
               apply Rnot_ge_lt in n.
              
              generalize (el2 radix2 (x4+x5)%R (ln_beta radix2 (x4+x5))).
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
              specialize (posResInf lb1 lb2 x4 x5 x1lb x2lb resultGe0).
              apply Rge_le in posResInf.
              destruct (Rle_lt_or_eq_dec 0 (x4+x5)%R).
              {
                apply posResInf.
              }
              {
                pose proof subNormal as subNormalProof. 
                apply Rlt_gt in r.
                specialize (subNormalProof (x4+x5)%R r n).
                remember (ln_beta radix2 (x4 + x5)) as ex.
                
                pose proof gt0ImpNE0 as gt0ImpNE0.
                specialize (gt0ImpNE0 (x4+x5)%R r).
                specialize (ln_beta_premise gt0ImpNE0).
                pose proof bpow_le as bpow_le.
                specialize (bpow_le radix2 ex custom_emin subNormalProof).
                pose proof plusRoundingTruth2.
  
                intros.
                pose proof floatMaxProofRounding.
                specialize (H0 (x4 +x5)%R ex ln_beta_premise subNormalProof n r).
                assert (floatToRealRelationForExpr1 := floatToRealProof1).
                assert (floatToRealRelationForExpr2 := floatToRealProof2).
                apply validFloat2 in floatToRealProof1.
                apply validFloat2 in floatToRealProof2.
                
                specialize (H x2 x3 x4 x5 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                rewrite <- floatToRealProof1 in H.
                rewrite <- floatToRealProof2 in H.
                destruct H0.
                specialize (H H1).
                destruct H.
                rewrite <- plusResultStmt in H.
                unfold B2R in H.
                remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                (round_mode mode_NE) (x4 + x5)) as roundedValue.
                destruct H0.
                {
                  unfold FLT_exp in H0.
                  destruct (Z_le_gt_dec (ex - custom_prec) (3 - custom_emax - custom_prec)%Z).
                  {
                    pose proof zMaxProof as zMaxProof.
                    specialize (zMaxProof (ex - custom_prec)%Z (3 - custom_emax - custom_prec)%Z l).
                    rewrite zMaxProof in *.
                    clear zMaxProof.  
                    Print customEminMinValue.
                    pose proof customEminMinValue as customEminMinValue.
                    rewrite <- H in *.
                    apply Z.ge_le in customEminMinValue.
                    pose proof compcert.flocq.Core.Fcore_Raux.bpow_le.
                    specialize (H3 radix2 (3 - custom_emax - custom_prec)%Z custom_emin customEminMinValue).
                    unfold floatMin in *.
                    unfold error, custom_emin,custom_emax, custom_prec in *.
                    pose proof bpow_gt_0 as bpowGt0_1.
                    specialize (bpowGt0_1 radix2 (- prec + 1)%Z)%R.
                    clear H H2 H1 l customEminMinValue ln_beta_premise floatToRealProof1 floatToRealProof2 absImp posResInf.
                    unfold lofst in *.
                    inversion Heqo0.
                    split.
                    split.
                    pose proof bpow_gt_0 as bpow_gt_0_2.
                    specialize (bpow_gt_0_2 radix2 (3-emax-prec)%Z).                   
                    psatz R.
                    psatz R.
                    rewrite <- plusResultStmt.
                    unfold isFloatConstValid.
                    intuition.
                  }
                  {
                    assert (g:=g0).
                    clear g0.
                    pose proof zMaxProof as zMaxProof.
                    
                    intros.
                    apply zlt_le in g.
                    apply Z.ge_le in g.
                    specialize (zMaxProof (3 - custom_emax - custom_prec)%Z (ex - custom_prec)%Z g).
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
                    unfold lofst in *.
                    inversion Heqo0.
                    rewrite H in *.
                    split.
                    psatz R.
                    rewrite <- plusResultStmt.
                    unfold isFloatConstValid.
                    intuition.
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
                    unfold lofst in *.
                    inversion Heqo0.
                    split.
                    rewrite H in *.
                    psatz R.
                    rewrite <- plusResultStmt.
                    unfold isFloatConstValid.
                    intuition.
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
                    unfold lofst in *.
                    inversion Heqo0.
                    split.
                    rewrite H in *.
                    psatz R.
                    rewrite <- plusResultStmt.
                    unfold isFloatConstValid.
                    intuition.
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
                assert (floatToRealRelationForExpr1 := floatToRealProof1).
                assert (floatToRealRelationForExpr2 := floatToRealProof2).
                apply validFloat2 in floatToRealProof1.
                apply validFloat2 in floatToRealProof2.
                unfold floatMax in *.
                specialize (H x2 x3 x4 x5 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                rewrite <- floatToRealProof1 in H.
                rewrite <- floatToRealProof2 in H.
                unfold floatMin in *.
                rewrite floatToRealProof1 in *.
                rewrite floatToRealProof2 in *.
                pose proof bpow_gt_0.
                specialize (H1 radix2 custom_emin).
                rewrite e1 in *.
                specialize (H H0).                
                pose proof errorGt0.
                unfold lofst in *.
                inversion Heqo0.
                rewrite <- e1 in *.
                split.
                simpl in f_des.
                simpl in plusResultStmt.
                rewrite <- plusResultStmt in *.
                decompose [and] H.
                remember (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                (round_mode mode_NE) 0)%R as roundedValue.
                simpl in H4.
                
                inversion Heqo0.
                psatz R.
                rewrite <- plusResultStmt.
                unfold isFloatConstValid.
                intuition.
              }
            }
          }
        }
        {
          destruct H2.
          { 
            unfold simpleBound in *.
            rewrite <- H2 in *.
            clear H2.
            simpl in *.
            destruct H0.
            destruct H2.
            destruct H3.
            destruct H4.
            destruct H5.
            destruct H6.
            destruct H6.
            destruct H7.
            destruct H7.
            forward_reason.
            assert (floatToReal x2 = floatToReal x2).
            intuition.
            assert (floatToReal x3 = floatToReal x3).
            intuition.
            specialize (IHexpr1 (floatToReal x2) _ H0 H x2 H10 H6).
            specialize (IHexpr2 (floatToReal x3) _ H2 H1 x3 H11 H7).
            clear H11. clear H10.
            inversion H9.
            inversion H8.
            rewrite <- H10 in *.
            rewrite <- H11 in *.
            assert (floatToRealProof1 := H10).
            assert (floatToRealProof2 := H11).
            rewrite <- H6 in *.
            rewrite <- H7 in *.
            inversion Heqo.
            unfold float_plus.
            assert (validFloatArg1 := H9).
            assert (validFloatArg2 := H8).
            unfold lofst in *.
            assert (floatMinCase1 := H3).
            assert (floatMaxBound1 := H4).
            assert (resultGe0 := H5).
            inversion Heqo.
            clear Heqo.
            assert (plusResultStmt := H14).  
            clear H11 H13 H6 H8 H0 H2 H H1 H9 H10 H14 H7 H3 H4 H5 H14.
            destruct IHexpr1.
            destruct IHexpr2.
            assert (validArg1 := H0).
            assert (validArg2 := H2).
            assert (expr1Bound := H).
            assert (expr2Bound := H1).
            remember (lb x0 fState) as lb1.
            remember (lb x1 fState) as lb2.
            remember (ub x0 fState)  as ub2.
            remember (ub x1 fState) as ub1.
            clear Hequb1 Hequb2 Heqlb1 Heqlb2.
            unfold lofst in *.
            clear H H1 H0 H2.
            unfold float_plus in *.
            destruct f eqn:f_des.
            {
              simpl in *.
              clear x0 x1 x.
              destruct (Rle_dec floatMin (x4+x5)%R).
              {
                inversion Heqo0.
                rewrite <- plusResultStmt in *.
                simpl in *.
                split.
                psatz R.
                intuition.
              }
              {
                apply Rnot_le_gt in n.
                pose proof floatMaxProofRounding as floatMaxProofRounding.
                generalize (el2 radix2 (x4+x5)%R (ln_beta radix2 (x4+x5)%R)).
                intros.
                destruct (Rle_lt_or_eq_dec 0 (x4+x5)%R).
                {
                  psatz R.
                }
                {
                  assert (resultNe0 := r).                
                  apply RMicromega.Rlt_neq in resultNe0.
                  assert (ln_beta_premise :=H).
                  clear H.
                  specialize (ln_beta_premise resultNe0).
                  remember (ln_beta radix2 (x4 + x5)) as ex.
                  specialize (floatMaxProofRounding (x4 + x5)%R ex ln_beta_premise).
                  pose proof subNormal as subNormalProof.
                  apply Rlt_gt in r.
                  apply Rgt_lt in n.
                  specialize (subNormalProof (x4+x5)%R r n).
                  rewrite <- Heqex in subNormalProof.
                  specialize (floatMaxProofRounding subNormalProof n r).
                  destruct floatMaxProofRounding.
                  pose proof plusRoundingTruth2 as plusRoundingTruth2.
                  assert (floatToRealRelationForExpr1 := floatToRealProof1).
                  assert (floatToRealRelationForExpr2 := floatToRealProof2).
                  apply validFloat2 in floatToRealRelationForExpr1.
                  apply validFloat2 in floatToRealRelationForExpr2.
                  specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2).
                  rewrite <- floatToRealRelationForExpr1 in plusRoundingTruth2.
                  rewrite <- floatToRealRelationForExpr2 in plusRoundingTruth2.
                  specialize (plusRoundingTruth2 H0).
                  destruct plusRoundingTruth2.
                  rewrite <- plusResultStmt in *.
                  unfold B2R in H1.
                  rewrite H1 in *.
                  remember ( round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                   (round_mode mode_NE) (x4 + x5)) as roundedValue.
                  destruct H.
                  {
                    unfold FLT_exp in H.
                    
                    intros.
                    pose proof roundedValLessThanFloatMin.
                    specialize (H3 ex subNormalProof).
                    unfold FLT_exp in H3.
                    pose proof bpow_gt_0.
                    specialize (H4 radix2 (Z.max (ex - custom_prec) (3 - custom_emax - custom_prec))).
                    psatz R.
                  }  
                  {
                    destruct H.
                    {
                      unfold floatMin.
                      pose proof bpow_gt_0.
                      specialize (H3 radix2 custom_emin).
                      inversion Heqo0.
                      split.
                      psatz R.
                      simpl in *.
                      intuition.
                    }
                    {
                      pose proof bpow_le.
                      specialize (H3 radix2 ex custom_emin subNormalProof).
                      pose proof bpow_gt_0.
                      specialize (H4 radix2 (ex-1)%Z).
                      unfold floatMin.
                      inversion Heqo0.
                      split.
                      psatz R.
                      simpl in *.
                      intuition.
                    }

                  }
                }
                {

                  pose proof plusRoundingTruth2.
                  
                  pose proof round_0 as round_0.
                  specialize (round_0 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef)).
                  pose proof zeroLtFloatMax.
                  specialize (H1 (round radix2
                                        (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                        (round_mode mode_NE) 0) round_0).
                  assert (floatToRealRelationForExpr1 := floatToRealProof1).
                  assert (floatToRealRelationForExpr2 := floatToRealProof2).
                  apply validFloat2 in floatToRealProof1.
                  apply validFloat2 in floatToRealProof2.
                  unfold floatMax in *.
                  
                  specialize (H0 x2 x3 x4 x5 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                  rewrite <- floatToRealProof1 in *.
                  rewrite <- floatToRealProof2 in *.
                  rewrite <- e in *.
                  specialize (H0 H1).              
                  rewrite <- plusResultStmt in *.
                  unfold B2R in *.
                  rewrite round_0 in *.
                  destruct H0.
                  inversion Heqo0.
                  split.
                  psatz R.
                  simpl in *; intuition.
                }
              }
            }                
            {
              simpl in *.
              clear x0 x1 x.
              destruct (Rle_dec floatMin (x4+x5)%R).
              {
                psatz R.
              }
              {
                apply Rnot_le_gt in n.
                pose proof floatMaxProofRounding as floatMaxProofRounding.
                generalize (el2 radix2 (x4+x5)%R (ln_beta radix2 (x4+x5)%R)).
                intros.
                destruct (Rle_lt_or_eq_dec 0 (x4+x5)%R).
                {
                  psatz R.
                }
                {
                  assert (resultNe0 := r).                
                  apply RMicromega.Rlt_neq in resultNe0.
                  assert (ln_beta_premise :=H).
                  clear H.
                  specialize (ln_beta_premise resultNe0).
                  remember (ln_beta radix2 (x4 + x5)) as ex.
                  specialize (floatMaxProofRounding (x4 + x5)%R ex ln_beta_premise).
                  pose proof subNormal as subNormalProof.
                  apply Rlt_gt in r.
                  apply Rgt_lt in n.
                  specialize (subNormalProof (x4+x5)%R r n).
                  rewrite <- Heqex in subNormalProof.
                  specialize (floatMaxProofRounding subNormalProof n r).
                  destruct floatMaxProofRounding.
                  pose proof plusRoundingTruth2 as plusRoundingTruth2.
                  assert (floatToRealRelationForExpr1 := floatToRealProof1).
                  assert (floatToRealRelationForExpr2 := floatToRealProof2).
                  apply validFloat2 in floatToRealRelationForExpr1.
                  apply validFloat2 in floatToRealRelationForExpr2.
                  specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2).
                  rewrite <- floatToRealRelationForExpr1 in plusRoundingTruth2.
                  rewrite <- floatToRealRelationForExpr2 in plusRoundingTruth2.
                  specialize (plusRoundingTruth2 H0).
                  destruct plusRoundingTruth2.
                  rewrite <- plusResultStmt in *.
                  unfold B2R in H1.
                  rewrite H1 in *.
                  remember ( round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                   (round_mode mode_NE) (x4 + x5)) as roundedValue.
                  destruct H.
                  {
                    unfold FLT_exp in H.
                    
                    intros.
                    pose proof roundedValLessThanFloatMin.
                    specialize (H3 ex subNormalProof).
                    unfold FLT_exp in H3.
                    pose proof bpow_gt_0.
                    specialize (H4 radix2 (Z.max (ex - custom_prec) (3 - custom_emax - custom_prec))).
                    psatz R.
                  }  
                  {
                    destruct H.
                    {
                      unfold floatMin.
                      pose proof bpow_gt_0.
                      specialize (H3 radix2 custom_emin).
                      inversion Heqo0.
                      inversion H2.
                    }
                    {
                      pose proof bpow_le.
                      specialize (H3 radix2 ex custom_emin subNormalProof).
                      pose proof bpow_gt_0.
                      specialize (H4 radix2 (ex-1)%Z).
                      unfold floatMin.
                      inversion Heqo0.
                      inversion H2.
                    }

                  }
                }
                {

                  pose proof plusRoundingTruth2.
                  
                  pose proof round_0 as round_0.
                  specialize (round_0 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef)).
                  pose proof zeroLtFloatMax.
                  specialize (H1 (round radix2
                                        (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                        (round_mode mode_NE) 0) round_0).
                  assert (floatToRealRelationForExpr1 := floatToRealProof1).
                  assert (floatToRealRelationForExpr2 := floatToRealProof2).
                  apply validFloat2 in floatToRealProof1.
                  apply validFloat2 in floatToRealProof2.
                  unfold floatMax in *.
                  
                  specialize (H0 x2 x3 x4 x5 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                  rewrite <- floatToRealProof1 in *.
                  rewrite <- floatToRealProof2 in *.
                  rewrite <- e in *.
                  specialize (H0 H1).              
                  rewrite <- plusResultStmt in *.
                  unfold B2R in *.
                  rewrite round_0 in *.
                  destruct H0.
                  inversion Heqo0.
                  inversion H2.
                }
              }
            }
            {   
              {
                simpl in *.
                clear x0 x1 x.
                destruct (Rle_dec floatMin (x4+x5)%R).
                {
                  psatz R.
                }
                {
                  apply Rnot_le_gt in n0.
                  pose proof floatMaxProofRounding as floatMaxProofRounding.
                  generalize (el2 radix2 (x4+x5)%R (ln_beta radix2 (x4+x5)%R)).
                  intros.
                  destruct (Rle_lt_or_eq_dec 0 (x4+x5)%R).
                  {
                    psatz R.
                  }
                  {
                    assert (resultNe0 := r).                
                    apply RMicromega.Rlt_neq in resultNe0.
                    assert (ln_beta_premise :=H).
                    clear H.
                    specialize (ln_beta_premise resultNe0).
                    remember (ln_beta radix2 (x4 + x5)) as ex.
                    specialize (floatMaxProofRounding (x4 + x5)%R ex ln_beta_premise).
                    pose proof subNormal as subNormalProof.
                    apply Rlt_gt in r.
                    apply Rgt_lt in n0.
                    specialize (subNormalProof (x4+x5)%R r n0).
                    rewrite <- Heqex in subNormalProof.
                    specialize (floatMaxProofRounding subNormalProof n0 r).
                    destruct floatMaxProofRounding.
                    pose proof plusRoundingTruth2 as plusRoundingTruth2.
                    assert (floatToRealRelationForExpr1 := floatToRealProof1).
                    assert (floatToRealRelationForExpr2 := floatToRealProof2).
                    apply validFloat2 in floatToRealRelationForExpr1.
                    apply validFloat2 in floatToRealRelationForExpr2.
                    specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2).
                    rewrite <- floatToRealRelationForExpr1 in plusRoundingTruth2.
                    rewrite <- floatToRealRelationForExpr2 in plusRoundingTruth2.
                    specialize (plusRoundingTruth2 H0).
                    destruct plusRoundingTruth2.
                    rewrite <- plusResultStmt in *.
                    unfold B2R in H1.
                    rewrite H1 in *.
                    remember ( round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                     (round_mode mode_NE) (x4 + x5)) as roundedValue.
                    destruct H.
                    {
                      unfold FLT_exp in H.
                      
                      intros.
                      pose proof roundedValLessThanFloatMin.
                      specialize (H3 ex subNormalProof).
                      unfold FLT_exp in H3.
                      pose proof bpow_gt_0.
                      specialize (H4 radix2 (Z.max (ex - custom_prec) (3 - custom_emax - custom_prec))).
                      psatz R.
                    }  
                    {
                      destruct H.
                      {
                        unfold floatMin.
                        pose proof bpow_gt_0.
                        specialize (H3 radix2 custom_emin).
                        inversion Heqo0.
                        inversion H2.
                      }
                      {
                        pose proof bpow_le.
                        specialize (H3 radix2 ex custom_emin subNormalProof).
                        pose proof bpow_gt_0.
                        specialize (H4 radix2 (ex-1)%Z).
                        unfold floatMin.
                        inversion Heqo0.
                        inversion H2.
                      }

                    }
                  }
                  {

                    pose proof plusRoundingTruth2.
                    
                    pose proof round_0 as round_0.
                    specialize (round_0 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef)).
                    pose proof zeroLtFloatMax.
                    specialize (H1 (round radix2
                                          (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                          (round_mode mode_NE) 0) round_0).
                    assert (floatToRealRelationForExpr1 := floatToRealProof1).
                    assert (floatToRealRelationForExpr2 := floatToRealProof2).
                    apply validFloat2 in floatToRealProof1.
                    apply validFloat2 in floatToRealProof2.
                    unfold floatMax in *.
                    
                    specialize (H0 x2 x3 x4 x5 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                    rewrite <- floatToRealProof1 in *.
                    rewrite <- floatToRealProof2 in *.
                    rewrite <- e in *.
                    specialize (H0 H1).              
                    rewrite <- plusResultStmt in *.
                    unfold B2R in *.
                    rewrite round_0 in *.
                    destruct H0.
                    inversion Heqo0.
                    inversion H2.
                  }
                }
              }
            }
            {
              simpl in *.
              clear x0 x1 x.
              destruct (Rle_dec floatMin (x4+x5)%R).
              {
                inversion Heqo0.
                rewrite <- plusResultStmt in *.
                simpl in *.
                split.
                psatz R.
                unfold isFloatConstValid.
                intuition.
              }
              {
                apply Rnot_le_gt in n.
                pose proof floatMaxProofRounding as floatMaxProofRounding.
                generalize (el2 radix2 (x4+x5)%R (ln_beta radix2 (x4+x5)%R)).
                intros.
                destruct (Rle_lt_or_eq_dec 0 (x4+x5)%R).
                {
                  psatz R.
                }
                {
                  assert (resultNe0 := r).                
                  apply RMicromega.Rlt_neq in resultNe0.
                  assert (ln_beta_premise :=H).
                  clear H.
                  specialize (ln_beta_premise resultNe0).
                  remember (ln_beta radix2 (x4 + x5)) as ex.
                  specialize (floatMaxProofRounding (x4 + x5)%R ex ln_beta_premise).
                  pose proof subNormal as subNormalProof.
                  apply Rlt_gt in r.
                  apply Rgt_lt in n.
                  specialize (subNormalProof (x4+x5)%R r n).
                  rewrite <- Heqex in subNormalProof.
                  specialize (floatMaxProofRounding subNormalProof n r).
                  destruct floatMaxProofRounding.
                  pose proof plusRoundingTruth2 as plusRoundingTruth2.
                  assert (floatToRealRelationForExpr1 := floatToRealProof1).
                  assert (floatToRealRelationForExpr2 := floatToRealProof2).
                  apply validFloat2 in floatToRealRelationForExpr1.
                  apply validFloat2 in floatToRealRelationForExpr2.
                  specialize (plusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2).
                  rewrite <- floatToRealRelationForExpr1 in plusRoundingTruth2.
                  rewrite <- floatToRealRelationForExpr2 in plusRoundingTruth2.
                  specialize (plusRoundingTruth2 H0).
                  destruct plusRoundingTruth2.
                  rewrite <- plusResultStmt in *.
                  unfold B2R in H1.
                  rewrite H1 in *.
                  remember ( round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                   (round_mode mode_NE) (x4 + x5)) as roundedValue.
                  destruct H.
                  {
                    unfold FLT_exp in H.
                    
                    intros.
                    pose proof roundedValLessThanFloatMin.
                    specialize (H3 ex subNormalProof).
                    unfold FLT_exp in H3.
                    pose proof bpow_gt_0.
                    specialize (H4 radix2 (Z.max (ex - custom_prec) (3 - custom_emax - custom_prec))).
                    inversion Heqo0.
                    split.
                    psatz R.
                    unfold isFloatConstValid.
                    intuition.
                  }  
                  {
                    destruct H.
                    {
                      unfold floatMin.
                      pose proof bpow_gt_0.
                      specialize (H3 radix2 custom_emin).
                      inversion Heqo0.
                      split.
                      psatz R.
                      simpl in *.
                      intuition.
                    }
                    {
                      pose proof bpow_le.
                      specialize (H3 radix2 ex custom_emin subNormalProof).
                      pose proof bpow_gt_0.
                      specialize (H4 radix2 (ex-1)%Z).
                      unfold floatMin.
                      inversion Heqo0.
                      split.
                      psatz R.
                      simpl in *.
                      intuition.
                    }

                  }
                }
                {

                  pose proof plusRoundingTruth2.
                  
                  pose proof round_0 as round_0.
                  specialize (round_0 radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (valid_rnd_N choiceDef)).
                  pose proof zeroLtFloatMax.
                  specialize (H1 (round radix2
                                        (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                        (round_mode mode_NE) 0) round_0).
                  assert (floatToRealRelationForExpr1 := floatToRealProof1).
                  assert (floatToRealRelationForExpr2 := floatToRealProof2).
                  apply validFloat2 in floatToRealProof1.
                  apply validFloat2 in floatToRealProof2.
                  unfold floatMax in *.
                  
                  specialize (H0 x2 x3 x4 x5 floatToRealRelationForExpr1 floatToRealRelationForExpr2).
                  rewrite <- floatToRealProof1 in *.
                  rewrite <- floatToRealProof2 in *.
                  rewrite <- e1 in *.
                  specialize (H0 H1).              
                  rewrite <- plusResultStmt in *.
                  unfold B2R in *.
                  rewrite round_0 in *.
                  destruct H0.
                  inversion Heqo0.
                  split.
                  psatz R.
                  simpl in *; intuition.
                }
              }
              
            }
          }
          intuition.
        }
      }
    }
  }  
  {    
    simpl in *.
    intros.
    eapply In_cross_In in H.
    simpl in H.
    forward_reason.
    destruct H2.
    {
      unfold simpleBound in *.
      rewrite <- H2 in *.
      clear H2.
      simpl in *.
      destruct H0.
      destruct H2.
      destruct H3.
      destruct H4.
      destruct H5.
      destruct H6.
      destruct H6.
      destruct H7.
      inversion Heqo.
      
      forward_reason.
      assert (floatToReal x2 = floatToReal x2).
      intuition.
      assert (floatToReal x3 = floatToReal x3).
      intuition.
      specialize (IHexpr1 (floatToReal x2) _ H0 H x2 H11 H6).
      specialize (IHexpr2 (floatToReal x3) _ H2 H1 x3 H12 H7).
      inversion H10.
      inversion H8.
      rewrite <- H13 in *.
      rewrite <- H14 in *.
       assert (floatToRealRelationForExpr1:= H13).
      assert (floatToRealRelationForExpr2:= H14).
      assert (floatToRealProof1 := H13).
      assert (floatToRealProof2 := H14).
      rewrite <- H6 in *.
      rewrite <- H7 in *.
      assert (validFloatArg1 := H10).
      assert (validFloatArg2 := H8).
      clear H11 H12 H6 H8 H0 H2 H H1 H9 H10 H13 H14 H7.
      
      unfold float_minus in *.
      destruct f eqn:f_des.
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H7).
        assert (expr1Bound := H0).
        assert (expr2Bound := H6).
        assert (floatMinCase := H4).
        assert (floatMaxBound1 := H5). 
        assert (resultGe0 := H3).
        assert (minusResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMinus as relErrorBasedOnFloatMinTruthMinus.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMinus x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        
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
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H0 H2 H1 H3).
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
        
        specialize (minusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        
        pose proof minusRoundingTruth2 as minusRoundingTruth2.
        specialize (minusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 minusRoundingTruth).
        revert minusResultStmt. intros minusResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 -
                          B2R custom_prec custom_emax x3)) as roundedValue.
        simpl in minusRoundingTruth2.
        simpl in minusResultStmt.
        rewrite <- minusResultStmt in minusRoundingTruth2.
        simpl in minusRoundingTruth2.
        decompose [and] minusRoundingTruth2.
        rewrite H5.
        clear H6.
        clear minusRoundingTruth2. 
        assert (minusRoundingTruth2:= H5).
        clear H5.
        clear minusResultStmt.
        clear H4.
        clear minusRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
          pose proof errorGt0.
        clear  floatMinCase floatMaxBound1 HeqroundedValue minusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x2 x3 expr1 expr2  b f_des Heqo validFloatArg2 expr2Valid Heqlb1 Hequb1 validFloatArg1 expr1Valid.  clear x0 x1 x Heqlb2 Hequb2 f H.
         
        pose proof errorLessThan1.
        unfold error in *.
        unfold Rabs in *.
        clear extraFloatMinCase2 andExtra extraFloatMinCase.
        destruct Rcase_abs. 
        {
          destruct Rcase_abs.
          {
            split.
            {
              psatz R.
            }
            {
              intuition.
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
            psatz R.
          }
          {
            psatz R.
          }
        }
      }
      {
         inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H7).
        assert (expr1Bound := H0).
        assert (expr2Bound := H6).
        assert (floatMinCase := H4).
        assert (floatMaxBound1 := H5). 
        assert (resultGe0 := H3).
        assert (minusResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMinus as relErrorBasedOnFloatMinTruthMinus.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMinus x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        
         
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
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H0 H2 H1 H3).
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
        
        specialize (minusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        
        pose proof minusRoundingTruth2 as minusRoundingTruth2.
        specialize (minusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 minusRoundingTruth).
        decompose [and] minusRoundingTruth2.
        rewrite <- minusResultStmt in *.
        simpl in *.
        intuition.
      }
      {
         inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H7).
        assert (expr1Bound := H0).
        assert (expr2Bound := H6).
        assert (floatMinCase := H4).
        assert (floatMaxBound1 := H5). 
        assert (resultGe0 := H3).
        assert (minusResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMinus as relErrorBasedOnFloatMinTruthMinus.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMinus x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        
         
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
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H0 H2 H1 H3).
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
        
        specialize (minusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        
        pose proof minusRoundingTruth2 as minusRoundingTruth2.
        specialize (minusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 minusRoundingTruth).
        decompose [and] minusRoundingTruth2.
        rewrite <- minusResultStmt in *.
        simpl in *.
        intuition.
      }
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H7).
        assert (expr1Bound := H0).
        assert (expr2Bound := H6).
        assert (floatMinCase := H4).
        assert (floatMaxBound1 := H5). 
        assert (resultGe0 := H3).
        assert (minusResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMinus as relErrorBasedOnFloatMinTruthMinus.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMinus x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        
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
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H0 H2 H1 H3).
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
        
        specialize (minusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        
        pose proof minusRoundingTruth2 as minusRoundingTruth2.
        specialize (minusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 minusRoundingTruth).
        revert minusResultStmt. intros minusResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 -
                          B2R custom_prec custom_emax x3)) as roundedValue.
        simpl in minusRoundingTruth2.
        simpl in minusResultStmt.
        rewrite <- minusResultStmt in minusRoundingTruth2.
        simpl in minusRoundingTruth2.
        decompose [and] minusRoundingTruth2.
        rewrite H5.
        clear H6.
        clear minusRoundingTruth2. 
        assert (minusRoundingTruth2:= H5).
        clear H5.
        clear minusResultStmt.
        clear H4.
        clear minusRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
          pose proof errorGt0.
          clear Heqo0 H.
        clear  floatMinCase floatMaxBound1 HeqroundedValue minusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x2 x3 expr1 expr2  b f_des Heqo validFloatArg2 expr2Valid Heqlb1 Hequb1 validFloatArg1 expr1Valid.  clear x0 x1 x Heqlb2 Hequb2 f.
         
        pose proof errorLessThan1.
        unfold error in *.
        unfold Rabs in *.
        clear extraFloatMinCase2 andExtra extraFloatMinCase.
        destruct Rcase_abs. 
        {
          destruct Rcase_abs.
          {
            split.
            {
              psatz R.
            }
            {
              intuition.
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
            psatz R.
          }
          {
            psatz R.
          }
        }
      }
    }
    {
      destruct H2.
      {
       unfold simpleBound in *.
      rewrite <- H2 in *.
      clear H2.
      simpl in *.
      destruct H0.
      destruct H2.
      destruct H3.
      destruct H4.
      destruct H5.
      destruct H6.
      destruct H6.
      destruct H7.
      inversion Heqo.
      
      forward_reason.
      assert (floatToReal x2 = floatToReal x2).
      intuition.
      assert (floatToReal x3 = floatToReal x3).
      intuition.
      specialize (IHexpr1 (floatToReal x2) _ H0 H x2 H11 H6).
      specialize (IHexpr2 (floatToReal x3) _ H2 H1 x3 H12 H7).
      inversion H10.
      inversion H8.
      rewrite <- H13 in *.
      rewrite <- H14 in *.
       assert (floatToRealRelationForExpr1:= H13).
      assert (floatToRealRelationForExpr2:= H14).
      assert (floatToRealProof1 := H13).
      assert (floatToRealProof2 := H14).
      rewrite <- H6 in *.
      rewrite <- H7 in *.
      assert (validFloatArg1 := H10).
      assert (validFloatArg2 := H8).
      clear H11 H12 H6 H8 H0 H2 H H1 H9 H10 H13 H14 H7.
      
      unfold float_minus in *.
      destruct f eqn:f_des.
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H7).
        assert (expr1Bound := H0).
        assert (expr2Bound := H6).
        assert (floatMinCase := H4).
        assert (floatMaxBound1 := H5). 
        assert (resultGe0 := H3).
        assert (minusResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMinus as relErrorBasedOnFloatMinTruthMinus.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMinus x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        
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
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H0 H2 H1 H3).
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
        
        specialize (minusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        
        pose proof minusRoundingTruth2 as minusRoundingTruth2.
        specialize (minusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 minusRoundingTruth).
        revert minusResultStmt. intros minusResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 -
                          B2R custom_prec custom_emax x3)) as roundedValue.
        simpl in minusRoundingTruth2.
        simpl in minusResultStmt.
        rewrite <- minusResultStmt in minusRoundingTruth2.
        simpl in minusRoundingTruth2.
        decompose [and] minusRoundingTruth2.
        rewrite H5.
        clear H6.
        clear minusRoundingTruth2.
        assert (minusRoundingTruth2
:= H4).
        clear H5.
        clear minusResultStmt.
        clear H4.
        clear minusRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear  floatMinCase floatMaxBound1 HeqroundedValue minusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x x1 x0 expr1 expr2  fState b f_des Heqo validFloatArg2 expr2Valid Heqlb1 Hequb1 Heqlb2 Hequb2 expr1Valid validFloatArg1 H.
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
              psatz R.
            }
            {
              intuition.
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
            psatz R.
          }
          {
            psatz R.
          }
        }
      }
      {
         inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H7).
        assert (expr1Bound := H0).
        assert (expr2Bound := H6).
        assert (floatMinCase := H4).
        assert (floatMaxBound1 := H5). 
        assert (resultGe0 := H3).
        assert (minusResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMinus as relErrorBasedOnFloatMinTruthMinus.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMinus x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
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
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H0 H2 H1 H3).
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
        
        specialize (minusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        
        pose proof minusRoundingTruth2 as minusRoundingTruth2.
        specialize (minusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 minusRoundingTruth).
        rewrite <- minusResultStmt in *.
        decompose [and] minusRoundingTruth2.
        simpl in *.
        intuition.
      }
      {
         inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H7).
        assert (expr1Bound := H0).
        assert (expr2Bound := H6).
        assert (floatMinCase := H4).
        assert (floatMaxBound1 := H5). 
        assert (resultGe0 := H3).
        assert (minusResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMinus as relErrorBasedOnFloatMinTruthMinus.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMinus x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
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
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H0 H2 H1 H3).
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
        
        specialize (minusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        
        pose proof minusRoundingTruth2 as minusRoundingTruth2.
        specialize (minusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 minusRoundingTruth).
        rewrite <- minusResultStmt in *.
        decompose [and] minusRoundingTruth2.
        simpl in *.
        intuition.
      }
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H7).
        assert (expr1Bound := H0).
        assert (expr2Bound := H6).
        assert (floatMinCase := H4).
        assert (floatMaxBound1 := H5). 
        assert (resultGe0 := H3).
        assert (minusResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMinus as relErrorBasedOnFloatMinTruthMinus.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMinus x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
        
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
        specialize (relErrorBasedOnFloatMinTruthMinus extraFloatMinCase H0 H2 H1 H3).
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
        
        specialize (minusRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        
        pose proof minusRoundingTruth2 as minusRoundingTruth2.
        specialize (minusRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 minusRoundingTruth).
        revert minusResultStmt. intros minusResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 -
                          B2R custom_prec custom_emax x3)) as roundedValue.
        simpl in minusRoundingTruth2.
        simpl in minusResultStmt.
        rewrite <- minusResultStmt in minusRoundingTruth2.
        simpl in minusRoundingTruth2.
        decompose [and] minusRoundingTruth2.
        rewrite H5.
        clear H6.
        clear minusRoundingTruth2.
        assert (minusRoundingTruth2
:= H4).
        clear H5.
        clear minusResultStmt.
        clear H4.
        clear minusRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMinus.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear  floatMinCase floatMaxBound1 HeqroundedValue minusRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x x1 x0 expr1 expr2  fState b f_des Heqo validFloatArg2 expr2Valid Heqlb1 Hequb1 Heqlb2 Hequb2 expr1Valid validFloatArg1 H Heqo0.
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
              psatz R.
            }
            {
              intuition.
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
            psatz R.
          }
          {
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
    simpl in *.
    intros.
    eapply In_cross_In in H.
    simpl in H.
    forward_reason.
    destruct H2.
    {
      unfold simpleBound in *.
      rewrite <- H2 in *.
      clear H2.
      simpl in *.
      destruct H0.
      destruct H2.
      destruct H3.
      destruct H4.
      destruct H5.
      destruct H6.
      destruct H7.
      destruct H7. 
      destruct H8.
      destruct H7.
      destruct H8.
      inversion Heqo.
      
      forward_reason.
      assert (floatToReal x2 = floatToReal x2).
      intuition.
      assert (floatToReal x3 = floatToReal x3).
      intuition.
      specialize (IHexpr1 (floatToReal x2) _ H0 H x2 H11 H7).
      specialize (IHexpr2 (floatToReal x3) _ H2 H1 x3 H13 H8).
      inversion H9.
      inversion H10.
      rewrite <- H14 in *.
      rewrite <- H15 in *.
       assert (floatToRealRelationForExpr1:= H14).
      assert (floatToRealRelationForExpr2:= H15).
      assert (floatToRealProof1 := H14).
      assert (floatToRealProof2 := H15).
      rewrite <- H7 in *.
      rewrite <- H8 in *.
      assert (validFloatArg1 := H9).
      assert (validFloatArg2 := H10).
      clear H11 H12 H8 H0 H2 H H1 H9 H10 H13 H15 H7.
      
      unfold float_mult in *.
      destruct f eqn:f_des.
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
         pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= lb1 * lb2)%R (lb1 >= 0)%R (lb2 >= 0)%R).
        
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        
        pose proof orExtra3 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R)  ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\(lb1 >= 0)%R /\ (ub2 < 0)%R )  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R) ).
        remember  (Rabs
                                        (round radix2
                                           (FLT_exp
                                              (3 - custom_emax - custom_prec)
                                              custom_prec)
                                           (round_mode mode_NE) 
                                           (x4 * x5) - 
                                         x4 * x5) <
                                      bpow radix2 (- custom_prec + 1) *
                                      Rabs (x4 * x5))%R.
        simpl in relErrorBasedOnFloatMinTruthMult, floatMinCase, extraFloatMinCase.
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
        rewrite HeqP in relErrorBasedOnFloatMinTruthMult.
        clear HeqP.
         intros.
        specialize (andExtra ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0))%R (ub1 * ub2 * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        pose proof orExtra3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).
        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        revert multResultStmt. intros multResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 *
                          B2R custom_prec custom_emax x3)) as roundedValue.
        simpl in multRoundingTruth2.
        simpl in multResultStmt.
        rewrite <- multResultStmt in multRoundingTruth2.
        simpl in multRoundingTruth2.
        decompose [and] multRoundingTruth2.
        rewrite H5.
        clear H6.
        clear multRoundingTruth2.
        assert (multRoundingTruth2:= H5).
        clear H5.
        clear multResultStmt.
        clear H4.
        clear multRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear H8 f_des Heqo H14 validFloatArg1 validFloatArg2 expr1Valid expr2Valid Heqlb1 Heqlb2 Hequb1 Hequb2.
        clear floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x0 x1 x expr1 expr2 b.
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
                
                clear -r r0 resultGe1 resultGe2 H0 H2.  
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
                clear -r r0 resultGe1 resultGe2 H0 H2. 
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
                psatz R.
              }
              {
                psatz R.
              }
            }
          }
          {
            split.
            {
              destruct Rcase_abs.
              {
                psatz R.
              }
              {
                psatz R.
              }
            }
            destruct Rcase_abs.
            {
              psatz R.
            }
            {
              psatz R.
            }
          }
      }
      {
         inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
         pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= lb1 * lb2)%R (lb1 >= 0)%R (lb2 >= 0)%R).
        
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        
        pose proof orExtra3 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R)  ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\(lb1 >= 0)%R /\ (ub2 < 0)%R )  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R) ).
        remember  (Rabs
                                        (round radix2
                                           (FLT_exp
                                              (3 - custom_emax - custom_prec)
                                              custom_prec)
                                           (round_mode mode_NE) 
                                           (x4 * x5) - 
                                         x4 * x5) <
                                      bpow radix2 (- custom_prec + 1) *
                                      Rabs (x4 * x5))%R.
        simpl in relErrorBasedOnFloatMinTruthMult, floatMinCase, extraFloatMinCase.
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
        rewrite HeqP in relErrorBasedOnFloatMinTruthMult.
        clear HeqP.
         intros.
        specialize (andExtra ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0))%R (ub1 * ub2 * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        pose proof orExtra3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).
        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        destruct multRoundingTruth2.
        rewrite <- multResultStmt in *.
        simpl in *.
        intuition.
      }
      {
         inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
         pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= lb1 * lb2)%R (lb1 >= 0)%R (lb2 >= 0)%R).
        
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        
        pose proof orExtra3 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R)  ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\(lb1 >= 0)%R /\ (ub2 < 0)%R )  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R) ).
        remember  (Rabs
                                        (round radix2
                                           (FLT_exp
                                              (3 - custom_emax - custom_prec)
                                              custom_prec)
                                           (round_mode mode_NE) 
                                           (x4 * x5) - 
                                         x4 * x5) <
                                      bpow radix2 (- custom_prec + 1) *
                                      Rabs (x4 * x5))%R.
        simpl in relErrorBasedOnFloatMinTruthMult, floatMinCase, extraFloatMinCase.
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
        rewrite HeqP in relErrorBasedOnFloatMinTruthMult.
        clear HeqP.
         intros.
        specialize (andExtra ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0))%R (ub1 * ub2 * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        pose proof orExtra3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).
        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
          destruct multRoundingTruth2.
        rewrite <- multResultStmt in *.
        simpl in *.
        intuition.
      }
      {
         inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
         pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= lb1 * lb2)%R (lb1 >= 0)%R (lb2 >= 0)%R).
        
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        
        pose proof orExtra3 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R)  ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\(lb1 >= 0)%R /\ (ub2 < 0)%R )  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R) ).
        remember  (Rabs
                                        (round radix2
                                           (FLT_exp
                                              (3 - custom_emax - custom_prec)
                                              custom_prec)
                                           (round_mode mode_NE) 
                                           (x4 * x5) - 
                                         x4 * x5) <
                                      bpow radix2 (- custom_prec + 1) *
                                      Rabs (x4 * x5))%R.
        simpl in relErrorBasedOnFloatMinTruthMult, floatMinCase, extraFloatMinCase.
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
        rewrite HeqP in relErrorBasedOnFloatMinTruthMult.
        clear HeqP.
         intros.
        specialize (andExtra ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0))%R (ub1 * ub2 * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        pose proof orExtra3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).
        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        revert multResultStmt. intros multResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 *
                          B2R custom_prec custom_emax x3)) as roundedValue.
        simpl in multRoundingTruth2.
        simpl in multResultStmt.
        rewrite <- multResultStmt in multRoundingTruth2.
        simpl in multRoundingTruth2.
        decompose [and] multRoundingTruth2.
        rewrite H5.
        clear H6.
        clear multRoundingTruth2.
        assert (multRoundingTruth2:= H5).
        clear H5.
        clear multResultStmt.
        clear H4.
        clear multRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear H8 f_des Heqo H14 validFloatArg1 validFloatArg2 expr1Valid expr2Valid Heqlb1 Heqlb2 Hequb1 Hequb2.
        clear floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x0 x1 x expr1 expr2.
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
                psatz R.
              }
              {
                psatz R.
              }
            }
            {
              split.
              {
                psatz R.
              }
              {
                psatz R.
              }
            }
          }
          {
            split.
            {
              destruct Rcase_abs.
              {
                psatz R.
              }
              {
                psatz R.
              }
            }
            destruct Rcase_abs.
            {
              psatz R.
            }
            {
              psatz R.
            }
          }
      }
    }
    {
      destruct H2.
    {
      unfold simpleBound3 in *.
      rewrite <- H2 in *.
      clear H2.
      simpl in *.
      destruct H0.
      destruct H2.
      destruct H3.
      destruct H4.
      destruct H5.
      destruct H6.
      destruct H7.
      destruct H7. 
      destruct H8.
      destruct H7.
      destruct H8.
      inversion Heqo.
      
      forward_reason.
      assert (floatToReal x2 = floatToReal x2).
      intuition.
      assert (floatToReal x3 = floatToReal x3).
      intuition.
      specialize (IHexpr1 (floatToReal x2) _ H0 H x2 H11 H7).
      specialize (IHexpr2 (floatToReal x3) _ H2 H1 x3 H13 H8).
      inversion H9.
      inversion H10.
      rewrite <- H14 in *.
      rewrite <- H15 in *.
       assert (floatToRealRelationForExpr1:= H14).
      assert (floatToRealRelationForExpr2:= H15).
      assert (floatToRealProof1 := H14).
      assert (floatToRealProof2 := H15).
      rewrite <- H7 in *.
      rewrite <- H8 in *.
      assert (validFloatArg1 := H9).
      assert (validFloatArg2 := H10).
      clear H11 H12 H8 H0 H2 H H1 H9 H10 H13 H15 H7.
      
      unfold float_mult in *.
      destruct f eqn:f_des.
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
         pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= (0 - ub1) * (0 - ub2))%R (ub1 < 0)%R (ub2 < 0)%R).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        pose proof orExtra3 as extraFloatMinCase.
        specialize (extraFloatMinCase  ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R)  ((floatMin <= lb1 * (0 - ub2))%R /\(lb1 >= 0)%R /\ (ub2 < 0)%R )  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R) ).
        specialize (extraFloatMinCase floatMinCase).

        pose proof diffOR as diffOR.
        specialize ( diffOR ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R) ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R)).
        apply diffOR in extraFloatMinCase.
        clear diffOR.
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((0 - lb1) * (0 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        pose proof orExtra3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2
                       ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)                     
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).

        pose proof diffOR as diffOR.
        specialize ( diffOR 
                       ((floatMin <= (0 - ub1) * (0 - ub2) /\ ub1 < 0 /\ ub2 < 0) /\ (0 - lb1) * (0 - lb2) * (1 + error) < floatMax) 
                       ((floatMin <= lb1 * lb2 /\ lb1 >= 0 /\ lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax) 
                       ((floatMin <= lb1 * (0 - ub2) /\ lb1 >= 0 /\ ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax) 
                       ((floatMin <= (0 - ub1) * lb2 /\ ub1 < 0 /\ lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax) )%R.

        

        apply diffOR in extraFloatMinCase2.
        clear diffOR.


        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        revert multResultStmt. intros multResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 *
                          B2R custom_prec custom_emax x3)) as roundedValue.
        simpl in multRoundingTruth2.
        simpl in multResultStmt.
        rewrite <- multResultStmt in multRoundingTruth2.
        simpl in multRoundingTruth2.
        decompose [and] multRoundingTruth2.
        rewrite H5.
        clear H6.
        clear multRoundingTruth2.
        assert (multRoundingTruth2:= H5).
        clear H5.
        clear multResultStmt.
        clear H4.
        clear multRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear H8 f_des H14 Heqlb1 Heqlb2 Hequb1 Hequb2 validFloatArg1 validFloatArg2 expr1Valid expr2Valid Heqo floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2 x0 x1 x x2 x3 expr1 expr2 b.
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
                psatz R.
              }
              {
                intuition.
              }
            }
            {
              split.
              {
                psatz R.
              }
              {
                intuition.
              }
            }
          }
          {
            split.
            {
              destruct Rcase_abs.
              {
                psatz R.
              }
              {
                psatz R.
              }
            }
            destruct Rcase_abs.
            {
              intuition.
            }
            {
              intuition.
            }
          }
      }
      {
         inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
         pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= (0 - ub1) * (0 - ub2))%R (ub1 < 0)%R (ub2 < 0)%R).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        pose proof orExtra3 as extraFloatMinCase.
        specialize (extraFloatMinCase  ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R)  ((floatMin <= lb1 * (0 - ub2))%R /\(lb1 >= 0)%R /\ (ub2 < 0)%R )  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R) ).
        specialize (extraFloatMinCase floatMinCase).

        pose proof diffOR as diffOR.
        specialize ( diffOR ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R) ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R)).
        apply diffOR in extraFloatMinCase.
        clear diffOR.
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((0 - lb1) * (0 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        pose proof orExtra3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2
                       ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)                     
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).

        pose proof diffOR as diffOR.
        specialize ( diffOR 
                       ((floatMin <= (0 - ub1) * (0 - ub2) /\ ub1 < 0 /\ ub2 < 0) /\ (0 - lb1) * (0 - lb2) * (1 + error) < floatMax) 
                       ((floatMin <= lb1 * lb2 /\ lb1 >= 0 /\ lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax) 
                       ((floatMin <= lb1 * (0 - ub2) /\ lb1 >= 0 /\ ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax) 
                       ((floatMin <= (0 - ub1) * lb2 /\ ub1 < 0 /\ lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax) )%R.

        

        apply diffOR in extraFloatMinCase2.
        clear diffOR.


        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        destruct multRoundingTruth2. 
        rewrite <- multResultStmt in *.
        simpl in *.
        intuition.
      }
      {
         inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
         pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= (0 - ub1) * (0 - ub2))%R (ub1 < 0)%R (ub2 < 0)%R).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        pose proof orExtra3 as extraFloatMinCase.
        specialize (extraFloatMinCase  ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R)  ((floatMin <= lb1 * (0 - ub2))%R /\(lb1 >= 0)%R /\ (ub2 < 0)%R )  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R) ).
        specialize (extraFloatMinCase floatMinCase).

        pose proof diffOR as diffOR.
        specialize ( diffOR ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R) ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R)).
        apply diffOR in extraFloatMinCase.
        clear diffOR.
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((0 - lb1) * (0 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        pose proof orExtra3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2
                       ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)                     
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).

        pose proof diffOR as diffOR.
        specialize ( diffOR 
                       ((floatMin <= (0 - ub1) * (0 - ub2) /\ ub1 < 0 /\ ub2 < 0) /\ (0 - lb1) * (0 - lb2) * (1 + error) < floatMax) 
                       ((floatMin <= lb1 * lb2 /\ lb1 >= 0 /\ lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax) 
                       ((floatMin <= lb1 * (0 - ub2) /\ lb1 >= 0 /\ ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax) 
                       ((floatMin <= (0 - ub1) * lb2 /\ ub1 < 0 /\ lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax) )%R.

        

        apply diffOR in extraFloatMinCase2.
        clear diffOR.


        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        destruct multRoundingTruth2. 
        rewrite <- multResultStmt in *.
        simpl in *.
        intuition.
      }
      {
          inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
         pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= (0 - ub1) * (0 - ub2))%R (ub1 < 0)%R (ub2 < 0)%R).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        pose proof orExtra3 as extraFloatMinCase.
        specialize (extraFloatMinCase  ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R)  ((floatMin <= lb1 * (0 - ub2))%R /\(lb1 >= 0)%R /\ (ub2 < 0)%R )  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R) ).
        specialize (extraFloatMinCase floatMinCase).

        pose proof diffOR as diffOR.
        specialize ( diffOR ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R) ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R)).
        apply diffOR in extraFloatMinCase.
        clear diffOR.
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((0 - lb1) * (0 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1 ).
        pose proof orExtra3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        Local Open Scope R_scope.
        specialize (extraFloatMinCase2
                       ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)                     
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).

        pose proof diffOR as diffOR.
        specialize ( diffOR 
                       ((floatMin <= (0 - ub1) * (0 - ub2) /\ ub1 < 0 /\ ub2 < 0) /\ (0 - lb1) * (0 - lb2) * (1 + error) < floatMax) 
                       ((floatMin <= lb1 * lb2 /\ lb1 >= 0 /\ lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax) 
                       ((floatMin <= lb1 * (0 - ub2) /\ lb1 >= 0 /\ ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax) 
                       ((floatMin <= (0 - ub1) * lb2 /\ ub1 < 0 /\ lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax) )%R.

        

        apply diffOR in extraFloatMinCase2.
        clear diffOR.


        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        revert multResultStmt. intros multResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 *
                          B2R custom_prec custom_emax x3)) as roundedValue.
        simpl in multRoundingTruth2.
        simpl in multResultStmt.
        rewrite <- multResultStmt in multRoundingTruth2.
        simpl in multRoundingTruth2.
        decompose [and] multRoundingTruth2.
        rewrite H5.
        clear H6.
        clear multRoundingTruth2.
        assert (multRoundingTruth2:= H5).
        clear H5.
        clear multResultStmt.
        clear H4.
        clear multRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear H8 f_des H14 Heqlb1 Heqlb2 Hequb1 Hequb2 validFloatArg1 validFloatArg2 expr1Valid expr2Valid Heqo floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2 x0 x1 x x2 x3 expr1 expr2.
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
                psatz R.
              }
              {
                intuition.
              }
            }
            {
              split.
              {
                psatz R.
              }
              {
                intuition.
              }
            }
          }
          {
            split.
            {
              destruct Rcase_abs.
              {
                psatz R.
              }
              {
                psatz R.
              }
            }
            destruct Rcase_abs.
            {
              intuition.
            }
            {
              intuition.
            }
          }
      }
    }  
    {
        destruct H2.
    {
      unfold simpleBound6 in *.
      rewrite <- H2 in *.
      clear H2.
      simpl in *.
      destruct H0.
      destruct H2.
      destruct H3.
      destruct H4.
      destruct H5.
      destruct H6.
      destruct H7.
      destruct H7. 
      destruct H8.
      destruct H7.
      destruct H8.
      inversion Heqo.
      
      forward_reason.
      assert (floatToReal x2 = floatToReal x2).
      intuition.
      assert (floatToReal x3 = floatToReal x3).
      intuition.
      specialize (IHexpr1 (floatToReal x2) _ H0 H x2 H11 H7).
      specialize (IHexpr2 (floatToReal x3) _ H2 H1 x3 H13 H8).
      inversion H9.
      inversion H10.
      rewrite <- H14 in *.
      rewrite <- H15 in *.
       assert (floatToRealRelationForExpr1:= H14).
      assert (floatToRealRelationForExpr2:= H15).
      assert (floatToRealProof1 := H14).
      assert (floatToRealProof2 := H15).
      rewrite <- H7 in *.
      rewrite <- H8 in *.
      assert (validFloatArg1 := H9).
      assert (validFloatArg2 := H10).
      clear H11 H12 H8 H0 H2 H H1 H9 H10 H13 H15 H7.
      
      unfold float_mult in *.
      destruct f eqn:f_des.
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
          pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= lb1 * (0 - ub2))%R (lb1 >= 0)%R  (ub2 < 0)%R ).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        
        pose proof orExtra3_3 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R) ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R)  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R)).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R) (ub1 * (0 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1).
       
        Local Open Scope R_scope.
       
        pose proof orExtra3_3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).

        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).


        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        revert multResultStmt. intros multResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 *
                          B2R custom_prec custom_emax x3)) as roundedValue.
        simpl in multRoundingTruth2.
        simpl in multResultStmt.
        rewrite <- multResultStmt in multRoundingTruth2.
        simpl in multRoundingTruth2.
        decompose [and] multRoundingTruth2.
        rewrite H5.
        clear H6.
        clear multRoundingTruth2.
        assert (multRoundingTruth2:= H5).
        clear H5.
        clear multResultStmt.
        clear H4.
        clear multRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear expr1Valid Hequb2 Heqlb2  Hequb1 Heqlb1 expr2Valid validFloatArg1 validFloatArg2 H14 f_des Heqo H8 floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x0 x1 x x2 x3 expr1 expr2 b .
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
                psatz R.
              }
              {
                intuition.
              }
            }
            {
              split.
              {
                 
                psatz R.
              }
              {
                
                psatz R.
              }
            }
          }
          {
            split.
            {
              destruct Rcase_abs.
              {
                psatz R.
              }
              {
                psatz R.
              }
            }
            {
              psatz R.
            }
          }
      }
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
          pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= lb1 * (0 - ub2))%R (lb1 >= 0)%R  (ub2 < 0)%R ).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        
        pose proof orExtra3_3 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R) ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R)  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R)).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R) (ub1 * (0 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1).
       
        Local Open Scope R_scope.
       
        pose proof orExtra3_3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).

        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).


        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        destruct multRoundingTruth2.
        rewrite <- multResultStmt in *.
        simpl in *.
        intuition.
      }
      {
         inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
          pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= lb1 * (0 - ub2))%R (lb1 >= 0)%R  (ub2 < 0)%R ).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        
        pose proof orExtra3_3 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R) ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R)  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R)).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R) (ub1 * (0 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1).
       
        Local Open Scope R_scope.
       
        pose proof orExtra3_3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).

        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).


        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        destruct multRoundingTruth2.
        rewrite <- multResultStmt in *.
        simpl in *.
        intuition.
      }
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
          pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= lb1 * (0 - ub2))%R (lb1 >= 0)%R  (ub2 < 0)%R ).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        
        pose proof orExtra3_3 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R) ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R)  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R)).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R) (ub1 * (0 - lb2) * (1 + error) < floatMax)%R floatMinCase floatMaxBound1).
       
        Local Open Scope R_scope.
       
        pose proof orExtra3_3 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).

        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).


        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        revert multResultStmt. intros multResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 *
                          B2R custom_prec custom_emax x3)) as roundedValue.
        simpl in multRoundingTruth2.
        simpl in multResultStmt.
        rewrite <- multResultStmt in multRoundingTruth2.
        simpl in multRoundingTruth2.
        decompose [and] multRoundingTruth2.
        rewrite H5.
        clear H6.
        clear multRoundingTruth2.
        assert (multRoundingTruth2:= H5).
        clear H5.
        clear multResultStmt.
        clear H4.
        clear multRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear expr1Valid Hequb2 Heqlb2  Hequb1 Heqlb1 expr2Valid validFloatArg1 validFloatArg2 H14 f_des Heqo H8 floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x0 x1 x x2 x3 expr1 expr2 .
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
                psatz R.
              }
              {
                intuition.
              }
            }
            {
              split.
              {
                 
                psatz R.
              }
              {
                
                psatz R.
              }
            }
          }
          {
            split.
            {
              destruct Rcase_abs.
              {
                psatz R.
              }
              {
                psatz R.
              }
            }
            {
              psatz R.
            }
          }
      }
    }
    {
          destruct H2.
    {
      unfold simpleBound6 in *.
      rewrite <- H2 in *.
      clear H2.
      simpl in *.
      destruct H0.
      destruct H2.
      destruct H3.
      destruct H4.
      destruct H5.
      destruct H6.
      destruct H7.
      destruct H7. 
      destruct H8.
      destruct H7.
      destruct H8.
      inversion Heqo.
      
      forward_reason.
      assert (floatToReal x2 = floatToReal x2).
      intuition.
      assert (floatToReal x3 = floatToReal x3).
      intuition.
      specialize (IHexpr1 (floatToReal x2) _ H0 H x2 H11 H7).
      specialize (IHexpr2 (floatToReal x3) _ H2 H1 x3 H13 H8).
      inversion H9.
      inversion H10.
      rewrite <- H14 in *.
      rewrite <- H15 in *.
       assert (floatToRealRelationForExpr1:= H14).
      assert (floatToRealRelationForExpr2:= H15).
      assert (floatToRealProof1 := H14).
      assert (floatToRealProof2 := H15).
      rewrite <- H7 in *.
      rewrite <- H8 in *.
      assert (validFloatArg1 := H9).
      assert (validFloatArg2 := H10).
      clear H11 H12 H8 H0 H2 H H1 H9 H10 H13 H15 H7.
      
      unfold float_mult in *.
      destruct f eqn:f_des.
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
          pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= (0 - ub1) * lb2)%R (ub1 < 0)%R (lb2 >= 0)%R ).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
        Lemma orExtra3_4 : forall p1 p2 p3 p4: Prop, p4 -> p1 \/ p2 \/ p3 \/ p4.
          intros; intuition. Qed.
        pose proof orExtra3_4 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R) ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R)  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R)).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R) ((0 - lb1) * ub2 * (1 + error) < floatMax)%R floatMinCase floatMaxBound1).
       
        Local Open Scope R_scope.

        pose proof orExtra3_4 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).

        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).


        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        revert multResultStmt. intros multResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 *
                          B2R custom_prec custom_emax x3)) as roundedValue.
        simpl in multRoundingTruth2.
        simpl in multResultStmt.
        rewrite <- multResultStmt in multRoundingTruth2.
        simpl in multRoundingTruth2.
        decompose [and] multRoundingTruth2.
        rewrite H5.
        clear H6.
        clear multRoundingTruth2.
        assert (multRoundingTruth2:= H5).
        clear H5.
        clear multResultStmt.
        clear H4.
        clear multRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear H14 H8 validFloatArg1 validFloatArg2 expr1Valid expr2Valid Heqlb1 Hequb1 Heqlb2 Hequb2 f_des Heqo floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x0 x1 x x2 x3 expr1 expr2 b.
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
                psatz R.
              }
              {
                psatz R.
              }
            }
            {
              split.
              {
                psatz R.
              }
              {
                psatz R.
              }
            }
          }
          {
            split.
            {
              destruct Rcase_abs.
              psatz R.
              psatz R.
            }
            {
              destruct Rcase_abs.
              psatz R.
              psatz R.
            }
          }
      }
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
          pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= (0 - ub1) * lb2)%R (ub1 < 0)%R (lb2 >= 0)%R ).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
       
        pose proof orExtra3_4 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R) ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R)  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R)).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R) ((0 - lb1) * ub2 * (1 + error) < floatMax)%R floatMinCase floatMaxBound1).
       
        Local Open Scope R_scope.

        pose proof orExtra3_4 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).

        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).


        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        destruct multRoundingTruth2.
        rewrite <- multResultStmt in *.
        simpl in *.
        intuition.
      }
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
          pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= (0 - ub1) * lb2)%R (ub1 < 0)%R (lb2 >= 0)%R ).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
       
        pose proof orExtra3_4 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R) ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R)  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R)).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R) ((0 - lb1) * ub2 * (1 + error) < floatMax)%R floatMinCase floatMaxBound1).
       
        Local Open Scope R_scope.

        pose proof orExtra3_4 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).

        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).


        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        destruct multRoundingTruth2.
        rewrite <- multResultStmt in *.
        simpl in *.
        intuition.
      }
      {
        inversion Heqo0.
        simpl in *.
        inversion Heqo.
        unfold lofst in *.
        destruct IHexpr1.
        destruct IHexpr2.
        assert (expr1Valid := H2).
        assert (expr2Valid := H8).
        assert (expr1Bound := H0).
        assert (expr2Bound := H7).
        assert (floatMinCase := H3).
        assert (floatMaxBound1 := H4). 
        assert (resultGe1 := H5).
        assert (resultGe2 := H6).
        assert (multResultStmt := H1).
        clear H2 H7 H0 H6 H3 H4 H5 H1.
        pose proof relErrorBasedOnFloatMinTruthMult as relErrorBasedOnFloatMinTruthMult.
        remember (lb x0 fState) as lb1.
        remember (lb x1 fState) as lb2.
        remember (ub x0 fState) as ub1.
        remember (ub x1 fState) as ub2.
        specialize (relErrorBasedOnFloatMinTruthMult x4 x5 lb1 lb2 ub1 ub2 ).
        
        destruct expr1Bound.
        destruct expr2Bound.
        pose proof or_introl.
          pose proof conjoin2 as conjoin2.
        specialize (conjoin2 (floatMin <= (0 - ub1) * lb2)%R (ub1 < 0)%R (lb2 >= 0)%R ).
        specialize (conjoin2 floatMinCase resultGe1 resultGe2).
        clear floatMinCase.
        assert (floatMinCase:=conjoin2).
        clear conjoin2.
        intros.
      
        pose proof orExtra3_4 as extraFloatMinCase.
        specialize (extraFloatMinCase ((floatMin <= lb1 * lb2)%R /\ (lb1 >= 0)%R /\ (lb2 >= 0)%R) ((floatMin <= (0 - ub1) * (0 - ub2))%R /\ (ub1 < 0)%R /\ (ub2 < 0)%R) ((floatMin <= lb1 * (0 - ub2))%R /\ (lb1 >= 0)%R /\ (ub2 < 0)%R)  ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R)).
        specialize (extraFloatMinCase floatMinCase).
        specialize (relErrorBasedOnFloatMinTruthMult extraFloatMinCase H0 H2 H1 H3).
        pose proof multRoundingTruth as multRoundingTruth.
        intros.
        pose proof andExtra as andExtra.
         intros.
        specialize (andExtra ((floatMin <= (0 - ub1) * lb2)%R /\ (ub1 < 0)%R /\ (lb2 >= 0)%R) ((0 - lb1) * ub2 * (1 + error) < floatMax)%R floatMinCase floatMaxBound1).
       
        Local Open Scope R_scope.

        pose proof orExtra3_4 as extraFloatMinCase2.
        simpl in andExtra.
        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2
                      ((floatMin <= lb1 * lb2 /\
                        lb1 >= 0 /\
                        lb2 >= 0) /\ ub1 * ub2 * (1 + error) < floatMax)
                      ((floatMin <= (0 - ub1) * (0 - ub2) /\
                      ub1 < 0 /\
                      ub2 < 0) /\
                      (0 - lb1) * (0 - lb2) * (1 + error) < floatMax)
                      ((floatMin <= lb1 * (0 - ub2) /\
                      lb1 >= 0 /\
                      ub2 < 0) /\ ub1 * (0 - lb2) * (1 + error) < floatMax)
                      (( floatMin <= (0 - ub1) * lb2 /\
                      ub1 < 0 /\
                      lb2 >= 0) /\ (0 - lb1) * ub2 * (1 + error) < floatMax)).

        simpl in extraFloatMinCase2.
        specialize (extraFloatMinCase2 andExtra).


        specialize (multRoundingTruth x2 x3 lb1 lb2 ub1 ub2 x4 x5 floatToRealProof1 floatToRealProof2 extraFloatMinCase2 H0 H2 H1 H3).
        pose proof multRoundingTruth2 as multRoundingTruth2.
        specialize (multRoundingTruth2 x2 x3 x4 x5 floatToRealProof1 floatToRealProof2 multRoundingTruth).
        revert multResultStmt. intros multResultStmt.
        apply validFloat2 in floatToRealProof1.
        apply validFloat2 in floatToRealProof2.
        rewrite floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        remember ( round radix2
                         (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                         (round_mode mode_NE)
                         (B2R custom_prec custom_emax x2 *
                          B2R custom_prec custom_emax x3)) as roundedValue.
        simpl in multRoundingTruth2.
        simpl in multResultStmt.
        rewrite <- multResultStmt in multRoundingTruth2.
        simpl in multRoundingTruth2.
        decompose [and] multRoundingTruth2.
        rewrite H5.
        clear H6.
        clear multRoundingTruth2.
        assert (multRoundingTruth2:= H5).
        clear H5.
        clear multResultStmt.
        clear H4.
        clear multRoundingTruth.
        rewrite <- floatToRealProof2 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof1 in relErrorBasedOnFloatMinTruthMult.
        rewrite <- floatToRealProof2 in HeqroundedValue.
        rewrite <- floatToRealProof1 in HeqroundedValue.
        pose proof errorGt0.
        clear H14 H8 H validFloatArg1 validFloatArg2 expr1Valid expr2Valid Heqlb1 Hequb1 Heqlb2 Hequb2 f_des Heqo floatMinCase floatMaxBound1 HeqroundedValue multRoundingTruth2 floatToRealRelationForExpr1 floatToRealRelationForExpr2 floatToRealProof1 floatToRealProof2  x0 x1 x x2 x3 expr1 expr2 b Heqo0.
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
                psatz R.
              }
              {
                psatz R.
              }
            }
            {
              split.
              {
                psatz R.
              }
              {
                psatz R.
              }
            }
          }
          {
            split.
            {
              destruct Rcase_abs.
              psatz R.
              psatz R.
            }
            {
              destruct Rcase_abs.
              psatz R.
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
    }
    }
Qed.
