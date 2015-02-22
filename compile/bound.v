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

  map (fun triple2  =>  simpleBoundFunc triple triple2 combFunc (premise triple /\ premise triple2 /\ fla)) list. 


Definition foldListwithList 
           (list1 list2: list singleBoundTerm) 
           (combFunc:Term->Term->Term) 
           (fla:Formula) 
           (simpleBoundFunc : singleBoundTerm -> 
                              singleBoundTerm -> 
                              (Term->Term->Term) -> 
                              Formula -> 
                              singleBoundTerm ): list singleBoundTerm :=
 
  fold_right  (fun triple list => list ++ (mapBoundListWithTriple list1 triple combFunc fla simpleBoundFunc)) List.nil list2.

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
 Lemma tlaToSourceRelation:
   forall (tlaExpr:NowTerm) fState tr, (forall x y, fstate_lookup fState x = Some y ->
                                                    Some ((Semantics.hd tr) x) = floatToReal y) ->  eval_formula ((denowify tlaExpr) > 0) tr->
                                       (match eval_NowTerm fState (tlaExpr) with 
                                          | Some f => match (floatToReal f) with
                                                        | Some num => (num > 0)%R
                                                        | None => True
                                                      end
                                          | None => True
                                        end).
   intros.
   
   destruct (eval_NowTerm fState tlaExpr) eqn:eval_Nowterm_des.                 
   + unfold eval_NowTerm.
     induction tlaExpr.
     unfold floatToReal.
     destruct f eqn:f_des.
     * simpl in *.
       specialize (H v f).
       rewrite f_des in H.
       unfold Semantics.eval_comp in H0.
       simpl in H0.
       apply H in eval_Nowterm_des.
       remember (hd tr v) as num1.
       admit.
     * intuition.  
     * intuition.
     * admit.
     * admit.
     * destruct f eqn:f_des.
       simpl in *. 
       unfold Semantics.eval_comp in *.
       simpl in *.
       inversion eval_Nowterm_des.
       rewrite H2 in H0.
       simpl in *.
       apply H0.
       simpl in *.
       intuition.
       simpl in *.
       intuition.
       simpl in *.
       inversion eval_Nowterm_des.
       unfold Semantics.eval_comp in *.
       simpl in *.
       rewrite H2 in H0.
       simpl in H0.
       apply H0.
     * destruct f eqn:f_des.
       simpl in *.
       unfold Semantics.eval_comp in *.
       simpl in *.
       remember  (eval_term (denowify tlaExpr1) (hd tr) (hd (tl tr))) as num1.
       remember  (eval_term (denowify tlaExpr2) (hd tr) (hd (tl tr))) as num2.
                               

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
  clear Heqeval_expr1 Heqeval_expr2.
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
induction expr1_boundList as [ | Iexpr1_bound].
  + induction expr2_boundList as [| Iexpr2_bound].
    * simpl in *.
      intuition.
    * simpl in *.
      unfold plusBound.
      unfold foldListwithList.
      unfold mapBoundListWithTriple.
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
         unfold foldListwithList in *.
         unfold mapBoundListWithTriple in *.
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
         destruct eval_expr1 eqn: eval_expr1_des.
         -  destruct eval_expr2 eqn: eval_expr2_des.
            + specialize (bplusCorrect custom_prec custom_emax eq_refl eq_refl Floats.Float.binop_pl mode_NE f f0).  (*proving it for the round to nearest case*) 
              unfold floatToReal in *.
              unfold lift2 in *.
              revert IHexpr2' IHexpr1'.
              intros IHexpr2' IHexpr1'.
              destruct f eqn:f_des.
              * destruct f0 eqn:f0_des.
                {
                  unfold Bplus in *.
                  destruct Bool.eqb.
                  - simpl.
                    simpl in IHexpr1'.
                    simpl in IHexpr2'.
                    apply fold_right_two_list in IHexpr2'.
                    apply fold_right_two_list in IHexpr1'.
                    apply fold_right_two_list_opp.
                    split. (*Ltac this full thing*)
                    + apply fold_right_two_list_opp.
                      split.
                      * decompose [and] IHexpr2'.
                        intuition.
                      * apply fold_right_combine.
                        split.
                        decompose [and] IHexpr1'.
                        apply fold_right_inferr_sublist in H.
                        decompose [and] H.
                        intuition.
                        simpl.
                        clear  fold_right_inferring_sublist_truth_from_list_truth IHexpr1_boundList IHexpr2_boundList Heqexpr1_boundList Heqexpr2_boundList.
                        revert IHexpr1 IHexpr2. intros IHexpr1 IHexpr2.
                        decompose [and] IHexpr1.
                        decompose [and] IHexpr2.
                        simpl in H0.
                        simpl in H2.
                        intros premGt0. 
                        decompose [and] premGt0.
                        apply H0 in H5.
                        apply H2 in H3.
                        remember  (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1.
                        remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1.
                        remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2.
                        remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2.
                        clear HeqIexpr1Andexpr1Withexpr2Gt0 Iexpr1Andexpr1Withexpr2Gt0 Iexpr2Withexpr1Gt0  HeqIexpr2Withexpr1Gt0  Iexpr1Andexp1Withexpr2Lt0  HeqIexpr1Andexp1Withexpr2Lt0  Iexpr2Withexpr1Lt0  HeqIexpr2Withexpr1Lt0 Heqexpr1Withexpr2Gt0  Heqexpr1WithExpr2Lt0 bplusCorrect IHexpr2'  IHexpr1' Heqlb2  Hequb2 IHexpr1  Heqlb1  Hequb1  Hequb1  H H0 H1 H2 H6 IHexpr2 premGt0 expr1WithExpr2Lt0  expr1Withexpr2Gt0 expr1Withexpr2Gt0 eval_expr1 eval_expr2  eval_expr2_des eval_expr1_des Iexpr1_bound Iexpr2_bound f2RPremise  expr1_boundList  expr2_boundList f0_des  f_des expr1 expr2 fState f b f0 .
                        unfold error.
                        simpl in *.
                        psatz R.
                    + apply fold_right_two_list_opp.
                      split.
                      * decompose [and] IHexpr2'.
                        intuition.
                      * apply fold_right_combine.
                        split.
                        decompose [and] IHexpr1'.
                        assert (H0':=H0).
                        assert (H':=H).
                        clear H H0.
                        assert (H:=H0').
                        assert (H0:=H').
                        apply fold_right_inferr_sublist in H.
                        decompose [and] H.
                        intuition.
                        simpl.
                        clear fold_right_inferring_sublist_truth_from_list_truth IHexpr1_boundList IHexpr2_boundList Heqexpr1_boundList Heqexpr2_boundList.
                        revert IHexpr1 IHexpr2. intros IHexpr1 IHexpr2.
                        decompose [and] IHexpr1.
                        decompose [and] IHexpr2.
                        simpl in H0.
                        simpl in H2.
                        intros premGt0. 
                        decompose [and] premGt0.
                        apply H0 in H5.
                        apply H2 in H3.
                        remember  (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1.
                        remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1.
                        remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2.
                        remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2.
                        clear HeqIexpr1Andexpr1Withexpr2Gt0 Iexpr1Andexpr1Withexpr2Gt0 Iexpr2Withexpr1Gt0  HeqIexpr2Withexpr1Gt0  Iexpr1Andexp1Withexpr2Lt0  HeqIexpr1Andexp1Withexpr2Lt0  Iexpr2Withexpr1Lt0  HeqIexpr2Withexpr1Lt0 Heqexpr1Withexpr2Gt0  Heqexpr1WithExpr2Lt0 bplusCorrect IHexpr2'  IHexpr1' Heqlb2  Hequb2 IHexpr1  Heqlb1  Hequb1  Hequb1  H H0 H1 H2 H6 IHexpr2 premGt0 expr1WithExpr2Lt0  expr1Withexpr2Gt0 expr1Withexpr2Gt0 eval_expr1 eval_expr2  eval_expr2_des eval_expr1_des Iexpr1_bound Iexpr2_bound f2RPremise  expr1_boundList  expr2_boundList f0_des  f_des expr1 expr2 fState f b f0 .
                        unfold error.
                        simpl in *.
                        psatz R.
                  -  simpl.
                     simpl in IHexpr1'.
                     simpl in IHexpr2'.
                     apply fold_right_two_list in IHexpr2'.
                     apply fold_right_two_list in IHexpr1'.
                     apply fold_right_two_list_opp.
                     split. (*Ltac this full thing*) 
                     +  apply fold_right_two_list_opp.
                        split.
                        * decompose [and] IHexpr2'.
                          intuition.
                        * apply fold_right_combine.
                          split.
                          decompose [and] IHexpr1'.
                          apply fold_right_inferr_sublist in H.
                          decompose [and] H.
                          intuition.
                          simpl.
                          clear  fold_right_inferring_sublist_truth_from_list_truth IHexpr1_boundList IHexpr2_boundList Heqexpr1_boundList Heqexpr2_boundList.
                          revert IHexpr1 IHexpr2. intros IHexpr1 IHexpr2.
                          decompose [and] IHexpr1.
                          decompose [and] IHexpr2.
                          simpl in H0.
                          simpl in H2.
                          intros premGt0. 
                          decompose [and] premGt0.
                          apply H0 in H5.
                          apply H2 in H3.
                          remember  (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1.
                          remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1.
                          remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2.
                          remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2.
                          clear HeqIexpr1Andexpr1Withexpr2Gt0 Iexpr1Andexpr1Withexpr2Gt0 Iexpr2Withexpr1Gt0  HeqIexpr2Withexpr1Gt0  Iexpr1Andexp1Withexpr2Lt0  HeqIexpr1Andexp1Withexpr2Lt0  Iexpr2Withexpr1Lt0  HeqIexpr2Withexpr1Lt0 Heqexpr1Withexpr2Gt0  Heqexpr1WithExpr2Lt0 bplusCorrect IHexpr2'  IHexpr1' Heqlb2  Hequb2 IHexpr1  Heqlb1  Hequb1  Hequb1  H H0 H1 H2 H6 IHexpr2 premGt0 expr1WithExpr2Lt0  expr1Withexpr2Gt0 expr1Withexpr2Gt0 eval_expr1 eval_expr2  eval_expr2_des eval_expr1_des Iexpr1_bound Iexpr2_bound f2RPremise  expr1_boundList  expr2_boundList f0_des  f_des expr1 expr2 fState f b f0 .
                          unfold error.
                          simpl in *.
                          psatz R.
                          
                     +  apply fold_right_two_list_opp.
                        split.
                        * decompose [and] IHexpr2'.
                          intuition.
                        * apply fold_right_combine.
                          split.
                          decompose [and] IHexpr1'.
                          assert (H0':=H0).
                          assert (H':=H).
                          clear H H0.
                          assert (H:=H0').
                          assert (H0:=H').
                          apply fold_right_inferr_sublist in H.
                          decompose [and] H.
                          intuition.
                          simpl.
                          clear fold_right_inferring_sublist_truth_from_list_truth IHexpr1_boundList IHexpr2_boundList Heqexpr1_boundList Heqexpr2_boundList.
                          revert IHexpr1 IHexpr2. intros IHexpr1 IHexpr2.
                          decompose [and] IHexpr1.
                          decompose [and] IHexpr2.
                          simpl in H0.
                          simpl in H2.
                          intros premGt0. 
                          decompose [and] premGt0.
                          apply H0 in H5.
                          apply H2 in H3.
                          remember  (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1.
                          remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1.
                          remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2.
                          remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2.
                          clear HeqIexpr1Andexpr1Withexpr2Gt0 Iexpr1Andexpr1Withexpr2Gt0 Iexpr2Withexpr1Gt0  HeqIexpr2Withexpr1Gt0  Iexpr1Andexp1Withexpr2Lt0  HeqIexpr1Andexp1Withexpr2Lt0  Iexpr2Withexpr1Lt0  HeqIexpr2Withexpr1Lt0 Heqexpr1Withexpr2Gt0  Heqexpr1WithExpr2Lt0 bplusCorrect IHexpr2'  IHexpr1' Heqlb2  Hequb2 IHexpr1  Heqlb1  Hequb1  Hequb1  H H0 H1 H2 H6 IHexpr2 premGt0 expr1WithExpr2Lt0  expr1Withexpr2Gt0 expr1Withexpr2Gt0 eval_expr1 eval_expr2  eval_expr2_des eval_expr1_des Iexpr1_bound Iexpr2_bound f2RPremise  expr1_boundList  expr2_boundList f0_des  f_des expr1 expr2 fState f b f0 .
                          unfold error.
                          simpl in *.
                          psatz R.
                }
                {    unfold Bplus in *. 
                     rewrite fold_right_truth.
                     intuition.
                }
                {
                  unfold Bplus in *.
                  rewrite fold_right_truth.
                  intuition.
                }
                {
                   unfold Bplus in *.
                   simpl.
                   simpl in IHexpr1'.
                   simpl in IHexpr2'.
                   apply fold_right_two_list in IHexpr2'.
                   apply fold_right_two_list in IHexpr1'.
                   apply fold_right_two_list_opp.
                   split. (*Ltac this full thing*)
                   + apply fold_right_two_list_opp.
                     split.
                     * decompose [and] IHexpr2'.
                       intuition.
                     * apply fold_right_combine.
                       split.
                       decompose [and] IHexpr1'.
                       apply fold_right_inferr_sublist in H.
                       decompose [and] H.
                       intuition.
                       simpl.
                       clear  fold_right_inferring_sublist_truth_from_list_truth IHexpr1_boundList IHexpr2_boundList Heqexpr1_boundList Heqexpr2_boundList.
                       revert IHexpr1 IHexpr2. intros IHexpr1 IHexpr2.
                       decompose [and] IHexpr1.
                       decompose [and] IHexpr2.
                       simpl in H0.
                       simpl in H2.
                       intros premGt0. 
                       decompose [and] premGt0.
                       apply H0 in H5.
                       apply H2 in H3.
                       remember  (eval_term (lb Iexpr2_bound) (hd tr) (hd (tl tr))) as lb1.
                       remember (eval_term (ub Iexpr2_bound) (hd tr) (hd (tl tr))) as ub1.
                       remember (eval_term (lb Iexpr1_bound) (hd tr) (hd (tl tr))) as lb2.
                       remember (eval_term (ub Iexpr1_bound) (hd tr) (hd (tl tr))) as ub2.
                       clear HeqIexpr1Andexpr1Withexpr2Gt0 Iexpr1Andexpr1Withexpr2Gt0 Iexpr2Withexpr1Gt0  HeqIexpr2Withexpr1Gt0  Iexpr1Andexp1Withexpr2Lt0  HeqIexpr1Andexp1Withexpr2Lt0  Iexpr2Withexpr1Lt0  HeqIexpr2Withexpr1Lt0 Heqexpr1Withexpr2Gt0  Heqexpr1WithExpr2Lt0
bplusCorrect IHexpr2'  IHexpr1' Heqlb2  Hequb2 IHexpr1  Heqlb1  Hequb1 Hequb1  H H0 H1 H2 H6 IHexpr2  expr1WithExpr2Lt0  expr1Withexpr2Gt0 expr1Withexpr2Gt0  eval_expr2_des eval_expr1_des f2RPremise  expr1_boundList  expr2_boundList f0_des  f_des  fState f b f0 .
                       unfold error.
                       simpl in *.
                       remember ( F2R {| Fnum := cond_Zopp b0 (Z.pos m); Fexp := e |}) as num.
                       clear Heqnum.
                      (*proof done till here*)
                       Admitted.
