Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Ranalysis1.
Require Import String.
Require Import List.

Section DiffDynLogic.
(* The syntax of differential dynamic logic. *)

(*Definition StVar := string.
Definition StVar_eqdec x1 x2 := string_dec x1 x2.*)
Variable StVar : Set.
Variable StVar_eqdec : forall (x1 x2:StVar), {x1 = x2} + {x1 <> x2}.

(* Real-valued Terms *)
Inductive Term :=
| SVar : StVar -> Term
| Real : R -> Term
| Plus : Term -> Term -> Term
| Minus : Term -> Term -> Term
| Times : Term -> Term -> Term
| Divide : Term -> Term -> Term.

(* First order logical formulas *)
Inductive FOL :=
| Leq : Term -> Term -> FOL
| Lt : Term -> Term -> FOL
| Geq : Term -> Term -> FOL
| Gt : Term -> Term -> FOL
| Neg : FOL -> FOL
| And : FOL -> FOL -> FOL
| Or : FOL -> FOL -> FOL
| Imp : FOL -> FOL -> FOL
| Forall : StVar -> FOL -> FOL
| Exists : StVar -> FOL -> FOL.

Inductive HybridProg :=
| Assign : StVar -> Term -> HybridProg
| NonDetAssign : StVar -> HybridProg
(* TODO restrict list to contain only unique StVars.
   Dependent types or separate checking function?*)
| DiffEq : list (StVar * Term) -> FOL -> HybridProg
| Pred : FOL -> HybridProg
| Union : HybridProg -> HybridProg -> HybridProg
| Seq : HybridProg -> HybridProg -> HybridProg
| Rep : HybridProg -> HybridProg.

Inductive Formula :=
| LeqDL : Term -> Term -> Formula
| LtDL : Term -> Term -> Formula
| GeqDL : Term -> Term -> Formula
| GtDL : Term -> Term -> Formula
| NegDL : Formula -> Formula
| AndDL : Formula -> Formula -> Formula
| OrDL : Formula -> Formula -> Formula
| ImpDL : Formula -> Formula -> Formula
| ForallDL : StVar -> Formula -> Formula
| ExistsDL : StVar -> Formula -> Formula
| ForallProg : HybridProg -> Formula -> Formula
| ExistsProg : HybridProg -> Formula -> Formula.

Fixpoint fol_to_formula (f:FOL) : Formula :=
  match f with
  | Leq t1 t2 => LeqDL t1 t2
  | Lt t1 t2 => LtDL t1 t2
  | Geq t1 t2 => GeqDL t1 t2
  | Gt t1 t2 => GtDL t1 t2
  | Neg f' => fol_to_formula f'
  | And f1 f2 => AndDL (fol_to_formula f1) (fol_to_formula f2)
  | Or f1 f2 => OrDL (fol_to_formula f1) (fol_to_formula f2)
  | Imp f1 f2 => ImpDL (fol_to_formula f1) (fol_to_formula f2)
  | Forall x f' => ForallDL x (fol_to_formula f')
  | Exists x f' => ExistsDL x (fol_to_formula f')
  end.

Definition state := StVar -> R.

(* The semantics of differential dynamic logic. *)

Open Scope R_scope.

Fixpoint eval_term (t:Term) (st:state) : R :=
  match t with
  | SVar x => st x
  | Real r => r
  | Plus t1 t2 => (eval_term t1 st) + (eval_term t2 st)
  | Minus t1 t2 => (eval_term t1 st) - (eval_term t2 st)
  | Times t1 t2 => (eval_term t1 st) * (eval_term t2 st)
  | Divide t1 t2 => (eval_term t1 st) / (eval_term t2 st)
  end.

Fixpoint eval_fol (f:FOL) (st:state) : Prop :=
  match f with
  | Leq t1 t2   => eval_term t1 st <= eval_term t2 st
  | Lt t1 t2    => eval_term t1 st <  eval_term t2 st
  | Geq t1 t2   => eval_term t1 st >= eval_term t2 st
  | Gt t1 t2    => eval_term t1 st >  eval_term t2 st
  | Neg f'      => ~eval_fol f' st
  | And f1 f2   => eval_fol f1 st /\ eval_fol f2 st
  | Or f1 f2    => eval_fol f1 st \/ eval_fol f2 st
  | Imp f1 f2   => eval_fol f1 st -> eval_fol f2 st
  | Forall x f' => forall v,
                     eval_fol f'
                              (fun y =>
                                 if StVar_eqdec x y
                                 then v
                                 else st y)
  | Exists x f' => exists v, eval_fol f'
                                      (fun y =>
                                         if StVar_eqdec x y
                                         then v
                                         else st y)
  end.

Inductive Transition :
  HybridProg -> state -> state -> Prop :=
| Discrete : forall s1 s2 x t,
   s2 x = eval_term t s1 ->
   (forall y, y <> x -> s1 y = s2 y) ->
   Transition (Assign x t) s1 s2
| DiscreteNonDet : forall s1 s2 x r,
   s2 x = r ->
   (forall y, y <> x -> s1 y = s2 y) ->
   Transition (NonDetAssign x) s1 s2
| Continuous : forall s1 s2 diffeqs pred f r,
   f R0 = s1 -> f r = s2 ->
   (* TODO f is continuous on [0,r] *)
   (* f respects the derivative *)
   (forall x d pr,
      In (x, d) diffeqs ->
      forall z, R0 < z < r ->
        derive (fun w => eval_term (SVar x) (f w)) pr z =
        eval_term d (f z)) ->
   (* f does not change other variables *)
   (forall x d,
      ~In (x, d) diffeqs ->
      forall z, R0 < z < r ->
        eval_term (SVar x) (f z) = s1 x) ->
   (* f respects pred *)
   (forall z, R0 < z < r -> eval_fol pred (f z)) ->
   Transition (DiffEq diffeqs pred) s1 s2
| TestTrans : forall s pred,
   eval_fol pred s ->
   Transition (Pred pred) s s
| Union1 : forall s1 s2 p1 p2,
   Transition p1 s1 s2 ->
   Transition (Union p1 p2) s1 s2
| Union2 : forall s1 s2 p1 p2,
   Transition p2 s1 s2 ->
   Transition (Union p1 p2) s1 s2
| SeqTrans : forall s1 s2 s3 p1 p2,
   Transition p1 s1 s2 ->
   Transition p2 s2 s3 ->
   Transition (Seq p1 p2) s1 s3
| Rep0 : forall s p,
   Transition (Rep p) s s
| RepN : forall s1 s2 s3 p,
   Transition p s1 s2 ->
   Transition (Rep p) s2 s3 ->
   Transition (Rep p) s1 s3.

Fixpoint eval_formula (f:Formula) (st:state) : Prop :=
  match f with
  | LeqDL t1 t2   => eval_term t1 st <= eval_term t2 st
  | LtDL t1 t2    => eval_term t1 st <  eval_term t2 st
  | GeqDL t1 t2   => eval_term t1 st >= eval_term t2 st
  | GtDL t1 t2    => eval_term t1 st >  eval_term t2 st
  | NegDL f'      => ~eval_formula f' st
  | AndDL f1 f2   => eval_formula f1 st /\ eval_formula f2 st
  | OrDL f1 f2    => eval_formula f1 st \/ eval_formula f2 st
  | ImpDL f1 f2   => eval_formula f1 st -> eval_formula f2 st
  | ForallDL x f' => forall v,
                     eval_formula f'
                              (fun y =>
                                 if StVar_eqdec x y
                                 then v
                                 else st y)
  | ExistsDL x f' => exists v, eval_formula f'
                                      (fun y =>
                                         if StVar_eqdec x y
                                         then v
                                         else st y)
  | ForallProg p f' => forall st',
     Transition p st st' ->
     eval_formula f' st'
  | ExistsProg p f' => exists st',
     Transition p st st' /\
     eval_formula f' st'
  end.

Close Scope R_scope.

End DiffDynLogic.

Definition Var := string.

(* Some notation for the logic. *)
(*Term notation *)
Notation " ` a " := (SVar Var a) (at level 10) : HP_scope.
Notation "0" := (Real Var (INR 0)) (at level 10) : HP_scope.
Notation "1" := (Real Var (INR 1)) (at level 10) : HP_scope.
Notation "2" := (Real Var (INR 2)) (at level 10) : HP_scope.
Notation "3" := (Real Var (INR 3)) (at level 10) : HP_scope.
Notation "4" := (Real Var (INR 4)) (at level 10) : HP_scope.
Infix "+" := (Plus Var) : HP_scope.
Infix "-" := (Minus Var) : HP_scope.
Open Scope HP_scope.
(* Need to open scope so that 0 is recognized as (Nat 0) *)
Notation "-- x" := (0 - x) (at level 9) : HP_scope.
Close Scope HP_scope.
Infix "*" := (Times Var) : HP_scope.
Infix "/" := (Divide Var) : HP_scope.

Check Leq.
(* FOL notation *)
Infix "<=" := (Leq Var) : HP_scope.
Infix "<" := (Lt Var) : HP_scope.
Infix ">=" := (Geq Var) : HP_scope.
Infix ">" := (Gt Var) : HP_scope.
Notation "! f" := (Neg Var f) (at level 10) : HP_scope.
Infix "/\" := (And Var) : HP_scope.
Infix "\/" := (Or Var) : HP_scope.
Notation "f1 --> f2" := (Imp Var f1 f2) (at level 11) : HP_scope.
Notation "\A x , f" := (Forall Var x f) (at level 10) : HP_scope.
Notation "\E x , f" := (Exists Var x f) (at level 10) : HP_scope.
Notation "x == y" :=
  (And Var (Leq Var x y) (Geq Var x y)) (at level 10)
  : HP_scope.

(* HybridProg notation *)
Notation "x ::= t" := (Assign Var x t) (at level 10) : HP_scope.
Notation "x ::= *" := (NonDetAssign Var x) (at level 10) : HP_scope.
Notation "x ' ::= t" := (x, t) (at level 10) : HP_scope.
Notation "[ x1 , .. , xn ]" := (cons x1 .. (cons xn nil) .. )
                                 (at level 10) : HP_scope.
Notation "eqs & f" := (DiffEq Var eqs f) (at level 10) : HP_scope.
Notation "? pred" := (Pred Var pred) (at level 10) : HP_scope.
Notation "p1 '|||' p2" := (Union Var p1 p2) (at level 11)
                          : HP_scope.
Notation "p1 ; p2" := (Seq Var p1 p2) (at level 11) : HP_scope.
Notation "p **" := (Rep Var p) (at level 10) : HP_scope.

(* Formula notation *)
Infix "<=" := (LeqDL Var) : DL_scope.
Infix "<" := (LtDL Var) : DL_scope.
Infix ">=" := (GeqDL Var) : DL_scope.
Infix ">" := (GtDL Var) : DL_scope.
Notation "! f" := (NegDL Var f) (at level 10) : DL_scope.
Infix "/\" := (AndDL Var) : DL_scope.
Infix "\/" := (OrDL Var) : DL_scope.
Notation "f1 --> f2" := (ImpDL Var f1 f2) (at level 11) : DL_scope.
Notation "\A x , f" := (ForallDL Var x f) (at level 10) : DL_scope.
Notation "\E x , f" := (ExistsDL Var x f) (at level 10) : DL_scope.
Notation "x == y" :=
  (AndDL Var (LeqDL Var x y) (GeqDL Var x y)) (at level 10)
  : DL_scope.
Notation "[ p ] f" := (ForallProg Var p f) (at level 10) : DL_scope.
Notation "< p > f" := (ExistsProg Var p f) (at level 10) : DL_scope.

(* Some examples *)

Open Scope HP_scope.
Open Scope string_scope.

(* Intelligent Cruise Control *)
Section ICC.
Variable Br : R.
Variable Ar : R.
Variable br : R.
Variable er : R.
Definition B := Real Var Br.
Definition A := Real Var Ar.
Definition b := Real Var br.
Definition e := Real Var er.

Definition POV_ctrl :=
  "a_pov" ::= *; ?(--B <= `"a_pov" /\ `"a_pov" <= A).

(* TODO Rethink level of arithmetic operators to remove need
   for parenthesis. *)
Definition Safe :=
  `"p_sv" + (`"v_sv"*`"v_sv")/(2*b) + ((A/b)+1)*((A*e*e/2)+(e*`"v_sv"))
  < `"p_pov" + (`"v_pov"*`"v_pov"/(2*B)).

Definition SV_ctrl :=
  "a_sv" ::= *; ?(--B <= `"a_sv" /\ `"a_sv" <= --b) |||
  (? Safe; "a_sv" ::= *; ?(--B <= `"a_sv" /\ `"a_sv" <= A)) |||
  (?(`"v_sv" == 0); "a_sv" ::= 0).

(* This should be concurrent, but we don't have that in the language
   so we go with sequential for now. Things happen instantiously and
   the cars do not share variables, so this is fine.*)
Definition ctrl :=
  POV_ctrl ; SV_ctrl.

Definition dyn :=
  "t" ::= 0;
  ["t"' ::= 1, "p_sv"' ::= `"v_sv", "v_sv"' ::= `"a_sv",
   "p_pov"' ::= `"v_pov", "v_pov"' ::= `"a_pov"] &
  (`"v_sv" >= 0 /\ `"v_pov" >= 0 /\ `"t" <= e).

Definition ICC := (ctrl; dyn)**.
Close Scope string_scope.
Close Scope HP_scope.
End ICC.

Open Scope DL_scope.
Lemma rep_rule : forall p f st,
  eval_formula Var string_dec f st ->
  (forall st, eval_formula Var string_dec (f --> [p]f) st) ->
  eval_formula Var string_dec ([p**]f) st.
Proof.
  intros p f st Hbase Hind.
  simpl in *. intros st' Htrans.
Require Import Equality.
  dependent induction Htrans; firstorder.
Qed.

Lemma seq_intro : forall p1 p2 f st,
  eval_formula Var string_dec ([p1]([p2]f)) st ->
  eval_formula Var string_dec ([p1; p2]f) st.
Proof.
  intros p1 p2 f st H.
  simpl in *. intros st' Htrans.
  inversion Htrans.
  firstorder.
Qed.

(*Lemma seq_intro : forall p1 p2 f st,
  eval_formula Var string_dec ([p1]f) st ->
  (forall st, eval_formula Var string_dec (f --> [p2]f) st) ->
  eval_formula Var string_dec ([p1; p2]f) st.
Proof.
  intros p1 p2 f st Hp1 Hp2.
  simpl. intros st' Htrans.
  inversion Htrans. simpl in *.
  firstorder.
Qed.*)

Lemma union_intro : forall p1 p2 f st,
  eval_formula Var string_dec ([p1]f) st ->
  eval_formula Var string_dec ([p2]f) st ->
  eval_formula Var string_dec ([p1 ||| p2]f) st.
Proof.
  intros p1 p2 f st Hp1 Hp2.
  simpl. intros st' Htrans.
  inversion Htrans; auto.
Qed.

Lemma test_intro : forall test f st,
  (eval_fol Var string_dec test st ->
   eval_formula Var string_dec f st) ->
  eval_formula Var string_dec ([? test]f) st.
Proof.
  intros test f st H.
  simpl. intros st' Htrans.
  inversion Htrans. subst. auto.
Qed.

Inductive VarOrDeriv : Set :=
| VarC : Var -> VarOrDeriv
| DerivC : Var -> VarOrDeriv.

Definition VarOrDeriv_dec : forall (x1 x2:VarOrDeriv),
  {x1 = x2} + {x1 <> x2}.
repeat decide equality.
Defined.

Fixpoint lift_term (t:Term Var) : Term VarOrDeriv :=
  match t with
  | SVar x       => SVar _ (VarC x)
  | Real r       => Real _ r
  | Plus t1 t2   => Plus _ (lift_term t1) (lift_term t2)
  | Minus t1 t2  => Minus _ (lift_term t1) (lift_term t2)
  | Times t1 t2  => Times _ (lift_term t1) (lift_term t2)
  | Divide t1 t2 => Divide _ (lift_term t1) (lift_term t2)
  end.

Fixpoint lift_fol (f:FOL Var) : FOL VarOrDeriv :=
  match f with
  | Leq t1 t2 => Leq _ (lift_term t1) (lift_term t2)
  | Lt t1 t2 => Lt _ (lift_term t1) (lift_term t2)
  | Geq t1 t2 => Geq _ (lift_term t1) (lift_term t2)
  | Gt t1 t2 => Gt _ (lift_term t1) (lift_term t2)
  | Neg f => Neg _ (lift_fol f)
  | And f1 f2 => And _ (lift_fol f1) (lift_fol f2)
  | Or f1 f2 => Or _ (lift_fol f1) (lift_fol f2)
  | Imp f1 f2 => Imp _ (lift_fol f1) (lift_fol f2)
  | Forall x f => Forall _ (VarC x) (lift_fol f)
  | Exists x f => Exists _ (VarC x) (lift_fol f)
  end.

Fixpoint lift_prog (p:HybridProg Var) : HybridProg VarOrDeriv :=
  match p with
  | Assign x t => Assign _ (VarC x) (lift_term t)
  | NonDetAssign x => NonDetAssign _ (VarC x)
  | DiffEq eqs f => DiffEq _
     (map (fun eq:Var*Term Var =>
             let (x,t) := eq in (VarC x, lift_term t)) eqs)
     (lift_fol f)
  | Pred f => Pred _ (lift_fol f)
  | Union p1 p2 => Union _ (lift_prog p1) (lift_prog p2)
  | Seq p1 p2 => Seq _ (lift_prog p1) (lift_prog p2)
  | Rep p' => Rep _ (lift_prog p')
  end.

Fixpoint lift_formula (f:Formula Var) : Formula VarOrDeriv :=
  match f with
  | LeqDL t1 t2 => LeqDL _ (lift_term t1) (lift_term t2)
  | LtDL t1 t2 => LtDL _ (lift_term t1) (lift_term t2)
  | GeqDL t1 t2 => GeqDL _ (lift_term t1) (lift_term t2)
  | GtDL t1 t2 => GtDL _ (lift_term t1) (lift_term t2)
  | NegDL f => NegDL _ (lift_formula f)
  | AndDL f1 f2 => AndDL _ (lift_formula f1) (lift_formula f2)
  | OrDL f1 f2 => OrDL _ (lift_formula f1) (lift_formula f2)
  | ImpDL f1 f2 => ImpDL _ (lift_formula f1) (lift_formula f2)
  | ForallDL x f => ForallDL _ (VarC x) (lift_formula f)
  | ExistsDL x f => ExistsDL _ (VarC x) (lift_formula f)
  | ForallProg p f => ForallProg _ (lift_prog p) (lift_formula f)
  | ExistsProg p f => ExistsProg _ (lift_prog p) (lift_formula f)
  end.

Fixpoint syn_deriv_term (t:Term Var) : Term VarOrDeriv :=
  match t with
  | SVar x => SVar _ (DerivC x)
  | Real r => Real _ R0
  | Plus t1 t2 =>
     Plus _ (syn_deriv_term t1) (syn_deriv_term t2)
  | Minus t1 t2 =>
     Minus _ (syn_deriv_term t1) (syn_deriv_term t2)
  | Times t1 t2 =>
     Plus _ (Times _ (syn_deriv_term t1) (lift_term t2))
            (Times _ (lift_term t1) (syn_deriv_term t2))
  | Divide t1 t2 =>
     Divide _ (Minus _ (Times _ (syn_deriv_term t1) (lift_term t2))
                       (Times _ (lift_term t1) (syn_deriv_term t2)))
              (Times _ (lift_term t2) (lift_term t2))
  end.

Fixpoint subst_diffeq_term (eq:Var * Term Var) (t:Term VarOrDeriv) :=
  match t with
  | SVar (VarC _)       => t
  | SVar (DerivC x)   => if string_dec x (fst eq)
                        then lift_term (snd eq)
                        else t
  | Real _       => t
  | Plus t1 t2   => Plus _ (subst_diffeq_term eq t1)
                           (subst_diffeq_term eq t2)
  | Minus t1 t2  => Minus _ (subst_diffeq_term eq t1)
                            (subst_diffeq_term eq t2)
  | Times t1 t2  => Times _ (subst_diffeq_term eq t1)
                            (subst_diffeq_term eq t2)
  | Divide t1 t2 => Divide _ (subst_diffeq_term eq t1)
                             (subst_diffeq_term eq t2)
  end.

Fixpoint syn_deriv_formula (f:Formula Var) : Formula VarOrDeriv :=
  match f with
  | LeqDL t1 t2 => LeqDL _ (syn_deriv_term t1) (syn_deriv_term t2)
  | LtDL t1 t2 => LeqDL _ (syn_deriv_term t1) (syn_deriv_term t2)
  | GeqDL t1 t2 => GeqDL _ (syn_deriv_term t1) (syn_deriv_term t2)
  | GtDL t1 t2 => GeqDL _ (syn_deriv_term t1) (syn_deriv_term t2)
  | NegDL f => NegDL _ (syn_deriv_formula f)
  | AndDL f1 f2 => AndDL _ (syn_deriv_formula f1)
                         (syn_deriv_formula f2)
  | OrDL f1 f2 => OrDL _ (syn_deriv_formula f1) (syn_deriv_formula f2)
  | ImpDL f1 f2 => ImpDL _ (syn_deriv_formula f1)
                         (syn_deriv_formula f2)
  | ForallDL x f => ForallDL _ (VarC x) (syn_deriv_formula f)
  | ExistsDL x f => ExistsDL _ (VarC x) (syn_deriv_formula f)
  | ForallProg p f => ForallProg _ (lift_prog p) (syn_deriv_formula f)
  | ExistsProg p f => ExistsProg _ (lift_prog p) (syn_deriv_formula f)
  end.

Fixpoint subst_diffeq_fol (eq:Var * Term Var) (f:FOL VarOrDeriv) :=
  match f with
  | Leq t1 t2 => Leq _ (subst_diffeq_term eq t1)
                       (subst_diffeq_term eq t2)
  | Lt t1 t2 => Lt _ (subst_diffeq_term eq t1)
                     (subst_diffeq_term eq t2)
  | Geq t1 t2 => Geq _ (subst_diffeq_term eq t1)
                       (subst_diffeq_term eq t2)
  | Gt t1 t2 => Gt _ (subst_diffeq_term eq t1)
                     (subst_diffeq_term eq t2)
  | Neg f => Neg _ (subst_diffeq_fol eq f)
  | And f1 f2 => And _ (subst_diffeq_fol eq f1)
                       (subst_diffeq_fol eq f2)
  | Or f1 f2 => Or _ (subst_diffeq_fol eq f1)
                     (subst_diffeq_fol eq f2)
  | Imp f1 f2 => Imp _ (subst_diffeq_fol eq f1)
                       (subst_diffeq_fol eq f2)
  | Forall x f => Forall _ x (subst_diffeq_fol eq f)
  | Exists x f => Exists _ x (subst_diffeq_fol eq f)
  end.

Fixpoint subst_diffeq_formula (eq:Var * Term Var)
         (f:Formula VarOrDeriv) :=
  match f with
  | LeqDL t1 t2 => LeqDL _ (subst_diffeq_term eq t1)
                       (subst_diffeq_term eq t2)
  | LtDL t1 t2 => LtDL _ (subst_diffeq_term eq t1)
                     (subst_diffeq_term eq t2)
  | GeqDL t1 t2 => GeqDL _ (subst_diffeq_term eq t1)
                       (subst_diffeq_term eq t2)
  | GtDL t1 t2 => GtDL _ (subst_diffeq_term eq t1)
                     (subst_diffeq_term eq t2)
  | NegDL f => NegDL _ (subst_diffeq_formula eq f)
  | AndDL f1 f2 => AndDL _ (subst_diffeq_formula eq f1)
                       (subst_diffeq_formula eq f2)
  | OrDL f1 f2 => OrDL _ (subst_diffeq_formula eq f1)
                     (subst_diffeq_formula eq f2)
  | ImpDL f1 f2 => ImpDL _ (subst_diffeq_formula eq f1)
                       (subst_diffeq_formula eq f2)
  | ForallDL x f => ForallDL _ x (subst_diffeq_formula eq f)
  | ExistsDL x f => ExistsDL _ x (subst_diffeq_formula eq f)
  | ForallProg p f => ForallProg _ p (subst_diffeq_formula eq f)
  | ExistsProg p f => ExistsProg _ p (subst_diffeq_formula eq f)
  end.

Definition subst_diffeqs_formula (eqs:list (Var * Term Var))
  (f:Formula VarOrDeriv) :=
  fold_right subst_diffeq_formula f eqs.

(* TODO Differential induction from Platzer *)
Lemma diffeqs_intro : forall eqs pred f st,
  (forall st,
     eval_fol _ VarOrDeriv_dec (lift_fol pred) st ->
     eval_formula VarOrDeriv VarOrDeriv_dec
                  (subst_diffeqs_formula eqs (syn_deriv_formula f))
                  st) ->
  eval_formula Var string_dec ([eqs & pred]f) st.
Admitted.

Require Import FunctionalExtensionality.
(* Importing this modules brings in a general function extensionality
   axiom which has been proven to be consistent with CIC. Its not
   clear if we could do without it. I tried to prove the following
   lemmas without and got stuck on state_extensionality_transistion
   when trying to prove the continuous transition case. We would need
   to redefine the semantics of that case, which we could do, but
   should we? These semantics would be different than what Platzer
   does in his book. In particular, instead of saying that the flow
   function must produce the right beginning and ending states
   we would have to say that it agrees with those two states on
   all inputs. *)
(*Lemma state_extensionality_term : forall t st1 st2,
  (forall x, st1 x = st2 x) ->
  eval_term t st1 =
  eval_term t st2.
Proof.
  intros t st1 st2 Heq.
  induction t; simpl in *; auto;
  rewrite IHt1; rewrite IHt2; auto.
Qed.

Lemma state_extensionality_transition : forall h st1 st2 st3,
  (forall x, st1 x = st2 x) ->
  Transition h st1 st3 ->
  Transition h st2 st3.
Proof.
  intros h st1 st2 st3 Heq Htrans.
  induction Htrans.
    constructor.
    rewrite H. apply state_extensionality_term; auto.
    intros y Hy. specialize (H0 y Hy). congruence.

    econstructor; eauto.
    intros y Hy. specialize (H0 y Hy). congruence.

    econstructor; eauto.

Lemma state_extensionality_formula : forall f st1 st2,
  (forall x, st1 x = st2 x) ->
  eval_formula Var string_dec f st1 ->
  eval_formula Var string_dec f st2.
Proof.
  intro f.
  induction f; intros st1 st2 Heq Hst1; simpl in *; eauto;
    try (rewrite (state_extensionality_term t st2 st1); auto;
         rewrite (state_extensionality_term t0 st2 st1); auto).
    split; (eapply IHf1 || eapply IHf2); eauto; tauto.
    destruct Hst1; [left; eapply IHf1 | right; eapply IHf2]; eauto.
    firstorder.
    intros. apply Hst1. eapply Ihf; eauto.*)

Lemma assign_intro : forall x t f st,
  eval_formula Var string_dec f
    (fun y => if string_dec x y then eval_term _ t st else st y) ->
  eval_formula Var string_dec ([x ::= t]f) st.
Proof.
  intros x t f st H.
  simpl. intros st' Htrans.
  inversion Htrans.
 assert (st' = (fun y : Var =>
    if string_dec x y then eval_term _ t st else st y)).
    apply functional_extensionality.
    intro x1. destruct (string_dec x x1).
    subst x1; auto.
    symmetry. eapply H5.
    congruence.
  rewrite H6. auto.
Qed.

Lemma nondetassign_intro : forall x f st,
  (forall r, eval_formula Var string_dec f
    (fun y => if string_dec x y then r else st y)) ->
  eval_formula Var string_dec ([x ::= *]f) st.
Proof.
  intros x f st H.
  simpl. intros st' Htrans.
  inversion Htrans.
 assert (st' = fun y : Var => if string_dec x y then r else st y).
    apply functional_extensionality.
    intro x1. destruct (string_dec x x1).
    subst x1; auto.
    symmetry. eapply H2.
    congruence.
  rewrite H5. auto.
Qed.

Lemma imp_intro : forall f f' st,
  (eval_formula Var string_dec f st ->
   eval_formula Var string_dec f' st) ->
  eval_formula Var string_dec (f --> f') st.
Proof.
  auto.
Qed.

Definition Inv := `"p_sv" < `"p_pov".

Definition IndInv_safe B A b :=
  `"p_sv" + (`"v_sv"*`"v_sv")/(2*(Real _ b)) +
  (((Real _ A)/(Real _ b))+1)*(((Real _ A)*`"t"*`"t"/2)+(`"t"*`"v_sv"))
  < `"p_pov" + (`"v_pov"*`"v_pov"/(2*(Real _ B))).

Definition IndInv_v B A b :=
  (`"v_sv"*`"v_sv")/(2*(Real _ b)) +
  (((Real _ A)/(Real _ b))+1)*(((Real _ A)*`"t"*`"t"/2)+(`"t"*`"v_sv"))
  < (`"v_pov"*`"v_pov"/(2*(Real _ B))).

Lemma IndInv_imp_inv : forall B A b st,
  eval_formula Var string_dec
    (((IndInv_safe B A b) /\ (IndInv_v B A b)) --> Inv) st.
Proof.
repeat (intros; apply imp_intro).
simpl in *. intros.
destruct H.
Admitted.

Definition IndInv (B A b e:R) :=
  (`"p_sv" <= `"p_pov") -->
     (  Inv
      /\ (`"p_sv" + (`"v_sv"*`"v_sv")/(2*(Real _ b))
         < `"p_pov" + (`"v_pov"*`"v_pov"/(2*(Real _ B))))
      /\ (`"v_sv" >= 0 /\ `"v_pov" >= 0)).

Lemma R_0_div : forall r:R, r <> R0 -> Rdiv 0%R r = R0.
Admitted.

Theorem ICC_ok : forall B A b e st,
  eval_formula Var string_dec
    ((IndInv_safe B A b) --> [ICC B A b e] (IndInv_safe B A b)) st.
Proof.
  intros B A b e st.
Arguments string_dec !s1 !s2.
  repeat (intros; match goal with
         | [ |- _ ] => apply imp_intro
         | [ |- _ ] => apply rep_rule
         | [ |- _ ] => apply seq_intro
         | [ |- _ ] => apply union_intro
         | [ |- _ ] => apply assign_intro
         | [ |- _ ] => apply nondetassign_intro
         | [ |- _ ] => apply test_intro
         | [ |- _ ] => apply diffeqs_intro
         end); auto; simpl in *; intros.
