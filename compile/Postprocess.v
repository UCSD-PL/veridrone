Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.ProofRules.
Require Import String.
Local Open Scope HP_scope.
Local Open Scope string_scope.
Require Import List.
Require Import Strings.String.
Import ListNotations.
Require Import Rdefinitions.
Require Import RelDec.
Require Import Coq.Reals.Rbase.
Require Import Z3.Tactic.
Require Import Abstractor.
Require Import TLA.Automation.
Require Import Coq.Classes.Morphisms.

Lemma Z3Test : forall (a : R), (a + 1 = 3)%R%type -> ((a + 2 = 3)%R /\ ((1+1)%R=2%R)%R)%type.
Proof.
  intros.
  (*z3 solve.*)
  Abort.

(* Implementation of postprocessing automation for the Abstractor,
   using the Z3 plugin to simplify the terms produced b ythe abstractor *)

(* test cases - velocity shim *)

Definition velshim : fcmd :=
  FIte (FMinus (FVar "ub") (FPlus (FMult (FVar "a") (FVar "d")) (FVar "vmax")))
       (FAsn "a" (FVar "a"))
       (FAsn "a" (FConst fzero)).

Definition velshim_ivs : list (Var * Var) :=
  [("ub", "ub"); ("a", "a"); ("d", "d"); ("vmax", "vmax")].

(* proportional controller *)

Print FMinus.

(* c is constant and goal is 0 *)
Definition proportional_controller : fcmd :=
  FAsn "a" (FMinus (FConst fzero) (FVar "x")).

Definition proportional_controller_ivs : list (Var * Var) :=
  [("a", "a"); ("x", "x")].

(* "Pushing" Embed through connectives *)
Lemma lequiv_formula_iff :
  forall (P Q : Formula),
    (forall tr, eval_formula P tr <-> eval_formula Q tr) <->
    (P -|- Q).
Proof.
  intros.
  split.
  - intros. split; breakAbstraction; intros; apply H; assumption.
  - intros. unfold lequiv in H. destruct H.
    breakAbstraction.
    split; intros; [apply H | apply H0]; assumption.
Qed.

Ltac shatterAbstraction :=
  try apply lequiv_formula_iff; unfold lequiv in *; breakAbstraction.  

Lemma embed_push_TRUE :
  Embed (fun _ _ => True) -|- TRUE.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma embed_push_FALSE :
  Embed (fun _ _ => False) -|- FALSE.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma embed_push_And :
  forall (P1 P2 : _ -> _ -> Prop) (F1 F2 : Formula),
    Embed P1 -|- F1 -> Embed P2 -|- F2 ->
    Embed (fun x y => P1 x y /\ P2 x y) -|- F1 //\\ F2.
Proof.
  shatterAbstraction. intuition.
Qed.

Lemma embed_push_Or :
  forall (P1 P2 : _ -> _ -> Prop) (F1 F2 : Formula),
    Embed P1 -|- F1 -> Embed P2 -|- F2 ->
    Embed (fun x y => P1 x y \/ P2 x y) -|- F1 \\// F2.
Proof.
  shatterAbstraction. intuition.
Qed.

Lemma embed_push_Imp :
  forall (P1 P2 : _ -> _ -> Prop) (F1 F2 : Formula),
    Embed P1 -|- F1 -> Embed P2 -|- F2 ->
    Embed (fun x y => P1 x y -> P2 x y) -|- F1 -->> F2.
Proof.
  shatterAbstraction. intuition.
Qed.

Lemma embed_push_Exists :
  forall (T : Type) (P : T -> state -> state -> Prop) (F : T -> Formula),
    (forall (t : T), Embed (P t) -|- F t) ->
    Embed (fun x y => exists (t : T), (P t x y)) -|- lexists F.
Proof.
  shatterAbstraction.
  intuition.
  fwd. specialize (H x). fwd.
  eexists. eauto.
  fwd. specialize (H x). fwd.
  eexists. eauto.
Qed.

Lemma embed_push_Forall :
  forall (T : Type) (P : T -> state -> state -> Prop) (F : T -> Formula),
    (forall (t : T), Embed (P t) -|- F t) ->
    Embed (fun x y => forall (t : T), (P t x y)) -|- lforall F.
Proof.
  intros.
  shatterAbstraction. intuition.
  eapply H. apply H0.
  eapply H. apply H0.  
Qed.

Lemma embed_push_Const : forall P, Embed (fun _ _ => P) -|- PropF P.
Proof.
  shatterAbstraction; tlaIntuition.
Qed.

(* Relation expressing a side-condition that must be used to push embed through arithmetic facts *)
Definition evals_to (f : Term) (f' : state -> state -> R) : Prop :=
  (eval_term f = f')%type.

Notation "f =|> g" := (evals_to f g) (at level 60).

(* comparison pushing *)
Lemma embed_push_Eq :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => l' x y = r' x y)%type -|-
          Comp l r Eq.
Proof.
  intros.
  unfold evals_to in *. 
  shatterAbstraction. subst. reflexivity.
Qed.

Lemma embed_push_Gt :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => Rgt (l' x y) (r' x y))%type -|-
          Comp l r Gt.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma embed_push_Ge :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => Rge (l' x y) (r' x y))%type -|-
          Comp l r Ge.
Proof.
  intros.
  unfold evals_to in *. 
  shatterAbstraction. subst. reflexivity.
Qed.

Lemma embed_push_Lt :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => Rlt (l' x y) (r' x y))%type -|-
          Comp l r Lt.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma embed_push_Le :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => Rle (l' x y) (r' x y))%type -|-
          Comp l r Le.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

(* arithmetic pushing *)
Lemma arith_push_plus :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    PlusT l r =|> (fun x y => l' x y + r' x y)%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_minus :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    MinusT l r =|> (fun x y => l' x y - r' x y)%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_mult :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    MultT l r =|> (fun x y => l' x y * r' x y)%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_inv :
  forall l l',
    l =|> l' ->
    InvT l =|> (fun x y => / (l' x y))%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_cos :
  forall l l',
    l =|> l' ->
    CosT l =|> (fun x y => Rtrigo_def.cos (l' x y))%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_sin :
  forall l l',
    l =|> l' ->
    SinT l =|> (fun x y => Rtrigo_def.sin (l' x y))%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

(* var, real *)
Lemma arith_push_VarNow :
  forall (x : Var),
    VarNowT x =|> fun st _ => st x.
Proof.
  reflexivity.
Qed.

Lemma arith_push_VarNext :
  forall (x : Var),
    VarNextT x =|> fun _ st' => st' x.
Proof.
  reflexivity.
Qed.

(* special cases for 0 and 1: want to compile these into nats,
   since nat are easier to work with *)
Lemma arith_push_Nat_zero :
    NatT 0 =|> fun _ _ => 0%R.
Proof. reflexivity. Qed.

Lemma arith_push_Nat_one :
    NatT 1 =|> fun _ _ => 1%R.
Proof. reflexivity. Qed.

Lemma arith_push_Nat :
  forall (n : nat),
    NatT n =|> fun _ _ => INR n.
Proof. reflexivity. Qed.

Lemma arith_push_Real :
  forall (r : R),
    RealT r =|> fun _ _ => r.
Proof. reflexivity. Qed.

(* for solving goals containing fupdate *)
Lemma arith_push_fupdate_eq :
  forall (t: state -> state -> R) (v : Var) (X : Term) f,
    X =|> t ->
    X =|> (fun x y : state => fupdate (f x y) v (t x y) v).
Proof.
  intros. unfold evals_to in *.
  rewrite H. unfold fupdate.
  rewrite rel_dec_eq_true; eauto with typeclass_instances.
Qed.

Lemma arith_push_fupdate_neq :
  forall (t: state -> state -> R) (v v' : Var) (X : Term) f,
    v <> v' ->
    X =|> (fun x y : state => f x y v') ->
    X =|> (fun x y : state => fupdate (f x y) v (t x y) v').
Proof.
  intros.
  unfold fupdate, evals_to in *. rewrite H0.
  rewrite rel_dec_neq_false; eauto with typeclass_instances.
Qed.

Create HintDb embed_push discriminated.
Create HintDb arith_push discriminated.

Hint Rewrite
     embed_push_TRUE embed_push_FALSE
     embed_push_And embed_push_Or embed_push_Imp
     embed_push_Exists embed_push_Forall
     embed_push_Const
  : embed_push.

Hint Rewrite
     embed_push_Eq embed_push_Gt embed_push_Ge embed_push_Lt embed_push_Le
     using solve [eauto 20 with arith_push]
                         : embed_push.

(* for the "<>" goals created by arith_push_fupdate_neq *)
Hint Extern
     0 (_ <> _) => congruence : arith_push.

(* Other miscellaneous rewriting lemmas *)
Lemma AnyOf_singleton :
  forall (P : Prop), AnyOf [P] -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma AnyOf_weaken :
  forall (P : Prop) (Ps : list Prop),
    AnyOf Ps |-- AnyOf (P :: Ps).
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma and_True_snip1 :
  forall (P : Prop),
    True //\\ P -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma and_True_snip2 :
  forall (P : Prop),
    P //\\ True -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma or_False_snip1 :
  forall (P : Prop),
    P \\// False -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma or_False_snip2 :
  forall (P : Prop),
    False \\// P -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

(* Very simple program for testing. We want to prove that x stays >0 *)
Definition float_one := source.nat_to_float 1.
Opaque float_one.
Definition simple_prog : fcmd :=
  FAsn "x" (FPlus (FConst float_one) (FVar "x")).

Definition simple_prog_ivs : list (Var * Var) :=
  [("x", "x")].

Lemma PropF_revert :
  forall (P : Prop) (G Q : Syntax.Formula),
    (P -> G |-- Q) ->
    (G |-- PropF P -->> Q).
Proof.
  tlaIntuition.
Qed.

Lemma PropF_pull :
  forall (P : Prop) (G Q : Syntax.Formula),
    P ->
    (G |-- Q) ->
    (PropF P -->> G |-- Q).
Proof.
  tlaIntuition.
Qed.

(* Version of HoareA_embed_ex we can use for rewriting. *)
Lemma HoareA_embed_ex_rw :
  forall (c : fcmd)
         (vs1 : list (Var * Var)),
    var_spec_valid' vs1 ->
    varmap_check_fcmd vs1 c ->
    oembed_fcmd vs1 vs1 c |--
                Forall Q : state -> Prop,
  let P := fwp c Q vs1 in
  PropF (SEMR vs1 Q) -->> Embed (fun st st' : state => P st -> Q st').
Proof.
  intros. apply lforallR.
  intro. simpl. restoreAbstraction.
  apply PropF_revert. intro.
  tlaRevert.
  apply HoareA_embed_ex; auto.
  apply fwp_correct; auto.
Qed.

Axiom Always_proper : Proper (lentails ==> lentails) Syntax.Always.
Existing Instance Always_proper.

(* Used to begin rewriting in our goal. *)
Lemma lequiv_rewrite_left :
  forall (A B C : Formula),
    A -|- C -> C |-- B -> A |-- B.
Proof.
  shatterAbstraction. intuition.
Qed.

Fact fwp_simple : |-- "x" > 0 //\\ [](oembed_fcmd simple_prog_ivs simple_prog_ivs simple_prog) -->> []("x" > 0).
Proof.
  erewrite -> HoareA_embed_ex_rw; [| solve [simpl; intuition] | solve [simpl; intuition; eauto]].
  charge_intros.
  eapply discr_indX.
  { red; intuition. }
  { charge_assumption. }
  { charge_assumption. }
  { SearchAbout land lentails.
    SearchAbout Proper land.
    Print ILogic.
    (* rhs *)
    rewrite landforallDL. eapply lforallL. instantiate (1 := (fun st => st "x" > 0)%R).
    tlaRevert. apply PropF_pull.
    - unfold SEMR. intros. SearchAbout vmodels. admit (* prove a lemma *).
    - simpl fwp.
      (*rewrite_strat (topdown (terms embed_push_Eq)).
      rewrite_strat (topdown (old_hints embed_push)).*)
      (*
      rewrite_strat (topdown (repeat (terms embed_push_TRUE embed_push_FALSE
                                            embed_push_And embed_push_Or embed_push_Imp
                                            embed_push_Exists embed_push_Forall
                                            embed_push_Const))). *)
      (*autorewrite with embed_push.*)



      eapply lequiv_rewrite_left.

      Hint Extern
           0 (_ =|> (fun _ _ => ?X)) => first [ apply arith_push_Nat_zero | apply arith_push_Nat_one
                                              | apply arith_push_Nat | apply arith_push_Real]
        : arith_push.

      Hint Resolve
           arith_push_plus arith_push_minus arith_push_mult arith_push_inv
           arith_push_sin arith_push_cos
           arith_push_VarNow arith_push_VarNext
           arith_push_fupdate_eq arith_push_fupdate_neq
        : arith_push.

      {
        progress repeat
            match goal with
            | |- Embed (fun x y => _ /\ _) -|- _ => eapply embed_push_And
            | |- Embed (fun x y => _ -> _) -|- _ => eapply embed_push_Imp
            | |- Embed (fun x y => _ \/ _) -|- _ => eapply embed_push_Or
            | |- Embed (fun x y => exists z, _) -|- _ => eapply embed_push_Exists; intro
            | |- Embed (fun x y => forall z, _) -|- _ => eapply embed_push_Forall; intro
            | |- Embed (fun x y => _ = _) -|- _ => eapply embed_push_Eq; eauto with arith_push
            | |- Embed (fun x y => (_ < _)%R) -|- _ => eapply embed_push_Lt; eauto with arith_push
            | |- Embed (fun x y => (_ <= _)%R) -|- _ => eapply embed_push_Le; eauto with arith_push
            | |- Embed (fun x y => (_ > _)%R) -|- _ => eapply embed_push_Gt; eauto with arith_push
            | |- Embed (fun x y => (_ >= _)%R) -|- _ => eapply embed_push_Ge; eauto with arith_push
            | |- Embed (fun x y => ?X) -|- _ => eapply embed_push_Const
            end.
      }

      Lemma lentail_cut1 :
        forall (A B C : Formula),
               C |-- A ->
               A -->> B |-- C -->> B.
      Proof.
        intros. breakAbstraction. intuition.
      Qed.
               

      idtac.
      apply lentail_cut1.
      Print bound.isVarValid.
      
      simpl next.

      

        idtac.
        eapply arith_push_fupdate.
        eauto with arith_push.

        Print evals_to.
        
        Print Syntax.Term.
        unfold fupdate.
        simpl.
        Print eval_term.
        eauto with arith_push.
        
        
            
        Print fupdate.
        
                                                                                                                    

        repeat (first [ eapply embed_push_And (*; eauto with arith_push*) |
                        eapply embed_push_Or  (*; eauto with arith_push*) |
                        eapply embed_push_Imp (*; eauto with arith_push*) |
                        eapply embed_push_Exists; intro (*; eauto with arith_push*) |
                        eapply embed_push_Forall; intro (*; eauto with arith_push*) |
                        eapply embed_push_Const (*; eauto with arith_push*) |
                        eapply embed_push_Eq; eauto with arith_push |
                        eapply embed_push_Lt; eauto with arith_push |
                        eapply embed_push_Le; eauto with arith_push |
                        eapply embed_push_Gt; eauto with arith_push |
                        eapply embed_push_Ge; eauto with arith_push
               ]).
        simple eapply embed_push_Imp.
        eapply embed_push_And.

        idtac.
        Check embed_push_Forall.
        match goal with 
        
        eauto with arith_push.
        
        Focus 7. eapply lforall_lequiv_m.
      2: eauto with arith_push.
      2: eauto with arith_push.
      setoid_rewrite embed_push_Le.

      rewrite_strat (subterm (terms (embed_push_Le))).
      rewrite_strat (topdown (repeat (old_hints embed_push))).

      rewrite_strat (topdown (repeat (terms embed_push_Imp embed_push_And embed_push_Or))).

      autorewrite with embed_push.
      rewrite 
      rewrite_strat (bottomup (repeat (terms embed_push_Imp embed_push_And embed_push_Or))).
      setoid_rewrite embed_push_Imp.
      
      rewrite_strat bottomup embed_push_Imp.
      rewrite_strat bottomup (repeat (hints embed_push)).

    
      apply H.
    
    breakAbstraction.

    
    

    
  simpl. intuition. eexists. left. reflexivity.
        
  specialize (fwp_correct simple_prog_ivs ivs 
                    

(* sample abstractor outputs *)
Section fwp.
  Parameter st : state.
  Parameter postcond : state -> Prop.
  
  (* discrete invariant: controller never changes x *)
  (*Fact fwp_propcontrol : forall (P : (fwp proportional_controller postcond proportional_controller_ivs st)), False.*)
  Fact fwp_propcontrol : (fwp proportional_controller postcond proportional_controller_ivs st).
  Proof.
    intros.
    cbv beta iota delta [fwp proportional_controller].
    simpl.
    Print bound.isVarValid.
    
    unfold Semantics.eval_comp.
    simpl.


    (* TODO may need to bolt on continuation support *)
    Unset Ltac Debug.
    Ltac abstractor_cleanup P :=
      let rec cleanup P :=
          match P with
          | AnyOf ?P1 :: nil => apply AnyOf_singleton in P; abstractor_cleanup P
          | AnyOf ?PS => cleanup_list PS
          | ?P1 \/ ?P2 => abstractor_cleanup P1; abstractor_cleanup P2
          | True /\ ?P1 => apply and_True_snip1 in P; abstractor_cleanup P
          | _ => idtac
    end
    with cleanup_list ls :=
      match ls with
      | ?P :: ?PS => cleanup P; cleanup_list PS
      | nil => idtac
      end
      in
        let t := type of P in
        cleanup t.

    (* use entailment |-- and -|-
       also want to convert (state -> Prop) to Formula by distributing embed.
       test on "just increment x" controller, where safety is x > 0 
       prove bi entailment of result formula *)

    Ltac abstractor_cleanup_goal :=
      match goal with
      | |- ?P => abstractor_cleanup P
      end.

    match goal with
    | |- _ \/ _ => idtac
    end.

    abstractor_cleanup_goal.

    
    Unset Ltac Debug.

              Lemma silly_AnyOf :
                AnyOf (True :: nil) -> False.
              Proof.
                intro.
                apply AnyOf_singleton in H.
                Focus 2.
                Check AnyOf_singleton.
                rewrite AnyOf_singleton; reflexivity.
                apply AnyOf_singleton.
                abstractor_cleanup H.
              
              abstractor_cleanup P.

              repeat (
        match P with
        | 
        end
        ).
  Abort.
  
Fact fwp_velshim : False.
  pose (fun P => fwp velshim P velshim_ivs).
Opaque AnyOf. 
cbv beta iota delta [ fwp velshim ] in P.
unfold Semantics.eval_comp in P.
simpl in P.
unfold maybe_ge0, maybe_lt0 in P.
simpl eval_term in P.
simpl bound_fexpr in P.

Abort.


(* ltac automation *)
Ltac abstractor_cleanup P :=
  

(*
Fact fwp_test :
  forall (st : Syntax.state),
    (st "x" = 1%R)%type ->
    (fwp simple_prog (fun (ss : Syntax.state) => (ss "x" > 0)%R)%type)
      st.
Proof.
  intros.
  simpl. destruct (bounds_to_formula
           {|
           lb := RealT
                   (Fappli_IEEE.B2R custom_prec custom_emax (nat_to_float 1));
           ub := RealT
                   (Fappli_IEEE.B2R custom_prec custom_emax (nat_to_float 1));
           premise := TRUE |} st) eqn:Hb2f.
  left.
  split.
  
  - apply P.
  red.
  compute.

Opaque nat_to_float.

Check fwp.

Fact fwp_test :
  forall (st : Syntax.state),
  (fwp simple_prog (fun (ss : Syntax.state) => (ss "x" > 0)%R)%type)
    st.
Proof.
  intros.
  compute.

  Print nat_to_float.
  Print Fappli_IEEE_extra.BofZ.
  Print Fappli_IEEE.binary_normalize.
  Check Fappli_IEEE.FF2B.
  About Fappli_IEEE.binary_round_correct.
  Eval vm_compute in (nat_to_float 0).


  Print custom_prec.


  simpl. left.
  generalize (bound_fexpr_sound). intro.
  SearchAbout bounds_to_formula.
  
Abort.
