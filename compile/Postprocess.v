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

Lemma Z3Test : forall (a : R), (a + 1 = 3)%R%type -> ((a + 2 = 3)%R /\ ((1+1)%R=2%R)%R)%type.
Proof.
  intros.
  (*z3 solve.*)
  Abort.

(* Implementation of postprocessing automation for the Abstractor,
   using the Z3 plugin to simplify the terms produced by the abstractor *)

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
  forall (P1 P2 : _ -> _ -> Prop),
    Embed (fun x y => P1 x y /\ P2 x y) -|- Embed P1 //\\ Embed P2.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma embed_push_Or :
  forall (P1 P2 : _ -> _ -> Prop),
    Embed (fun x y => P1 x y \/ P2 x y) -|- Embed P1 \\// Embed P2.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma embed_push_Imp :
  forall (P1 P2 : _ -> _ -> Prop),
    Embed (fun x y => P1 x y -> P2 x y) -|- Embed P1 -->> Embed P2.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma embed_push_Exists :
  forall (T : Type) (P : T -> state -> state -> Prop),
    Embed (fun x y => exists (t : T), (P t x y)) -|- Syntax.Exists T (fun (t : T) => Embed (P t)).
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma embed_push_Forall :
  forall (T : Type) (P : T -> state -> state -> Prop),
    Embed (fun x y => forall (t : T), (P t x y)) -|- Syntax.Forall T (fun (t : T) => Embed (P t)).
Proof.
  shatterAbstraction. tauto.
Qed.

(* Useful lemmas *)
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
