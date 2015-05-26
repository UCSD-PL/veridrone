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

Definition proportional_controller : fcmd :=
  FAsn "a" (FMult (FVar "c") (FMinus (FVar "goal") (FVar "x"))).

Definition proportional_controller_ivs : list (Var * Var) :=
  [("a", "a"); ("c", "c"); ("x", "x"); ("goal", "goal")].

(* Useful lemmas *)
Lemma AnyOf_singleton :
  forall (P : Prop), AnyOf [P] -> P.
Proof.
  intros. inversion H.
  - auto.
  - inversion H0.
Qed.

Lemma AnyOf_weaken :
  forall (P : Prop) (Ps : list Prop),
    AnyOf Ps -> AnyOf (P :: Ps).
Proof.
  intros.
  simpl. right. auto.
Qed.
    

(* sample abstractor outputs *)
Section fwp.
  Parameter st : state.
  Parameter precond : state -> Prop.
  Fact fwp_propcontrol : forall (P : (fwp proportional_controller precond proportional_controller_ivs st)), False.
        Opaque AnyOf.
        intros.
        cbv beta iota delta [fwp proportional_controller] in P.
        simpl in P.
        unfold Semantics.eval_comp in P.

        (* TODO may need to bolt on continuation support *)
        Unset Ltac Debug.
        Ltac abstractor_cleanup P :=
          let rec cleanup P :=
              match P with
              | AnyOf ?P1 :: nil => apply AnyOf_singleton in P; admit
              | AnyOf ?PS => cleanup_list PS
              | ?P1 \/ ?P2 => abstractor_cleanup P1; abstractor_cleanup P2
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

        abstractor_cleanup P.

        
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
