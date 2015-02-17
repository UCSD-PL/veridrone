Require Import Compile2.
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
Require Import TLA.Tactics.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Traversable. (* for sequence function *)
Require Import ExtLib.Data.List.
Require Import compcert.flocq.Core.Fcore_defs.
Require Import compcert.flocq.Appli.Fappli_IEEE.
Require Import compcert.flocq.Appli.Fappli_IEEE_bits.
Require Import compcert.common.Events.
Require Import compcert.cfrontend.ClightBigstep.
Require Import Strings.String.
Require Import ExtLib.Programming.Extras.
Import FunNotation.

(* Experiments with semantics follow below this point *)

Print Smallstep.bigstep_semantics.

(* for now, assume output program not divergent *)
(* we will also ignore return value *)

(* these take a default state to fill in if compcert trace contains
   a state that's meaningless in TLA *)

Import MonadNotation.
Local Open Scope monad.
Require Import OptionMonad.
Require Import MonadTrans.

(* compcert trace only records event changes, while TLA records everything *)
Print event.
Check bigstep_program_terminates.

(* State monad, where state is a function mapping variables to values
   This function is "built up" over the course of a translating a trace *)
Definition OVFS := optionT $ state Semantics.state.

Print Semantics.trace.
Print Semantics.state.
Print event.

Definition dummyS : Semantics.state :=
  (fun _ => 42)%R.

(* Add a new var-mapping *)
Definition updS (s : Semantics.state) (v : Var) (r : R) : Semantics.state :=
  (fun name => if (string_dec v name) then r else s v).

(* Does "nth" in varmap, looking up string name for nth variable *)
Eval hnf in OVFS.
Check (mkOptionT (state Semantics.state) Var).

Fixpoint vmnth (vm : list Var) (id : AST.ident) : option Var :=
  match vm with
    | nil       => None
    | vh :: vm' =>
      if (AST.ident_eq id 1)
      then Some vh
      else vmnth vm' (id - 1)%positive
  end.
  
(* For now we actually treat loads and stores pretty much the same. *)
(* toOVFS function - could even use coercion *)

Axiom todo : forall t : Type, t.

Typeclasses eauto := debug.

Print vmnth.

Print eval_formula.

Definition trans_trace_elem (e : event) (vm : list Var) : OVFS Semantics.state :=
  match e return OVFS Semantics.state with
      (* we only need the event value argument *)
    | Event_vload  mc id n ev =>
      match ev with
        | EVfloat f =>
          olds <- MonadState.get (m:=OVFS);;
          mapped <- (vmnth vm id : OVFS Var);;
          put (m:=OVFS) (updS olds mapped f);;
          MonadState.get (m:=OVFS)
        | _ => ret (m:=OVFS) dummyS
      end
    | Event_vstore mc id n ev =>
      match ev with
        | EVfloat f => todo (*
          olds <- MonadState.get;;
          mapped <- vmnth vm id;;
          put (updS olds mapped f);;
          MonadState.get *)
        | _ => ret (m:=OVFS) dummyS
      end
    | _ => ret (m:=OVFS) dummyS (* for now, dummy event *)
  end.

Loc

(* Needs the var-map *)
Fixpoint trans_trace_fin (es : compcert.common.Events.trace) (vm : list Var) : VFS TLA.Semantics.trace :=
  match ctr with
    | nil       => return nil
    | e1 :: es' =>
      
      
      
  
(*Axiom trans_trace_inf : compcert.common.Events.traceinf -> state -> TLA.Semantics.trace.*)

(* to support non-divergent programs we just need to change this to trace*)
(* statement that if a progr compiles to a divergent C program, the (infinite) trace
   will be identical to the TLA version of the trace *)
Theorem compile_correct : forall (p : progr) (tri : compcert.common.Events.traceinf)
                                 (s : state) (retval : int),
                            bigstep_program_terminates (progr_to_clight p) tri retval ->
                            exists ttr,
                              trans_trace_fin tri s = Some ttr /\
                              eval_formula (progr_to_tla p) (ttr).

                            
(* Theorem compile_correct2: 
                            bigstep_program_terminates
                              (progr_to_clight p) (trans_trace_fin tr) retcode /\ *)
                            
*)
