Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.lib.Integers.
Require Import Coq.Reals.Rdefinitions.
Require Import List.
Import ListNotations.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib. Require Import compcert.flocq.Core.Fcore_defs.
Require Import compcert.flocq.Appli.Fappli_IEEE.
Require Import compcert.flocq.Appli.Fappli_IEEE_bits.
Lemma stupid : bounded 53 1024 5 2 = true. 
admit. Qed.
Eval compute in (Floats.Float.add (B754_finite 53 1024 true 5 2 stupid) (B754_finite 53 1024 true 5 2 stupid)).
(*Eval vm_compute in (Floats.Float.add (B754_finite 53 1024 true 5 2 stupid) (B754_finite 53 1024 true 5 2 stupid)).*)
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Traversable. (* for sequence function *)
Require Import ExtLib.Data.List.

Locate ident.
Local Close Scope HP_scope.
Delimit Scope SrcLang_scope with SL.
Local Open Scope SrcLang_scope.

Locate mkprogram.

(* Term, sans the next operator *)
Inductive NowTerm : Type :=
| VarNowN : Var -> NowTerm
| NatN : nat -> NowTerm
(*| RealN : Rdefinitions.R -> NowTerm*)
| FloatN : Floats.float -> NowTerm
| PlusN : NowTerm -> NowTerm -> NowTerm
| MinusN : NowTerm -> NowTerm -> NowTerm
| MultN : NowTerm -> NowTerm -> NowTerm.

(* peeled from Haskell, because it's beautiful *)
Definition app {A B: Type} (f : A -> B) (x : A) : B := f x.
Notation "f $ x" := (app f x) (at level 99, right associativity).

(* peeled from Syntax.v *)
Infix "+" := (PlusN) : SrcLang_scope.
Infix "-" := (MinusN) : SrcLang_scope.
Notation "-- x" := (MinusN (FloatN 0) x)
                     (at level 0) : SrcLang_scope.
Infix "*" := (MultN) : SrcLang_scope.

(* convenient coercions between number formats *)
Definition nat_to_int (n : nat) : int :=
  Int.repr $ Z.of_nat n.

Definition nat_to_float (n : nat) : Floats.float :=
  Floats.Float.of_int $ nat_to_int n.

Coercion nat_to_int : nat >-> int.
Coercion nat_to_float : nat >-> Floats.float.
Coercion Pos.of_nat : nat >-> positive.

Fixpoint pow (t : NowTerm) (n : nat) :=
  match n with
  | O => FloatN 1
  | S n => MultN t (pow t n)
  end.
Notation "t ^^ n" := (pow t n) (at level 10) : SrcLang_scope.

(* we probably need to define more convenience methods/notations
   for this representation *)
Fixpoint denowify (nt : NowTerm) : Term :=
  match nt with
    | VarNowN v => VarNowT v
    | NatN n => NatT n
    | FloatN f => RealT $ B2R _ _ f
    | PlusN t1 t2 => PlusT (denowify t1) (denowify t2)
    | MinusN t1 t2 => MinusT (denowify t1) (denowify t2)
    | MultN t1 t2 => MultT (denowify t1) (denowify t2)
  end.

(* Formula, sans the things we don't need to worry about
   compiling, and without and and or *)
Inductive FlatFormula :=
| FTRUE : FlatFormula
| FFALSE : FlatFormula
| FComp : NowTerm -> NowTerm -> CompOp -> FlatFormula.

(* Comparisons *)
Notation "t1 > t2" := (FComp t1 t2 Gt) : SrcLang_scope.
Notation "t1 >= t2" := (FComp t1 t2 Ge) : SrcLang_scope.
Notation "t1 < t2" := (FComp t1 t2 Lt) : SrcLang_scope.
Notation "t1 <= t2" := (FComp t1 t2 Le) : SrcLang_scope.
Notation "t1 = t2" := (FComp t1 t2 Eq) : SrcLang_scope.
Notation "x <= y <= z" :=
  (And (FComp x y Le) (FComp y z Le)) : SrcLang_scope.

(* Convert a formula to a flat one *)
(*Definition flatten_formula (tla : Formula) : option FlatFormula :=
  match tla with
    | TRUE => Some FTRUE
    | FALSE => Some FFALSE
    | Comp a b c => Some (FComp a b c)
    | _ => None
  end.*)

Definition deflatten_formula (ff : FlatFormula) : Formula :=
  match ff with
    | FTRUE => TRUE
    | FFALSE => FALSE
    | FComp a b c => Comp (denowify a) (denowify b) c
  end.

(* Captures the structure we want each term in our IR to have
   Basically, a list of simultaneous assignments, and a
   list of conditions guarding (all of) those assigments.
   Our program will be a list of these statements. *)

(* eventually this will be our IR, using "unknown" to account for possibility
   of e.g. rounding errors *)

(*
Record progr_stmt : Set :=
  mk_progr_stmt {
      conds : list FlatFormula;
      yes_assns : list (Var * NowTerm);
      unknown_assns : list (Var * NowTerm)
    }.
*)

Record progr_assn : Set :=
  mk_progr_assn {
      pa_dest : Var;
      pa_source : NowTerm
    }.

(* for now we omit "unknown" case for simplicity *)
Record progr_stmt : Set :=
  mk_progr_stmt {
      ps_conds : list FlatFormula;
      ps_assns : list progr_assn
    }.

Notation "a !!= b" := (mk_progr_assn a b) (at level 40) : SrcLang_scope.

Notation "'PIF' cs 'PTHEN' yas" :=
  (mk_progr_stmt cs yas) (at level 60) : SrcLang_scope.

(*
Notation "'PIF' cs 'PTHEN' yas 'PUNKNOWN' unas" := 
  (mk_progr_stmt cs yas unas) (at level 59).
*)
Check (PIF nil PTHEN nil).

Definition progr : Set := list progr_stmt.

(* definition of trace *)
Require Import compcert.common.Events.
Require Import compcert.cfrontend.ClightBigstep.

(* Fold a list with its first element as starting accumulator
   Takes function and list, as well as default element to return if list is nil *)
Definition self_foldr {A : Type} (f : A -> A -> A) (l : list A) (dflt : A) : A :=
  match l with
    | nil => dflt
    | h :: t =>
      List.fold_right f h t
  end.

Definition progr_stmt_to_tla (ps : progr_stmt) : Formula :=
  match ps with
    | mk_progr_stmt conds assns =>
      let convert_assn (assn : progr_assn) :=
          match assn with
            | mk_progr_assn var term => Comp (VarNextT var) (denowify term) Eq
          end
      in
      let conjuncts :=
          List.app (List.map convert_assn assns) (List.map deflatten_formula conds) in
      self_foldr And conjuncts FALSE
  end.

Definition progr_to_tla (pr : progr) : Formula :=
  let disjuncts :=
      List.map progr_stmt_to_tla pr in
  self_foldr Or disjuncts FALSE.

Require Import compcert.lib.Integers.

Local Open Scope string_scope.

Definition derp : progr :=
  ([PIF (FTRUE  ::
        (NatN 1 = NatN 1) :: nil)
   PTHEN ["ab" !!= FloatN 1]])%SL.

(* This hides the nastiness of the definition of B2R, but I don't think it's a long term solution
   In the long run we're going to have to figure out how to deal with converting from real numbers
   into floating point. There's no easy way to go back. *)
Opaque B2R.
Eval compute in (progr_to_tla derp).

(* bool type in C, briefly *)
Locate Tint.
Definition c_bool : type :=
  Tint IBool Signed noattr.

Definition c_float : type :=
  Tfloat F64 noattr.

(* "And" operator in C, briefly *)
Definition c_and (e1 e2 : expr) : expr :=
  Ebinop Oand e1 e2 c_bool.

(* "true" constant in C, briefly *)
Definition c_true : expr.
  refine (Econst_int (Int.mkint 1 _) c_bool).
  compute. auto.
Qed.

(* "false" constant in C, briefly *)  
Definition c_false : expr.
  refine (Econst_int (Int.mkint 0 _) c_bool).
  compute. auto.
Qed.

(* This is going to give us "backwards" place-values for string indices
   but it's not a big deal as long as we do it consistently. *)
(* Also, please don't use null characters or empty strings, these are likely to cause
   problems *)
(*Fixpoint tlavar2N (tlav : Var) : N :=
  match tlav with
    | EmptyString => 0%N
    | String ch rest => 
      let place := N_of_ascii ch in
      (place + 256 * (tlavar2N rest))%N
  end.*)

(*Definition tlavar2c (tlav : Var) : AST.ident :=
  N.succ_pos (tlavar2N tlav).

Definition cvar2tla (id : AST.ident) : Var :=
  Nvar2tla (Pos.pred_N id).*)

(* varmap-state *)
Definition VMS := state (list Var).

(* Utility function for doing lookup in a variable map
   If found, returns the same map and the index of the variable
   Otherwise, returns a new map with variable appended, and new index *)

Import MonadNotation.
Local Open Scope monad.
Require Import String.
(* monadic, but well-formed recursion is not evident *)
(*
Fixpoint lookup_or_add (v : Var) : VMS positive :=
  vm <- get;;
  match vm with
    | nil => put [v];;
             ret 1
    | v1 :: vm' =>
      if (string_dec v v1) then ret 1
      else
        put vm';;
        idx <- lookup_or_add v;;
        vm'' <- get;;
        put (v1 :: vm'');;
        ret (idx + 1)
  end.
 *)

Fixpoint lookup_or_add' (v : Var) (varmap : list Var) : (positive * list Var) :=
  match varmap with
    | nil => (1%positive, v :: nil)
    | v1 :: varmap' =>
      if (string_dec v v1) then
        (1%positive, varmap)
      else
  (* if we can't find it at head, look in tail, then increment index *)
        let (idx, vm') := lookup_or_add' v varmap' in
        ((idx + 1)%positive, v1 :: vm')
  end.

Definition lookup_or_add (v : Var) : VMS positive :=
  vm <- get;;
  let (idx, vm') := lookup_or_add' v vm in
  put vm';;
  ret idx.

(* Helper routines for converting from source language to C *)
Fixpoint nowTerm_to_clight (nt : NowTerm) : VMS expr :=
  match nt with
    | VarNowN var =>
      idx <- lookup_or_add var;;
      ret $ Evar idx c_float
    | NatN n =>
      ret $ Econst_float (nat_to_float n) c_float
    | FloatN f =>
      ret $ Econst_float f c_float
    | PlusN nt1 nt2 =>
      clnt1 <- nowTerm_to_clight nt1;;
      clnt2 <- nowTerm_to_clight nt2;;
      ret $ Ebinop Oadd clnt1 clnt2 c_float
    | MinusN nt1 nt2 =>
      clnt1 <- nowTerm_to_clight nt1;;
      clnt2 <- nowTerm_to_clight nt2;;
      ret $ Ebinop Osub clnt1 clnt2 c_float
    | MultN nt1 nt2 =>
      clnt1 <- nowTerm_to_clight nt1;;
      clnt2 <- nowTerm_to_clight nt2;;
      ret $ Ebinop Omul clnt1 clnt2 c_float
  end.

Definition progr_assn_to_clight (assn : progr_assn) : VMS statement :=
  match assn with
    | mk_progr_assn dst src =>
      dst_idx <- lookup_or_add dst;;
      rhs <- nowTerm_to_clight src;;
      ret $ Sassign (Evar dst_idx c_float) rhs
  end.

Definition compOp_to_binop (cmp : CompOp) : binary_operation :=
  match cmp with
    | Gt => Ogt
    | Ge => Oge
    | Lt => Olt
    | Le => Ole
    | Eq => Oeq
  end.

Definition flatFormula_to_clight (ff : FlatFormula) : VMS expr :=
  match ff with
    | FTRUE => ret c_true
    | FFALSE => ret c_false
    | FComp nt1 nt2 cmp =>
      clnt1 <- nowTerm_to_clight nt1;;
      clnt2 <- nowTerm_to_clight nt2;;
      ret $ Ebinop (compOp_to_binop cmp) clnt1 clnt2 c_bool
  end.

(* TODO define mapM function. I don't want to take the time right now to figure
   out its fully general type signature... *)

(* converts a single progr_stmt to an "if" statement in Clight *)
(* in the process, builds up a table mapping source-language variable names
   to target-language positive indices *)
Definition progr_stmt_to_clight (ps : progr_stmt) : VMS statement :=
  match ps with
    | mk_progr_stmt conds assns =>      
      let convd_conds := map flatFormula_to_clight conds in
      let convd_assns := map progr_assn_to_clight assns in
      cconds <- sequence convd_conds;;
      cassns <- sequence convd_assns;;
      let if_condition :=
          self_foldr (fun l r => Ebinop Oand l r c_bool) cconds c_false
      in
      let if_body :=
          self_foldr Ssequence cassns Sskip
      in
      ret $ Sifthenelse if_condition if_body Sskip
  end.  

(* needed for correctly packing into the function record *)
(* for now we cheat because all our variables are floats. In the long run we
   may not be able to get away with this and may need to start including types
   in the var-map *)
Fixpoint varmap_to_typed_idents (vm : list Var) (p : positive) : list (AST.ident * type) :=
  match vm with
    | nil => nil
    | _ :: vm' =>
      (p, c_float) :: varmap_to_typed_idents vm' (p + 1)%positive
  end.  

(* this function probably exists somewhere else *)
Definition ltail {A : Type} (l : list A) : list A :=
  match l with
    | nil => nil
    | _ :: t => t
  end.

(* almost there - first, define a helper function that computes the program
   within the state monad *)

(* pretty printer gets calling convention backwards?
   we need to say we support varargs in order to have pretty printer not say (...) *)
Definition default_cc :=
  {| AST.cc_vararg := true; AST.cc_structret := false|}.

Definition progr_to_clight' (pr : progr) : VMS program :=
  prog_stmts <- sequence $ map progr_stmt_to_clight pr;;
  vm <- get;;
  let prog_body := self_foldr Ssequence prog_stmts Sskip in
  (* now we need to pack the program structure appropriately *)
  let funrec :=
      {| (* no return now; that may change *)
         fn_return := Tvoid;

         fn_callconv := default_cc;
         (* no params right now; that may change *)
         fn_params := nil;
         (* main is number 1, so rest of vars must start at 2 *)
         fn_vars := varmap_to_typed_idents (ltail vm) 2%positive;
         fn_temps := nil;
         fn_body := prog_body
      |}
  in
  let globdefs :=
      [(1%positive, AST.Gfun (Internal funrec))]
  in
  let main_id := 1%positive in
  ret $ AST.mkprogram globdefs main_id.

(* Beginning var-map; includes main function *)
Definition init_state := ["main"].

Definition progr_to_clight (pr : progr) : (program) :=
  let pVMS := progr_to_clight' pr in
  evalState pVMS init_state.

(* Pretty-printing adapter utilities below *)

(* Convert string into list of chars *)
Require Import String.
Check String.String.
Fixpoint str_to_nats (s : String.string) : list nat :=
  match s with
    | String.String a s' =>
      (nat_of_ascii a) :: (str_to_nats s')
    | EmptyString => nil
  end.

(* Convert var list for easier input into pretty printer
   Which expects a hash table from positive -> string.
   We do the hashtable conversion in ML. *)

Fixpoint convert_var_list' (l : list Var) (p : positive) : list (positive * (list nat)) :=
  match l with
    | nil => nil
    | h :: t =>
      (p, str_to_nats h) :: convert_var_list' t (p + 1)%positive
  end.

Definition convert_var_list (l : list Var) : list (positive * (list nat)) :=
  convert_var_list' l 1%positive.

(* Emit program and converted version of its var list *)
Definition prepare_pretty_print (pr : progr) : (program * list (positive * list nat)) :=
  let (prog, vars) := runState (progr_to_clight' pr) init_state in
  (prog, convert_var_list vars).

(* You have to unpack and repack because I have no idea how to unpack Coq pairs in Ocaml >:( *)
(*Definition cfst := @fst (positive * list nat).
Definition csnd := @snd (positive * list nat).*)

Definition ex_derp_prog := fst (prepare_pretty_print derp).
Definition ex_derp_vars := snd (prepare_pretty_print derp).
Definition coqmap := map.
(* Package everything upto extract it all at once *)
Definition extract_derp := (ex_derp_prog, ex_derp_vars, coqmap).
Extraction "derp.ml" extract_derp.

Check fold_right.

Eval compute in (progr_to_clight derp).
Print binary_float.
Check Econst_float.

(* Experiments with semantics follow below this point *)

Check bigstep_semantics.
Locate bigstep_semantics.
Print bigstep_semantics.
Print Smallstep.bigstep_semantics.
(* for now, assume output program not divergent *)
(* these take a default state to fill in if compcert trace contains
   a state that's meaningless in TLA *)
(*Axiom trans_trace_fin : compcert.common.Events.trace -> state -> TLA.Semantics.trace.
Axiom trans_trace_inf : compcert.common.Events.traceinf -> state -> TLA.Semantics.trace.

(* to support non-divergent programs we just need to change this to trace*)
(* statement that if a progr compiles to a divergent C program, the (infinite) trace
   will be identical to the TLA version of the trace *)
Theorem compile_correct : forall (p : progr) (tri : compcert.common.Events.traceinf)
                                 (s : state),
                            bigstep_program_diverges (progr_to_clight p) tri ->
                            eval_formula (progr_to_tla p) (trans_trace_inf tri s).

                            
(* Theorem compile_correct2: 
                            bigstep_program_terminates
                              (progr_to_clight p) (trans_trace_fin tr) retcode /\ *)
                            
*)

Local Open Scope HP_scope.

Definition clightExpr expr := evalState (nowTerm_to_clight expr) nil.

Require Import Coq.Reals.Raxioms.
Require Import compcert.flocq.Appli.Fappli_IEEE.
Require Import compcert.flocq.Core.Fcore_Raux.
Require Import compcert.flocq.Core.Fcore_generic_fmt.
Definition e := bpow radix2 (- (53) + 1). 
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Reals.RIneq.
Local Open Scope HP_scope.

Definition lowerBound x := if Rgt_dec x 0 then (x*(RealT R1 - RealT e))  else   (x*(RealT R1 + RealT e)).
Definition upperBound x := if Rgt_dec x 0 then  (x*(RealT R1 + RealT e))  else  (x*(RealT R1 - RealT e)).

Definition custom_prec := 53%Z.
Print Floats.float.
Print binary64.
Print binary_float.



Definition custom_emax:= 1024%Z.
Print Floats.Float.binop_pl.
Print Archi.default_pl_64.
Print Z_of_nat'.
Definition custom_float_zero  := B754_zero custom_prec custom_emax true.

Definition custom_nat_to_float (n:nat):= B754_zero custom_prec custom_emax true.

Print Floats.float.
Print binary64.
Print binary_float.
Print Nat.

SearchAbout (nat-> Floats.float). 
Print nat_to_float.
Print INR.

Fixpoint custom_eval_expr (t:NowTerm) := match t with 
| VarNowN var  => custom_float_zero 
| NatN n =>  nat_to_float n
| FloatN f => f  
| PlusN t1 t2 => Bplus custom_prec custom_emax eq_refl eq_refl Floats.Float.binop_pl mode_NE (custom_eval_expr t1) (custom_eval_expr t2)  (*need to figure out what to do with Floats.Float.binop_pl - this is some architecture related stuff to handle Nan type values*) (*also may want to have different additions for different kinds of numbers*)
| MultN t1 t2 => custom_float_zero
| MinusN t1 t2 => custom_float_zero
end.



Fixpoint bound_term x := match x with
| VarNowN var => (RealT R0,RealT R0 )
| NatN n => (RealT (INR n),RealT (INR n))
| FloatN f => (RealT (B2R _ _ f), RealT (B2R _ _ f))
| PlusN t1 t2 => (((fst (bound_term t1) + fst (bound_term t2))* (RealT R1 - RealT e)) ,
((snd (bound_term t1) + snd (bound_term t2))* (RealT R1 + RealT e)))
| MinusN t1 t2 => (((fst (bound_term t1) - snd (bound_term t2))* (RealT R1 - RealT e)) ,
((snd (bound_term t1) - fst (bound_term t2)) * (RealT R1 + RealT e)))
| MultN t1 t2 => (((fst (bound_term t1)* fst (bound_term t2)) * (RealT R1 - RealT e)) ,
((snd (bound_term t1) * snd (bound_term t2))* (RealT R1 + RealT e)))
end.





Definition valToR val := match val with 
| Values.Vfloat f => B2R _ _ f
| _ => R0 (*need to implement this for other things as well*)
end.  
Local Close Scope HP_scope.
Local Close Scope SrcLang_scope.
Local Open Scope R_scope.
Print eval_expr.
Print expr.
Print type.
Print attr.
Print floatsize.
Print sem_binary_operation.
Print sem_add.
Print sem_binarith.
Print sem_cast.
Print classify_cast.
Require Import compcert.flocq.Appli.Fappli_IEEE.
Print is_finite.
Require Import compcert.flocq.Core.Fcore_Raux.
Print Rlt_bool.
Require Import compcert.flocq.Core.Fcore_generic_fmt.



Definition newBound expr s1 s2 :=
eval_term (fst (bound_term expr)) s1 s2 <= B2R _ _ (custom_eval_expr expr) <=  eval_term (snd (bound_term expr)) s1 s2.

Print Bplus.
Print Floats.float.
Print binary64.
Print  binary_float.
Eval compute in  B754_zero 53%Z 1024%Z true.




Fixpoint bound expr s1 s2:= match expr with
| PlusN x1 x2 =>  (forall fx1 fx2, ((B2R 53 1024 fx2 + B2R 53 1024 fx1) >= 0)-> (Rlt_bool (Rabs (round radix2 (Fcore_FLT.FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (B2R 53 1024 fx2 + B2R 53 1024 fx1))) (bpow radix2 1024) = true) /\ is_finite 53 1024 fx1 = true /\ is_finite 53 1024 fx2 = true /\ (((eval_term (fst (bound_term x1)) s1 s2)%R <= (B2R _ _ fx1)%R <=
(eval_term (snd (bound_term x1)) s1 s2)%R) /\ ((eval_term (fst (bound_term x2)) s1 s2)<= B2R _ _ fx2 <=
                                               (eval_term (snd (bound_term x2)) s1 s2))) -> ((forall ge e te mem val,
((eval_expr ge e te mem (clightExpr (PlusN (FloatN fx1) (FloatN fx2))) val)) ->
((eval_term (fst (bound_term expr)) s1 s2) <= (valToR val) <= (eval_term (snd (bound_term expr)) s1 s2)))))
| MultN x1 x2 => (forall fx1 fx2, (((eval_term (fst (bound_term x1)) s1 s2)%R <= (B2R _ _ fx1)%R <=
(eval_term (snd (bound_term x1)) s1 s2)%R) /\ ((eval_term (fst (bound_term x2)) s1 s2)<= B2R _ _ fx2 <=
(eval_term (snd (bound_term x2)) s1 s2))) -> ((forall ge e te mem val,
((eval_expr ge e te mem (clightExpr (MultN (FloatN fx1) (FloatN fx2))) val)) ->
((eval_term (fst (bound_term expr)) s1 s2) <= (valToR val) <= (eval_term (snd (bound_term expr)) s1 s2)))))
| MinusN x1 x2 => (forall fx1 fx2, (((eval_term (fst (bound_term x1)) s1 s2)%R <= (B2R _ _ fx1)%R <= (eval_term (snd (bound_term x1)) s1 s2)%R) /\ ((eval_term (fst (bound_term x2)) s1 s2)<= B2R _ _ fx2 <= (eval_term (snd (bound_term x2)) s1 s2))) -> ((forall ge e te mem val,
((eval_expr ge e te mem (clightExpr (MinusN (FloatN fx1) (FloatN fx2))) val)) -> ((eval_term (fst (bound_term expr)) s1 s2) <= (valToR val) <= (eval_term (snd (bound_term expr)) s1 s2)))))
| NatN n => True
| FloatN f => True
| VarNowN var => True (*this needs to changed*)
end.


Print eval_expr.
Print sem_binary_operation.
Print sem_add.
Print Floats.Float.add.
Print b64_plus.
Print eval_expr.


Eval compute in (Floats.Float.add (B754_finite 53 1024 true 5 2 stupid) (B754_finite 53 1024 true 5 2 stupid)).

Print B754_finite. 
Definition num:= B754_finite 53 1024 true 5 2 stupid.
Eval vm_compute in (B2R _ _ num).


Print B2R.
Print Floats.Float.add.
Print b64_plus.
Print Bplus. 
Check Bplus.
Check (Bplus 53 1024 eq_refl eq_refl Floats.Float.binop_pl mode_NE  (B754_finite 53 1024 true 5 2 stupid) (B754_finite 53 1024 true 5 2 stupid)).


Check B754_finite.
Definition num3 := (B754_finite 53 1024 true 1 53 stupid).
Require Import compcert.flocq.Appli.Fappli_IEEE.
Require Import compcert.flocq.Core.Fcore_generic_fmt.
Check round.

Print round.
Require Import compcert.flocq.Core.Fcore_Zaux.
Print radix.
Lemma ten: (2<=? 10)%Z =  true.
intuition.
Qed.
Definition rad10:=Build_radix 10 ten.
Print canonic_exp.
Print positive.
Definition fe (x:Z) := (x-2)%Z.
Eval vm_compute in (canonic_exp rad10 fe 124).
Print scaled_mantissa.
Print canonic_exp. 
Print radix.
Lemma tenGtZero : (2 <=? 10)%Z = true. 
intuition.
Qed.
(*Definition radix2 := Build_radix 2 tenGtZero.
Definition prec := 3%Z.
Definition emax := 128%Z.
Definition emin:= (3 - emax - prec)%Z.*)
Require Import compcert.flocq.Appli.Fappli_IEEE.
Require Import compcert.flocq.Core.Fcore_FLT.
Print FLT_exp.
(*
Definition FLT_exp emin prec e:= Zmax (e - prec) emin.
Definition fexp  := FLT_exp emin prec.
Print round.
Print binary_float.
Print Bplus.
Definition roundPlus radix fexp rnd (x:binary_float prec emax) (y:binary_float prec emax) := round radix fexp rnd (B2R _ _ x + B2R _ _ y).
Print binary_float.
Print bounded.
Lemma bounded_proof_num1 : bounded prec emax 7 0 = true.
unfold bounded. unfold canonic_mantissa.
Eval compute in  (Z.of_nat (S (Fcore_digits.digits2_Pnat 7))).
Eval compute in (Fcore_FLT.FLT_exp (3 - emax - prec) prec
         (Z.of_nat (S (Fcore_digits.digits2_Pnat 7)) + 0)).
compute.
intuition.
Qed.

Lemma bounded_proof_num2 : bounded prec emax 4 0 = true.
compute.
intuition.
Qed.
Lemma bounded_proof_error :  bounded 53 1024 1 (1-prec) = true.
unfold bounded.
unfold canonic_mantissa.
Eval compute in  (Fcore_digits.digits2_Pnat 1).
Print Fcore_FLT.FLT_exp.
Eval compute in (Z.of_nat (S (Fcore_digits.digits2_Pnat 1)) + (1 - 3))%Z.
Eval compute in (S (Fcore_digits.digits2_Pnat 1)).
Eval compute in (1-prec)%Z.
Eval compute in (Fcore_FLT.FLT_exp (3 - 1024 - 53) 53
         (Z.of_nat (S (Fcore_digits.digits2_Pnat 1)) + (1 - prec))).
Eval compute in (1-prec)%Z.
compute.
intuition.
admit.
Qed.

Definition num1 :=  (B754_finite prec emax false 7 0 bounded_proof_num1).
Definition num2 := (B754_finite prec emax false 4 0 bounded_proof_num2).*)
Require Import compcert.flocq.Core.Fcore_rnd_ne. 
Require Import compcert.flocq.Core.Fcore_Raux.
(*Definition error:=  (B754_finite prec emax false 1 (1-prec) bounded_proof_error).*)
Require Import compcert.flocq.Core.Fcore_generic_fmt.
Print Znearest.
Definition choice (num:Z) := true. 
Definition roundToNearest := Znearest choice.
(*
Definition roundPlusEx1 num1 num2:= roundPlus radix2 fexp roundToNearest num1 num2.
Lemma add1Le0 : forall x, (x  < 0)%Z -> (x  + 1<= 0)%Z.
intros. 

Require Import Coq.micromega.Psatz.
lia.
Qed.
Print fexp.
Print Valid_exp.
Locate Valid_exp.
Lemma fexpValidity : Valid_exp fexp. 
unfold Valid_exp.
Print fexp.
Print FLT_exp .
intros.
split.
intros.
unfold fexp in *.
unfold FLT_exp in *.
unfold Z.max in *.
(*remember (k - prec ?=emin)%Z as val.*)
destruct (k - prec ?=emin)%Z eqn:val.

destruct (k + 1 - prec ?= emin)%Z eqn:val1.
lia. 
SearchAbout (_?=_)%Z.
SearchAbout (_<->_).
apply Z.compare_eq in val.
lia. apply Z.compare_eq in val.
lia.
 SearchAbout (_?=_)%Z. pose proof Z.compare_lt_iff.
unfold iff in H0.
specialize (H0 (k-prec)%Z emin).
inversion H0.
apply H1 in val.
destruct (k + 1 - prec ?= emin)%Z eqn:val1.
lia. lia. lia. 
 SearchAbout (_?=_)%Z.
pose proof Z.compare_gt_iff.  
specialize (H0 (k-prec)%Z  emin).
inversion H0.
apply H1 in val.
destruct (k + 1 - prec ?= emin)%Z eqn:val1. 
apply Z.compare_eq in val1.
lia. lia. lia.  
intros. split.
unfold fexp in *.
Print FLT_exp.
unfold FLT_exp in *.
unfold Zmax in *.
destruct (k - prec ?= emin)%Z eqn:val.
apply Z.compare_eq in val.
destruct (k - prec + 1 - prec ?= emin)%Z eqn:val1.
apply Z.compare_eq in val1.
lia.
pose proof Z.compare_lt_iff.
specialize (H0 (k-prec+1-prec)%Z  emin).
inversion H0.
apply H1 in val1.
lia.
pose proof Z.compare_gt_iff.
specialize (H0 (k-prec+1-prec)%Z  emin).
inversion H0.
apply H1 in val1.
admit. admit. admit. admit. 
Qed.
*)
Lemma imp : forall x y, x -> (x->y) -> y.
firstorder.
Qed.
Require Import Coq.micromega.Psatz.
Lemma addProof : forall x y, x>=0 -> y>=0 -> x+y >=0.
intros. psatzl R.
Qed.
(*
Eval vm_compute in (B2R prec emax num1 + B2R prec emax num2) * (1 + B2R prec emax error).
unfold roundPlusEx1.
intros.
unfold roundPlus.
Require Import compcert.flocq.Prop.Fprop_relative.
pose proof relative_error.
pose radix2.
pose fexp.
specialize (H1 radix2 fexp).
pose proof fexpValidity.
pose emin.
pose prec.

apply imp in H1. 
specialize (H1 emin prec).
apply imp in H1.
Print round.
specialize (H1 roundToNearest).
apply imp in H1.
pose (B2R prec emax num4).
pose (B2R prec emax num5).
specialize (H1 ((B2R prec emax num4) + (B2R prec emax num5))).
apply imp in H1.
pose  (round radix2 fexp roundToNearest (B2R prec emax num4 + B2R prec emax num5)-(B2R prec emax num4 + B2R prec emax num5)).
destruct (Rge_dec (round radix2 fexp roundToNearest (B2R prec emax num4 + B2R prec emax num5)-(B2R prec emax num4 + B2R prec emax num5)) R0).
Require Import compcert.flocq.Core.Fcore_ulp.
pose proof Rabs_right.
specialize (H3 (round radix2 fexp (roundToNearest) (B2R prec emax num4 + B2R prec emax num5) -
        (B2R prec emax num4 + B2R prec emax num5))).
apply H3 in r3.
rewrite r3 in H1.
pose proof addProof.
specialize (H4 (B2R prec emax num4) (B2R prec emax num5)).
apply H4 in H.
pose proof Rabs_right.
specialize (H5 (B2R prec emax num4 + B2R prec emax num5)).
apply H5 in H.
rewrite H in H1.
clear H H0 r z H2 z0 z1 r0 r1 r2 r3.
clear H3 H4 H5.
psatz R.
apply H0.
pose proof Rabs_left.
specialize (H3  (round radix2 fexp roundToNearest
          (B2R prec emax num4 + B2R prec emax num5) -
        (B2R prec emax num4 + B2R prec emax num5))).
pose proof Rnot_ge_gt.
apply H4 in n.
pose proof Rgt_lt.
apply H5 in n.
apply H3 in n.
rewrite n in H1.

admit. admit.
admit.
admit. admit.
Qed
Print round.


*)

Print eval_expr.

Lemma new_bound_proof : (forall (tr:Semantics.trace) expr, (newBound expr (Semantics.hd tr) (Semantics.hd (Semantics.tl tr)))).
unfold newBound.

intros tr expr.
induction expr.
+ unfold custom_eval_expr.
unfold bound_term.
simpl.
unfold custom_float_zero.
Transparent B2R.
unfold B2R.
intuition.

+ unfold bound_term.

induction n.
*
vm_compute.
intuition.
* simpl in *.
unfold B2R in *.
compute in *.
admit. (*proving bound of natural numbers*)
+ simpl.
intuition.
+ unfold custom_eval_expr.
remember ((fix custom_eval_expr (t : NowTerm) :
            binary_float custom_prec custom_emax :=
            match t with
            | VarNowN _ => custom_float_zero
            | NatN n => nat_to_float n
            | FloatN f => f
            | (t1 + t2)%SL =>
                Bplus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (_ - _)%SL => custom_float_zero
            | (_ * _)%SL => custom_float_zero
            end) expr1) as eval_expr.
remember ((fix custom_eval_expr (t : NowTerm) :
            binary_float custom_prec custom_emax :=
            match t with
            | VarNowN _ => custom_float_zero
            | NatN n => nat_to_float n
            | FloatN f => f
            | (t1 + t2)%SL =>
                Bplus custom_prec custom_emax eq_refl eq_refl
                  Floats.Float.binop_pl mode_NE (custom_eval_expr t1)
                  (custom_eval_expr t2)
            | (_ - _)%SL => custom_float_zero
            | (_ * _)%SL => custom_float_zero
            end) expr2) as eval_expr2.


unfold custom_eval_expr in IHexpr1.
unfold custom_eval_expr in IHexpr2.

rewrite <-  Heqeval_expr2 in IHexpr2. 
rewrite <- Heqeval_expr in IHexpr1.
clear Heqeval_expr2 Heqeval_expr.

Print Bplus_correct.

pose proof Bplus_correct as bplus_correct.
specialize (bplus_correct custom_prec custom_emax eq_refl eq_refl Floats.Float.binop_pl mode_NE eval_expr eval_expr2).

destruct eval_expr eqn:eval_expr_des.  
* admit. (*zero case*) 
* admit. (*infinty case*)
* admit. (*nan case*)
* 
destruct eval_expr2 eqn:eval_expr2_des.
- admit. (*zero case*) 
- admit. (*infinty case*)
- admit. (*nan case*)
-   unfold is_finite in bplus_correct. 
Lemma truth : true = true.
intuition.
Qed.
specialize (bplus_correct truth).
specialize (bplus_correct truth).
remember (Rlt_bool (Rabs (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (B2R custom_prec custom_emax eval_expr + B2R custom_prec custom_emax eval_expr2)))  (bpow radix2 custom_emax)) as rltBoolInfo.  destruct rltBoolInfo.
subst.
destruct b eqn:b_des.
{*

destruct b0 eqn:b_des2.
+
rewrite <- HeqrltBoolInfo in bplus_correct.
decompose [and] bplus_correct.  
rewrite H. 

split.
- unfold bound_term in *.
remember (fst ((fix bound_term (x : NowTerm) : Term * Term :=
                     match x with
                     | VarNowN _ => (RealT 0, RealT 0)
                     | NatN n => (RealT (INR n), RealT (INR n))
                     | FloatN f =>
                         (RealT (B2R 53 1024 f), RealT (B2R 53 1024 f))
                     | (t1 + t2)%SL =>
                         (((fst (bound_term t1) + fst (bound_term t2)) *
                           (RealT 1 - RealT e))%HP,
                         ((snd (bound_term t1) + snd (bound_term t2)) *
                          (RealT 1 + RealT e))%HP)
                     | (t1 - t2)%SL =>
                         (((fst (bound_term t1) - snd (bound_term t2)) *
                           (RealT 1 - RealT e))%HP,
                         ((snd (bound_term t1) - fst (bound_term t2)) *
                          (RealT 1 + RealT e))%HP)
                     | (t1 * t2)%SL =>
                         ((fst (bound_term t1) * fst (bound_term t2) *
                           (RealT 1 - RealT e))%HP,
                         (snd (bound_term t1) * snd (bound_term t2) *
                          (RealT 1 + RealT e))%HP)
                     end) expr1)) as lb1.

remember  (fst
                 ((fix bound_term (x : NowTerm) : Term * Term :=
                     match x with
                     | VarNowN _ => (RealT 0, RealT 0)
                     | NatN n => (RealT (INR n), RealT (INR n))
                     | FloatN f =>
                         (RealT (B2R 53 1024 f), RealT (B2R 53 1024 f))
                     | (t1 + t2)%SL =>
                         (((fst (bound_term t1) + fst (bound_term t2)) *
                           (RealT 1 - RealT e))%HP,
                         ((snd (bound_term t1) + snd (bound_term t2)) *
                          (RealT 1 + RealT e))%HP)
                     | (t1 - t2)%SL =>
                         (((fst (bound_term t1) - snd (bound_term t2)) *
                           (RealT 1 - RealT e))%HP,
                         ((snd (bound_term t1) - fst (bound_term t2)) *
                          (RealT 1 + RealT e))%HP)
                     | (t1 * t2)%SL =>
                         ((fst (bound_term t1) * fst (bound_term t2) *
                           (RealT 1 - RealT e))%HP,
                         (snd (bound_term t1) * snd (bound_term t2) *
                          (RealT 1 + RealT e))%HP)
                     end) expr2)) as lb2.
unfold fst.


clear Heqlb1 Heqlb2 bplus_correct HeqrltBoolInfo H1 H H2.
remember (B2R custom_prec custom_emax
              (B754_zero custom_prec custom_emax true)) as eval_expr.
compute in Heqeval_expr.
subst. 
Require Import compcert.flocq.Prop.Fprop_relative.
pose proof relative_error as Rel_Err.
remember (FLT_exp (3 - custom_emax - custom_prec) custom_prec) as round_fexp.
specialize (Rel_Err radix2 round_fexp).
Lemma validFexpProof : Valid_exp  (FLT_exp (3 - custom_emax - custom_prec) custom_prec).
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
specialize (Rel_Err (3-custom_emax-custom_prec)%Z custom_prec).

Lemma precThm: (forall k : Z, ((3-custom_emax-custom_prec) < k)%Z -> (custom_prec <= k - FLT_exp (3-custom_emax - custom_prec) custom_prec k)%Z).
intros.
unfold custom_emax in *. unfold custom_prec in *. unfold FLT_exp. 
unfold Z.max.
Search (Z->Z -> {_}+{_}).
pose proof Z_lt_ge_dec ((k - 53)%Z) ((3 - 1024 - 53)%Z).
pose (k - 53 ?= 3 - 1024 - 53)%Z.
Print Datatypes.Eq.
Search (_ -> Datatypes.comparison).
Print Cge.

destruct H0. simpl in *. 


admit. admit.

Qed.

specialize (Rel_Err precThm (round_mode mode_NE)).
Definition choiceDef := (fun x => negb (Zeven x)).
specialize (Rel_Err (valid_rnd_N choiceDef)).
remember (B754_finite custom_prec custom_emax true m e0 e1) as f.
remember (B754_finite custom_prec custom_emax true m0 e2 e3) as f0.

specialize (Rel_Err ((B2R custom_prec custom_emax f +
      B2R custom_prec custom_emax f0))).
destruct (Rle_dec  (bpow radix2 (3 - custom_emax - custom_prec))  (Rabs (B2R custom_prec custom_emax f + B2R custom_prec custom_emax f0))) as [noUnderflow|underflow].
apply Rel_Err in noUnderflow.
unfold custom_prec, custom_emax in *.

Lemma three : forall x1 x2 x3,  x1 <=x2 <= x3 -> x1 <= x2. 
intros.
intuition.
Qed.
pose proof three as three. 
apply three in IHexpr2.
apply three in IHexpr1.
destruct (Rge_dec (B2R 53 1024 f + B2R 53 1024 f0) R0) as [suml|sumg]. {+ 
destruct (Rge_dec (round radix2 (FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (B2R 53 1024 f + B2R 53 1024 f0) -(B2R 53 1024 f + B2R 53 1024 f0)) R0) as [roundg | roundl].
-
unfold Rabs in *.
destruct Rcase_abs in noUnderflow.
*   psatz R.
* destruct Rcase_abs in noUnderflow. 
{+ psatz R.
}
{
+

 
unfold eval_term in *. 
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r1 => r1
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) lb1 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb1.
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r1 => r1
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) lb2 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb2.
revert IHexpr1. intros IHexpr1.
revert IHexpr2. intros IHexpr2.
unfold e.


remember (round radix2 (FLT_exp (3 - 1024 - 53) 53) 
             (round_mode mode_NE) (B2R 53 1024 f + B2R 53 1024 f0)) as roundedValue.
remember (B2R 53 1024 f) as f1.
remember (B2R 53 1024 f0) as f2.
clear Heqelb1 r0 three r Rel_Err Heqelb2 H noUnderflow expr1 expr2 lb1  Heqf2 Heqf0 e3 Heqf Heqf1 HeqroundedValue  tr m e0 e1 f f0 m0 e2 lb2 .
simpl.
psatz R.
}
- unfold Rabs in noUnderflow.
destruct Rcase_abs in noUnderflow.

* destruct Rcase_abs in noUnderflow. 

admit. (*the case when the sum is negative*)

unfold eval_term in *.

remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r1 => r1
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) lb1 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb1.
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r1 => r1
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) lb2 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb2.

revert IHexpr1 IHexpr2.
intros IHexpr1 IHexpr2.
clear  expr1 expr2 m e0 e1 lb1  Heqf  Heqelb1 Heqf0 Heqelb2 e2 e3  H Rel_Err roundl  lb2 tr m0  three.
unfold e in *.
simpl in *.
psatz R.
* destruct Rcase_abs in noUnderflow.
admit. (*the case when the sum is negative*)

unfold eval_term in *.
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r1 => r1
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) lb1 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb1.
remember ((fix eval_term (t : Term) (s1 s2 : Semantics.state) {struct t} : R :=
       match t with
       | VarNowT x => s1 x
       | (x) !%HP => s2 x
       | NatT n => INR n
       | RealT r1 => r1
       | (t1 + t2)%HP => eval_term t1 s1 s2 + eval_term t2 s1 s2
       | (t1 - t2)%HP => eval_term t1 s1 s2 - eval_term t2 s1 s2
       | (t1 * t2)%HP => eval_term t1 s1 s2 * eval_term t2 s1 s2
       end) lb2 (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))) as elb2.

unfold e in *.
simpl in *.
psatz R.
}

admit. (*the case when the sum is negative*)

admit. (*the case when there is underflow*)
-


 remember (round radix2 (FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (B2R 53 1024 f + B2R 53 1024 f0)) as roundedValue.
remember ((B2R 53 1024 f + B2R 53 1024 f0)) as trueValue.
remember (bpow radix2 (- (53) + 1)) as error.




apply three in IHexpr2.

unfold round.  unfold scaled_mantissa.
unfold canonic_exp. unfold F2R. unfold Z2R.
simpl.  
vm_compute.

apply three in IHexpr2.

eapply bplus_correct in HeqrltBoolInfo.
Print binary_float.




simpl in bplus_correct. 
remember (Rlt_bool (Rabs (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_NE) (B2R custom_prec custom_emax fx1 + B2R custom_prec custom_emax fx2)))  (bpow radix2 custom_emax)) as rltBoolInfo.
unfold round in bplus_correct.

specialize (bplus_correct X).
specialize (bplus_correct (is_finite custom_prec custom_emax eval_expr)).


* admit. (*VarNowN*)
* admit. (*NatN later*)
* intros val HClight.
compute in HClight.
 inversion HClight.

intuition.
admit. (*inversion of HClight for (clightExpr (FloatN f)) results in two goals - one containing a floating value and another containing a pointer containing a floating value*)
* intros val HClight.
unfold  clightExpr, nowTerm_to_clight,evalState,runState  in HClight. simpl in HClight. 
inversion HClight.
clear HClight.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit. admit.
* admit. 
* admit.  
Qed.
(*
inversion HClight. 
Print eval_expr. 
unfold  clightExpr, nowTerm_to_clight,evalState,runState  in HClight.

inversion HClight.
Print eval_expr.
unfold clightExpr in *.
unfold nowTerm_to_clight in *.

compute in H0.
inversion H0.
* unfold bound_term.
unfold clightExpr in *.

unfold valToR.
intuition.
admit. (*inversion of HClight for (clightExpr (FloatN f)) results in two goals - one containing a floating value and another containing a pointer containing a floating value*)
inversion HClight.
Print eval_expr.

Print eval_expr. 
Print Econst_int.
Print clightExpr.
simpl in *.
Print eval_expr.
unfold clightExpr in H0.
unfold nowTerm_to_clight in H0.

inversion H0.


admit.
admit.
admit.
admit.
unfold clightExpr in H0.
unfold nowTerm_to_clight in H0.

Print Econst_int.

Print Econst_int.


induction expr1.
induction expr2.
admit. (*addition of two VarNowNs*)
admit. (*addition of VarNowN and NatN*)
admit. (*addition of VarNowN and FloatN*)

admit. 
admit. (**)
inversion HClight.


Admitted.
*)
Lemma bound_proof : (forall (tr:Semantics.trace) expr, (bound expr (Semantics.hd tr) (Semantics.hd (Semantics.tl tr)))).

intros.
simpl in *.
unfold bound.
simpl in *.
destruct expr eqn:val.
- intuition. 
- intuition. 
- intuition.
- destruct n1 eqn:expr1. (*this is for the case n1+n2*)
admit. (* admitting the case when n1 is VarNowN*)
admit. (* admitting the case when n2 is NatN*)
(*solving the case when n1 is FloatN f*)

destruct n2 eqn:expr2.
admit. (*admitting the case when n2 is VarNowN*)
admit. (*admitting the case when n2 is NatN*)


+  intros fx1 fx2 H H0 ge e0 te mem val0 H1. 
Print eval_expr.
Print Values.val.
inversion H1.
Print Values.val.
 unfold sem_binary_operation in H9. unfold typeof in H9.
Print Values.val.
inversion H7. inversion H8.
* subst;simpl.
unfold c_float in *.
unfold sem_add in H9.
unfold classify_add in H9.
unfold typeconv in H9.
unfold remove_attributes in H9.
unfold change_attributes in H9.
unfold sem_binarith in H9.
unfold sem_cast in H9.
unfold classify_cast in H9.
unfold binarith_type in H9.
unfold classify_binarith in H9.
Transparent Floats.Float.add.
unfold Floats.Float.add in H9.
unfold b64_plus in H9.
Print Bplus_correct.
Print is_finite.
pose (is_finite 53 1024 fx1).
unfold is_finite in b.
decompose [and] H0.
pose proof Bplus_correct.
Check Bplus.
Print Fcore_FLT.FLT_exp.
Locate emin.
Print Bplus.
Print Floats.Float.binop_pl.
Print Archi.default_pl_64.

Print nan_pl.
Print Z_of_nat'.
eapply H10 in H3.

Print B2R.
Print Bsign.
Print B2R.
instantiate (1:=fx1) in H3.
instantiate (2:=mode_NE) in H3.
instantiate (3:=eq_refl) in H3.
instantiate (4:=eq_refl) in H3.
instantiate (1:=Floats.Float.binop_pl) in H3.  decompose [and] H0. 
remember (Rlt_bool (Rabs (round radix2 (Fcore_FLT.FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (B2R 53 1024 fx1 + B2R 53 1024 fx2)))  (bpow radix2 1024)) as rltBoolInfo.  destruct rltBoolInfo.
decompose [and] H3. 
revert H18. intros H18.
inversion H9. unfold valToR.
Lemma three : forall x1 x2 x3,x1 <=x2 <= x3 -> x1 <= x2 /\ x2 <= x3. 
intros.
intuition.
Qed.
split.
Transparent Floats.Float.binop_pl. 
Check eq_trans.
pose  (Bplus 53 1024 eq_refl eq_refl Floats.Float.binop_pl mode_NE fx1 fx2) as samp.
 Transparent Bplus.
Transparent B2R.
rewrite H18 at 1.
Require Import compcert.flocq.Prop.Fprop_relative.
Print relative_error.

pose proof relative_error as Rel_Err.

Print round.
Print Valid_exp.
Check Rel_Err.
Print round.
pose (FLT_exp (3 - 1024 - 53) 53) as round_fexp.
pose round_fexp as round_fexpCopy.
specialize (Rel_Err radix2 round_fexp).

Check Valid_exp.
Print Valid_exp.
Lemma validFexpProof : Valid_exp  (FLT_exp (3 - 1024 - 53) 53).
unfold Valid_exp;
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

revert H.
intros H.
specialize (Rel_Err validFexpProof).

Print round.
Locate Valid_exp.
Print Valid_exp.
Definition precVal :=53%Z.
Print round.
Print FLT_exp.
Definition eminVal:= (3-1024-53)%Z. 
Print binary_float.
Check binary_float.
specialize (Rel_Err eminVal precVal).
Check round_fexp.
unfold round_fexp in Rel_Err.
unfold eminVal in Rel_Err.
unfold precVal in Rel_Err.

Lemma precThm: (forall k : Z, (eminVal < k)%Z -> (precVal <= k - FLT_exp (eminVal) precVal k)%Z).
intros.
unfold eminVal in *. unfold precVal in *. unfold FLT_exp. 
unfold Z.max.
Search (Z->Z -> {_}+{_}).
pose proof Z_lt_ge_dec ((k - 53)%Z) ((3 - 1024 - 53)%Z).
pose (k - 53 ?= 3 - 1024 - 53)%Z.
Print Datatypes.Eq.
Search (_ -> Datatypes.comparison).
Print Cge.

destruct H0. simpl in *. 

Search (_->Datatypes.Eq).
Search (_->Datatypes.comparison).
admit. admit
Qed.
Check precThm.

revert H24. intros H24.
specialize (Rel_Err precThm).
specialize (Rel_Err (round_mode mode_NE)).

Definition choiceDef := (fun x => negb (Zeven x)).
specialize (Rel_Err (valid_rnd_N choiceDef)).
Print Bplus_correct.
simpl in H6.
simpl in H11. 
simpl in H5.
simpl in H12.
Lemma combine: forall x1 x2, x1 <= x2 -> x2 <= x1 -> x1 = x2.
intros. psatz R.
Qed.
revert H. intros H.
apply combine in H6.
rewrite H6.
rewrite H6 in H.
apply combine in H5.
rewrite H5.
rewrite H5 in H.
specialize (Rel_Err (B2R 53 1024 f + B2R 53 1024 f0)).
pose (bpow radix2 (3 - 1024 - 53) <= Rabs (B2R 53 1024 f + B2R 53 1024 f0)) as noOverflow.
Lemma noOverflowProof: forall f f0, bpow radix2 (3 - 1024 - 53) <= Rabs (B2R 53 1024 f + B2R 53 1024 f0).  
intros.  admit. Qed.
pose proof noOverflowProof as noOverflowProof.
specialize (noOverflowProof f f0).
specialize (Rel_Err noOverflowProof).
revert Rel_Err. intros Rel_Err.
clear H0 H1 H8 H7 H9. clear H4 H6 H11 H5 H12 H10 H2 H3 H24 H18 H24 samp H23 H16 H22. clear H20 H19 H17 H14 H15. clear H13. clear HeqrltBoolInfo. clear b. Print Rabs.
unfold e in *.
remember (round radix2 (FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (B2R 53 1024 f + B2R 53 1024 f0)) as roundedValue.
remember ((B2R 53 1024 f + B2R 53 1024 f0)) as trueValue.
remember (bpow radix2 (- (53) + 1)) as error.
destruct (Rge_dec trueValue R0). 
intuition.
destruct (Rgt_dec (roundedValue - trueValue) R0).
unfold Rabs in *.
destruct Rcase_abs in Rel_Err.
psatz R.
destruct Rcase_abs in Rel_Err.
psatz R.
clear  round_fexp  round_fexpCopy H HeqtrueValue noOverflow noOverflow noOverflowProof HeqroundedValue Heqerror.
psatz R.
unfold Rabs in *.
destruct Rcase_abs in Rel_Err.
destruct Rcase_abs in Rel_Err.
psatz R.
psatz R.
destruct Rcase_abs in Rel_Err.
psatz R.
psatz R.
unfold Rabs in *.
destruct Rcase_abs in Rel_Err.
destruct Rcase_abs in Rel_Err.
psatz R.
psatz R.
psatz R.
intuition.
intuition.

admit.
simpl in HeqrltBoolInfo.
clear H15 H14 H17 H19 H16 H20 H3. clear H1 H2 H8 H7 H9 H1 H8 H7 H9.
clear H4 H6 H11 H5 H12 H10. clear H0. clear b.

simpl in *.
Print Rabs.
Print Rcase_abs.
Print  is_finite.

simpl in Rel_Err.
simpl.

psatz R.
revert H6. revert H11.
eapply combine.
simpl in *.

Print  is_finite.

Lemma ValidRnd:  Valid_rnd (round_mode mode_NE).
Print Valid_rnd.
Locate Valid_rnd.
Check round_le.
Check Valid_rnd.
Print round_le.
Check (round_mode mode_NE).
Lemma Zrnd_leProof: forall x y : R, x <= y -> ((round_mode mode_NE) x <= (round_mode mode_NE) y)%Z.
intros.
unfold round_mode.
Check valid_rnd_N.
Print Znearest.

Print Build_Valid_rnd {Z}
unfold Valid_rnd in *.
apply three.
eapply three.
rewrite H18.
admit.
revert H2. intros H2.

unfold valToR.
revert H12. intros H12.
Print e.
rewrite H12. 
 simpl in *. 
subst.
clear tr H0 H. clear H3 H9. clear H11 H4 H10 H5 H2 H8.
clear b H7 H6. admit.(*not sure why intuition is not working here*)

rewrite <-Rlt_bool (Rabs (round radix2 (Fcore_FLT.FLT_exp (-1074) 53)ZnearestE (B2R 53 1024 fx2 + B2R 53 1024 fx1))) 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 in HeqrltBoolInfo.
rewrite H in HeqrltBoolInfo.
admit.
eapply H3 in H1.
apply H1 in Bplus_correct.
Check is_finite.
pose (is_finite fx1).
apply Bplus_correct in H8.
subst;simpl.
Print eval_expr.
destruct v1 eqn:v1Des.
destruct v2 eqn:v2Des.
admit. (*admitting the case when v1 and v2 are undefined*)
admit. (*admitting the case when v1 is undefined and v2 is int*)
admit. (*admitting the case when v1 is undefined and v2 is long*)
admit. (*admitting the case when v1 is undefined and v2 is float*)
Print Values.
admit. (*admitting the case when v1 is undefined and v2 is Vsingle*)
admit (* admitting the case when v1 is undefined and v2 is pointer*).
destruct v2 eqn:v2Des. 
admit (*admitting the case when v1 is int and v2 is undefined*).
admit.
admit.
admit.
admit.
admit.
destruct v2 eqn:v2Des. 
admit. 
admit.
admit.
admit.
admit.
admit.
destruct v2 eqn:v2Des.
admit.
admit.
admit.

(*solving the part when v1 is float and v2 is float*)

Print Values.
*

inversion H6.
{+
unfold c_float in H8.
unfold sem_add in H8.
unfold classify_add in H8.
unfold typeconv in H8.
unfold remove_attributes in H8.
unfold change_attributes in H8.
unfold sem_binarith in H8.
unfold sem_cast in H8.
unfold classify_cast in H8.
unfold binarith_type in H8.
unfold classify_binarith in H8.
Print Floats.Float.add.
Print b64_plus.
Transparent Floats.Float.add.
Locate Floats.Float.add.
unfold Floats.Float.add in *.

unfold a in H8.

+ unfold typeof in H8.
}

Print eval_expr.
inversion H6.
unfold c_float in H8.
unfold sem_add in H8.
unfold classify_add in H8.
unfold typeconv in H8.
unfold remove_attributes in H8.
unfold change_attributes in H8.
unfold sem_binarith in H8.
unfold sem_cast in H8.
unfold classify_cast in H8.
unfold binarith_type in H8.
unfold classify_binarith in H8.
Print sem_add.
Print classify_add.
Print c_float.
Print typeconv.
unfold sem_add in H8.
+ unfold typeof in H8.

Print eval_expr. 
+ Print eval_expr. 

Print eval_expr.
Print sem_binary_operation.
- destruct expr1.
destruct expr2. 

Print eval_expr.
Print Values.val.
 intros.
Check eval_Ebinop.
vm_compute in H0.
Print Ebinop.

(*need to write a function that takes the inductive definition of an expression and converts it to an computable one*)
Print eval_expr.
Print Econst_float.
Eval compute in typeof (Econst_float fx2
               (Tfloat F64 {| attr_volatile := false; attr_alignas := None |})).

Check eval_Ebinop.
Check  sem_binary_operation .
Check Econst_float.
Check Floats.float.
Print Floats.float.
Print binary64.
Print binary_float.


Print Floats.Float.add.

Print binary64.
Print binary_float.
Check B754_finite.
Lemma stupid : bounded 53 1024 5 2 = true. 
admit. 
Qed.
Print Floats.Float.add.
Eval compute in (Floats.Float.add (B754_finite 53 1024 true 5 2 stupid) (B754_finite 53 1024 true 5 2 stupid)).
Print Floats.Float.add.
Print b64_plus.
Check  Floats.Float.binop_pl.
Eval typeof Econst_float 
Eval compute in  sem_binary_operation Oadd 
Check Econst_float.
Check 
Check Ebinop.

 eval_Ebinop in H0.
Local Close Scope HP_scope.
Local Open Scope SrcLang_scope.
Eval compute in evalState (nowTerm_to_clight (FloatN fx1 + FloatN fx2)).
unfold nowTerm_to_clight in H0.
unfold evalState in H0.

unfold runState in H0.
eapply eval_Ebinop in H0.
unfold eval_expr in H0.
Check zero_deriv_term.
Check bound.

Definition bound_state s1 s2 : forall ge e te mem expr val, (eval_expr ge e te mem (clightExpr expr) val) -> (eval_term (fst (bound_term expr) s1 s2) <= val <= eval_term (snd (bound_term expr) s1 s2)).





Definition bound_st forall f expr, (fst (bound_term expr)) 
Lemma bound_proof : forall s1 s2, s1 <= eval_term( fst )
