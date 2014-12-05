Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Ctypes.
Require Import TLA.Syntax.
Require Import TLA.Lib.
Require Import TLA.Tactics.
Require Import String.
Require Import List.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.EitherMonad.

Local Open Scope string_scope.

(* First attempt at compilation; look at Compile2 for my most recent work *)

(* Formula, sans the things we don't need to worry about
   compiling, and without and and or *)
Inductive FlatFormula :=
| FTRUE : FlatFormula
| FFALSE : FlatFormula
| FComp : Term -> Term -> CompOp -> FlatFormula.

(* Convert a formula to a flat one *)
Definition flatten_formula (tla : Formula) : option FlatFormula :=
  match tla with
    | TRUE => Some FTRUE
    | FALSE => Some FFALSE
    | Comp a b c => Some (FComp a b c)
    | _ => None
  end.

(* Captures the structure we want each term in our IR to have
   Basically, a list of simultaneous assignments, and a
   list of conditions guarding (all of) those assigments.
   Our program will be a list of these statements. *)
Record ir_stmt : Set :=
  mk_ir_st {
      assns : list (Term * Term);
      conds : list FlatFormula
    }.
                            
Local Open Scope HP.

(* Convert to disjunctive normal form. Note that this
   cannot handle implication correctly. *)
Fixpoint DNF (tla : Formula) : Formula :=
  match tla with
    | And f1 f2 =>
      let df1 := (DNF f1) in
      let df2 := (DNF f2) in
      match (df1, df2) with
        | ((Or f11 f12), (Or f21 f22)) =>
          Or (Or (And f11 f21) (And f11 f22))
             (Or (And f12 f21) (And f12 f22))
        | ((Or f11 f12), _) =>
          Or (And f11 df2) (And f12 df2)
        | (_, (Or f21 f22)) =>
          Or (And df1 f21) (And df1 f22)
        | _ => And df1 df2
      end
    | Or f1 f2 =>
      Or (DNF f1) (DNF f2)
    | _ => tla
  end.

Fixpoint no_nexts (tlat : Term) : bool :=
  match tlat with
    | VarNowT _ => true
    | VarNextT _ => false
    | NatT _ => true
    | RealT _ => true
    | PlusT a b => andb (no_nexts a) (no_nexts b)
    | MinusT a b => andb (no_nexts a) (no_nexts b)
    | MultT a b => andb (no_nexts a) (no_nexts b)
  end.

Definition is_assn (tla : Formula) : bool :=
  match tla with
    | (Comp (VarNextT upd) rhs Eq) => no_nexts rhs
    | _ => false
  end.

Fixpoint is_cond (tla : Formula) : bool :=
  match tla with
    | TRUE => true
    | FALSE => true
    | Comp t1 t2 op =>
      andb (no_nexts t1) (no_nexts t2)
    | And f1 f2 => andb (is_cond f1) (is_cond f2)
    | Or f1 f2 => andb (is_cond f1) (is_cond f2)
    | Imp f1 f2 => andb (is_cond f1) (is_cond f2)
    (* we can't handle the remaining cases *)
    | PropF _ => false
    | Syntax.Exists _ _ => false
    | Always _ => false
    | Eventually _ => false
  end.

(* Input to this function should be one item in the DNF representation
   (that is, one conjunction with several conjuncts that don't have inner ORs)*)
Fixpoint listify_ands (tla : Formula) : list FlatFormula :=
  match tla with
    | And f1 f2 =>
      List.app (listify_ands f1) (listify_ands f2)
    | _ =>
      match flatten_formula tla with
        | Some ff => [ff]
        | None => nil
      end
  end.

Print Formula.

(* Convert to lists of single terms representing dnf *)
Fixpoint dnf2listoflists (tla : Formula) : list (list FlatFormula) :=
  match tla with
    | Or f1 f2 =>
      List.app (dnf2listoflists f1) (dnf2listoflists f2)
      (* as soon as we hit the first and, stop looking for ors *)
    | And f1 f2 =>
      [listify_ands tla]
    | _ => match flatten_formula tla with
             | Some ff => [[ff]]
             | None => nil
           end
                
  end.

(* Helper for tla2ir, helps us reorganize our list so we can easily partition it
   into conditions and assignments. Yes, I know this could have been done using a fold. *)
Print TLA.Syntax.Term.
Fixpoint split_conjs' (src lacc racc : list FlatFormula) : (list FlatFormula *  list FlatFormula) :=
  match src with
    | h :: src' =>
      (* if H is an assignment into a NEXT state, put it with assignments *)
      match h with
        | (FComp (VarNextT _) _ Eq) => split_conjs' src' (h :: lacc) racc
        | _ => split_conjs' src' lacc (h :: racc)
      end
    | nil => (lacc, racc)
  end.

Definition split_conjs forms := split_conjs' forms nil nil.

(* Put assignments into pair form *)
Fixpoint convert_assns_pairs (ffs : list FlatFormula) : list (Term * Term) :=
  match ffs with
    | f1 :: ffs' =>
      match f1 with
        | FComp lhs rhs Eq => (lhs, rhs) :: convert_assns_pairs ffs'
        | _ => convert_assns_pairs ffs'
      end
    | nil => nil
  end.

(* Perform conversion *) Print ir_stmt.
Definition tla2ir (tla : Formula) : list ir_stmt :=
  let dnf := DNF tla in
  let listrep := dnf2listoflists dnf in
  let splitted := map split_conjs listrep in
  let to_ir_st (f : list FlatFormula * list FlatFormula) :=
      let (assns, conds) := f in
      let assns' := convert_assns_pairs assns in
      (mk_ir_st assns' conds)
  in
  map to_ir_st splitted.

Print TLA.Syntax.Term.

(*
 * code for converting to clight
 *)

Print FlatFormula.
Print CompOp.
Print Syntax.Term.

(* ok so we need some kind of conversion from the string variable IDs used by this project
 * to the integer ids used by compcert *)

Print AST.ident.
Print Var.

(* Converts an individual term to equivalent Clight representation *)
Fixpoint convert_term (t : Term) : option expr :=
  match t with
    | 
  end.

(* Convert IR to an if statement *)
Fixpoint ir2clight_stmt (ir : ir_stmt) : statement :=
  (* if conditions met: run assignments, then publish *)
  let convert_condition (cond : FlatFormula) : expr :=
      match cond with
        | FFALSE => Econst_int (Int.repr 0) (Tint IBool Unsigned noattr)
        | FTRUE  => Econst_int (Int.repr 1) (Tint IBool Unsigned noattr)
        | FComp l r op =>
          match op with
            | Gt =>
            | Ge =>
            | Lt =>
            | Le =>
            | Eq =>
          end
      end
  in
  let convert_assignment (assn : Term * Term) : statement :=
  in
  match ir with
    | mk_ir_st assns conds =>
      (* need to map-reduce *)
      (* need to append assignment *)
      let conds' := convert_conditions conds in
      let assns' := convert_assignments assns in
      Sifthenelse conds' assns' Sskip
  end

Definition ir2clight (ir : list ir_stmt) : statement :=
  let mapped := map ir2clight_stmt ir in
  match mapped with
    | nil => Sskip
    | s :: nil => s
    | s1 :: mapped' => fold_right Sseq s1 mapped'
  end.

(* if-statement normal form: (cond /\ statement) \/ (cond2 /\ statement *)
