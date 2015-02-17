Require Import Compile2.

(* This file contains code enabling extraction and pretty-printing
   of Clight code. This code began its life in Compile2.v, but is
   factored out so that Compile2.v can be compiled/run without
   side effects (i.e., the extraction) *)

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
Definition prepare_pretty_print (pr : progr) (ws : wrapspec) : (program * list (positive * list nat)) :=
  let (prog, vars) := runState (progr_to_clight' pr ws) init_state in
  (prog, convert_var_list vars).

(* example code for doing the actual extraction. *)

Definition pp_derp := prepare_pretty_print derp height_wrapspec.
Definition ex_derp_prog := fst pp_derp.
Definition ex_derp_vars := snd pp_derp.
Eval compute in ex_derp_vars.
Definition coqmap := map.
(* Package everything upto extract it all at once *)
Definition extract_derp := (ex_derp_prog, ex_derp_vars, coqmap).
Extraction "derp.ml" extract_derp.
