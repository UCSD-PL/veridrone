Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Import LibNotations.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import TLA.ArithFacts.
Require Import TLA.Substitution.
Require Import Modules.AbstractIndAccCtrl.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

Module Type CtrlParameters.

  Parameter ub : R.
  Parameter d : R.
  Parameter Hd : (d > 0)%R.

  Parameter amax : R.
  Parameter Hamax : (amax > 0)%R.

  Parameter amin : R.
  Parameter Hamin : (amin < 0)%R.
                 
End CtrlParameters.

Module AbstractAccDimCtrl2 (Import Params : CtrlParameters).

  Definition amininv : R := (/amin)%R.
 
  Definition sdist (v:Term) : Term :=
    v^^2*(/2)%R*(--amininv).

  Definition Ctrlable : Formula :=
    "a" <= amax /\
    (0 <= "v" --> "h" + (sdist "v") <= ub) /\
    ("v" < 0 --> "h" <= ub) /\
    "h" - "H" <= tdist "V" amax d /\
    "v" - "V" <= amax*d.

(*
(* Attempt at a more sophisticated invariant. *)
    amin <= "a" /\
    (0 <= "v" --> "h" + (sdist "v") <= ub) /\
    ("v" < 0 --> "h" <= ub) /\
    (* Always moves up *)
    (("V" >= 0 /\ "a" >= 0)
     --> "h" - "H" <= tdist "V" "a" d) /\
    (* Always moves down *)
    (("V" < 0 /\ "a" < 0)
     --> "h" - "H" <= 0) /\
    (* Moves up for next d time *)
    (("V" >= 0 /\ "a" < 0 /\ --"a"*d < "V")
     --> "h" - "H" <= tdist "V" "a" d) /\
    (* Peaks in middle *)
    (("V" >= 0 /\ "a" < 0 /\ --"a"*d >= "V")
     (* We don't have division, so we need "a"
        on the left. *)
     --> "a"*("h" - "H") <= --"V"^^2*(/2)%R) /\
    (* Moves down then turns around and ends
       heigher than at the beginning *)
    (("V" < 0 /\ "a" >= 0 /\ tdist "V" "a" d >= 0)
     --> "h" - "H" <= tdist "V" "a" d) /\
    (* Moves down, maybe turns around, but ends
       lower than at the beginning *)
    (("V" < 0 /\ "a" >= 0 /\ tdist "V" "a" d < 0)
     --> "h" - "H" <= 0) /\
    ("a" > 0 --> "v" - "V" <= "a"*d) /\
    ("a" <= 0 --> "v" - "V" <= 0).*)
  
  Module InvParams <: InvParameters.
    Definition d := d.
    Definition Hd := Hd.
    Definition Inv := Ctrlable.

    Lemma HInv_st : is_st_formula Inv.
    Proof.
      simpl. intuition.
    Qed.

    Lemma HInv_unch : forall (t:R),
      |- (Inv["H" + (tdist "V" "a" t)//"h"]
             ["V" + "a"*t//"v"] /\
        Unchanged (["a", "H", "V", "T"]))
       --> (next Inv)
             [next_term ("H" + (tdist "V" "a" t))/!"h"]
             [next_term ("V" + "a"*t)/!"v"].
    Proof.
      solve_linear;
      repeat match goal with
               | [ H : _ |- _ ] =>
                 match type of H with
                   | @eq R _ _ => idtac
                   | _ => revert H
                 end
             end;
      repeat match goal with
               | [ H : @eq R _ _ |- _ ] =>
                 rewrite H
             end; solve_linear.
    Qed.

  End InvParams.

  Module AbstractCtrl := AbstractIndAccCtrl(InvParams).

  Definition Safe : Formula :=
    "h" <= ub.

  Ltac rewrite_h_v :=
    match goal with
      | [ H : eq (Rminus (hd ?tr "h") (hd ?tr "H")) ?e |- _ ]
          => assert (eq (hd tr "h") (hd tr "H" + e))%R as Heq
                    by solve_linear; rewrite Heq in *;
             clear Heq H
    end;
    match goal with
      | [ H : eq (Rminus (hd ?tr "v") (hd ?tr "V")) ?e |- _ ]
          => assert (eq (hd tr "v") (hd tr "V" + e))%R as Heq
                    by solve_linear; rewrite Heq in *;
             clear Heq H
    end.

  Lemma inv_safe : |- Ctrlable --> Safe.
  Proof.
    pose proof Hd.
    pose proof Hamin.
    solve_linear.
    generalize dependent (hd tr "t" - hd tr "T")%R.
    intros. unfold amininv in *.
    destruct (Rle_dec R0 (hd tr "v"))%R;
      solve_linear.
    eapply Rle_trans; eauto.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat_l.
    apply Rmult_0_le; solve_linear.
    apply Rmult_0_le; solve_linear.
    apply pow_0_le.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat_l.
    solve_linear.
  Qed.

  Lemma safety :
    |- (AbstractCtrl.Init /\ []AbstractCtrl.Next) --> []Safe.
  Proof.
    apply imp_trans with (F2:=[]Ctrlable).
    - apply AbstractCtrl.safety.
    - apply always_imp. apply inv_safe.
  Qed.

End AbstractAccDimCtrl2.