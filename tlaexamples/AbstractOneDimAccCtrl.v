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
 
  Parameter ubV : Term.
  Parameter ubv : Term.
  Parameter ubH : Term.
  Parameter amax : R.
  Parameter Hamax : (amax > 0)%R.
 
  Parameter ubH_st : is_st_term ubH = true.
  Parameter ubV_st : is_st_term ubV = true.
  Parameter ubv_st : is_st_term ubv = true.

  Parameter ubH_unch : forall t1 t2,
    |- Unchanged (["a", "H", "V", "T"])
       -->
       (subst_term_term 
          (subst_term_term (next_term ubH)
                           (next_term t1) "h" true)
          (next_term t2) "v" true) =
       (subst_term_term 
          (subst_term_term ubH t1 "h" false)
          t2 "v" false).

  Parameter ubV_unch : forall t1 t2,
    |- Unchanged (["a", "H", "V", "T"])
       -->
       (subst_term_term 
          (subst_term_term (next_term ubV)
                           (next_term t1) "h" true)
          (next_term t2) "v" true) =
       (subst_term_term 
          (subst_term_term ubV t1 "h" false)
          t2 "v" false).

  Parameter ubv_unch : forall t1 t2,
    |- Unchanged (["a", "H", "V", "T"])
       -->
       (subst_term_term 
          (subst_term_term (next_term ubv)
                           (next_term t1) "h" true)
          (next_term t2) "v" true) =
       (subst_term_term 
          (subst_term_term ubv t1 "h" false)
          t2 "v" false).
                 
End CtrlParameters.

Module AbstractAccDimCtrl (Import Params : CtrlParameters).

  Definition amaxinv : R := (/amax)%R.
 
  Definition sdist (v:Term) : Term :=
    v^^2*(/2)%R*amaxinv.

  Definition Ctrlable : Formula :=
    --amax <= "a" /\
    (0 <= "v" --> "h" + (sdist "v") <= ub) /\
    ("v" < 0 --> "h" <= ub) /\
    "h" - "H" <= ubH /\
    "v" - "V" <= ubV /\
    "v" <= ubv.
  
  Module InvParams <: InvParameters.
    Definition d := d.
    Definition Hd := Hd.
    Definition Inv := Ctrlable.

    Lemma HInv_st : is_st_formula Inv.
    Proof.
      pose proof ubH_st.
      pose proof ubV_st.
      pose proof ubv_st.
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
             end; solve_linear;
      match goal with
        |- context [subst_term_term
                      (subst_term_term _ ?t _ _)
                      ?t' _ _] =>
          rewrite ubH_unch
          with (t1:=unnext_term t) (t2:=unnext_term t') ||
          rewrite ubV_unch
          with (t1:=unnext_term t) (t2:=unnext_term t') ||
          rewrite ubv_unch
          with (t1:=unnext_term t) (t2:=unnext_term t')
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
    pose proof Hamax.
    solve_linear.
    generalize dependent (hd tr "t" - hd tr "T")%R.
    intros. unfold amaxinv in *.
    destruct (Rle_dec R0 (hd tr "v"))%R;
      solve_linear.
    eapply Rle_trans; eauto.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat_l.
    apply Rmult_0_le; solve_linear.
    apply Rmult_0_le; solve_linear.
    apply pow_0_le.
  Qed.

  Lemma safety :
    |- (AbstractCtrl.Init /\ []AbstractCtrl.Next) --> []Safe.
  Proof.
    apply imp_trans with (F2:=[]Ctrlable).
    - apply AbstractCtrl.safety.
    - apply always_imp. apply inv_safe.
  Qed.

End AbstractAccDimCtrl.