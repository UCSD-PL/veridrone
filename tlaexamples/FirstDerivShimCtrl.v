Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import TLA.Inductively.
Require Import Examples.System2.

Local Open Scope HP_scope.
Local Open Scope string_scope.

Module Type FirstDerivShimParams.
  (* Upper bound on velocity. *)
  Parameter ub : R.
  (* Max time between executions of the
     controller. *)
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
End FirstDerivShimParams.



Module FirstDerivShim (P : FirstDerivShimParams).

  Import P.

  (* The continuous dynamics of the system *)
  Definition w : Evolution :=
    fun st' => st' "v" = "a" //\\ st' "a" = 0.

  Definition SafeAcc (a v:Term) : Formula :=
    a*d + v <= ub.

  Definition Default (a:Term) : Formula :=
    a <= 0.

  Definition Ctrl : ActionFormula :=
    SafeAcc "a"! "v" \\// Default "a"!.


  Definition Next : ActionFormula :=
    Sys (Ctrl //\\ Unchanged ("v"::nil)) w d.

  Definition IndInv : Formula :=
         ("a" <  0 -->> "v" <= ub)
    //\\ ("a" >= 0 -->> "a"*"T" + "v" <= ub).

  Theorem IndInv_impl_Inv : IndInv //\\ 0 <= "T" <= d |-- "v" <= ub.
  Proof. solve_nonlinear. Qed.

  Theorem SysNeverStuck_Next
  : |-- SysNeverStuck d IndInv Next.
  Proof.
    eapply SysNeverStuck_Sys'; [ refine _ | pose proof d_gt_0 ; solve_linear | | ].
    { enable_ex_st.
      pose proof d_gt_0.
      do 2 eexists; exists d; solve_linear. }
    { admit. (** Provable, but we won't worry about it *) }
  Qed.

  Theorem TimedPreserves_Next
  : |-- TimedPreserves d IndInv Next.
  Proof.
    eapply Preserves_Sys.
    { refine _. }
    { charge_split; fold next.
      - eapply diff_ind with (Hyps:=ltrue).
        + tlaIntuition.
        + tlaIntuition.
        + unfold World. tlaAssume.
        + tlaIntuition.
        + tlaAssume.
        + tlaIntuition.
        + charge_tauto.
        + simpl deriv_formula. restoreAbstraction.
          charge_intros.
          unfold lift2, mkEvolution, w.
          repeat charge_split; charge_intros;
          try solve [ solve_linear
                    | eapply zero_deriv with (x:="a");
                      [ charge_tauto | tlaIntuition |
                        solve_linear ] ].
          solve_nonlinear.
      - solve_linear. }
    { solve_nonlinear. }
  Qed.

  (* Our main safety theorem. *)
  Theorem Spec_safe :
    |-- (IndInv //\\ 0 <= "T" <= d) //\\ []Next -->> []"v" <= ub.
  Proof.
    rewrite Preserves_Inv.
    { rewrite IndInv_impl_Inv.
      charge_tauto. }
    { compute; tauto. }
    { apply TimedPreserves_Next. }
  Qed.

  (* Some useful renaming lemmas *)
  Lemma Rename_SafeAcc :
    forall a v m,
      (forall x : Var, is_st_term (m x) = true) ->
      Rename m (SafeAcc a v) -|-
      SafeAcc (rename_term m a) (rename_term m v).
  Proof.
    intros; split; breakAbstraction; intros;
    destruct tr as [? [? ?]]; simpl in *.
    { repeat rewrite Rename_term_ok; auto. }
    { repeat rewrite <- Rename_term_ok; auto. }
  Qed.

  Lemma Rename_Default :
    forall a m,
      (forall x : Var, is_st_term (m x) = true) ->
      Rename m (Default a) -|- Default (rename_term m a).
  Proof.
    intros; split; breakAbstraction; intros;
    destruct tr as [? [? ?]]; simpl in *.
    { repeat rewrite Rename_term_ok; auto. }
    { repeat rewrite <- Rename_term_ok; auto. }
  Qed.

End FirstDerivShim.
