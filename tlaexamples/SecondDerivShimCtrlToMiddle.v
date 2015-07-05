Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Import TLA.TLA.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import TLA.BasicProofRules.
Require Import TLA.ArithFacts.
Require Import Examples.System.
Require Import Examples.SecondDerivUtil.

Open Scope HP_scope.
Open Scope string_scope.

Module Type SecondDerivShimParams <: SdistParams.

  (* The upper bound on y. *)
  Parameter ub : R.
  (* Max time between executions of the
     controller. *)
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
  (* Our breaking acceleration. *)
  Parameter amin : R.
  Parameter amin_lt_0 : (amin < 0)%R.

  Parameter ubv : R.

End SecondDerivShimParams.

Module SecondDerivShimCtrl (Import Params : SecondDerivShimParams).

  Module SdistUtil := SdistUtil(Params).
  Import SdistUtil.

  (* The continuous dynamics of the system *)
  Definition w : state->Formula :=
    fun st' =>
      st' "y" = "v" //\\ st' "v" = "a" //\\
      AllConstant ("a"::"Y"::"V"::"T"::nil)%list st'.

  Definition SafeAcc (a:Term) : Formula :=
    Max a 0
        (fun mxa =>
           "y" + tdist "v" mxa d + sdist ("v" + mxa*d)
           <= ub).

  Definition Default : Formula :=
    "y" > 0 -->> (("v" > 0 -->> "a"! <= amin) //\\
                  ("v" <= 0 -->> "a"! <= 0)).

  Definition Ctrl : Formula :=
    SafeAcc "a"! \\// Default.

  Definition History : Formula :=
    "Y"! = "y" //\\ "V"! = "v" //\\ "T"! = "t"!.

  Definition Safe : Formula :=
    "y" <= ub.

  Definition tdiff : Term :=
    "T" - "t".

  Definition I : Formula :=
    Syntax.Forall R
           (fun t =>
              0 <= t <= d -->>
              (0 <= "v" + "a"*t  -->>
               "y" + tdist "v" "a" t +
               sdist ("v" + "a"*t) <= ub) //\\
              ("v" + "a"*t < 0 -->>
               "y" + tdist "v" "a" t <= ub)) //\\
    "T" = "t" //\\ "Y" = "y" //\\ "V" = "v" //\\
    0 <= "t" <= d.

  Definition SpecR : SysRec :=
    {| Init := I;
       Prog := Ctrl //\\ History //\\
               Unchanged ("v"::"y"::nil)%list;
       world := w;
       unch := (("a":Term)::("Y":Term)::("V":Term)::
                ("T":Term)::("v":Term)::("y":Term)::nil)%list;
       maxTime := d |}.

  Definition ProgRefined : Formula :=
    Default //\\ History //\\ Unchanged ("v"::"y"::nil)%list.

  Lemma ProgRefined_ok :
    ProgRefined |-- SpecR.(Prog).
  Proof.
    unfold ProgRefined. unfold SpecR, Ctrl.
    simpl. restoreAbstraction. charge_tauto.
  Qed.

  Definition Spec := PartialSysD SpecR.

  Definition IndInv : Formula :=
    "y" - "Y" <= tdist "V" "a" tdiff //\\
    "v" - "V" = "a"*tdiff //\\
    Syntax.Forall R
           (fun t => "V" + "a"*t <= ubv -->>
              ((0 <= t <= d //\\ 0 <= "V" + "a"*t) -->>
                    "Y" + (tdist "V" "a" t) +
                    (sdist ("V" + "a"*t)) <= ub) //\\
              ((0 <= t <= d //\\ "V" + "a"*t < 0) -->>
                     "Y" + (tdist "V" "a" t) <= ub)) //\\
   "t" <= "T" <= d.

  Lemma ind_inv_init :
    I |-- IndInv.
  Proof.
    breakAbstraction; simpl; unfold eval_comp;
    simpl; intros. destruct H.
    decompose [and] H0. clear H0.
    rewrite H1 in *; clear H1;
    rewrite H2 in *; clear H2;
    rewrite H3 in *; clear H3.
    solve_linear; specialize (H x);
    solve_linear.
  Qed.

  (* A proof that the inductive safety condition
     Inv implies the safety contition
     we actually care about, Safe. *)
  Lemma inv_safe :
    "v" <= ubv //\\ IndInv //\\ TimeBound d |-- Safe.
  Proof.
    pose proof amin_lt_0.
    pose proof d_gt_0.
    tlaAssert (0 <= tdiff <= d);
    [ solve_linear | tlaIntro ].
    tlaAssert ("V" + "a"*tdiff <= ubv \\//
               "V" + "a"*tdiff > ubv);
    [ solve_linear | tlaIntro ].
    decompose_hyps.
    { breakAbstraction; simpl; unfold eval_comp; simpl; intros.
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           end.
    specialize (H9 ((Stream.hd tr) "T" - (Stream.hd tr) "t"))%R.
    destruct (Rle_dec R0
                      ((Stream.hd tr) "V"+
                       (Stream.hd tr) "a"*
                       ((Stream.hd tr) "T" - (Stream.hd tr) "t"))%R);
      intuition.
    - eapply Rle_trans; eauto.
      rewrite <- Rplus_0_r with (r:=(Stream.hd tr) "y").
      apply Rplus_le_compat.
      + solve_linear.
      + rewrite Rmult_assoc.
        apply Rmult_0_le; solve_linear.
        apply pow_0_le.
        assert (/ amin < 0)%R by solve_linear.
        solve_linear.
    - assert
        (((Stream.hd tr) "V" +
          (Stream.hd tr) "a" *
          ((Stream.hd tr) "T" - (Stream.hd tr) "t") < 0)%R)
        by solve_linear.
      eapply Rle_trans; eauto.
      solve_linear. }
    { solve_linear. }
  Qed.

  Lemma SysSafe_ctrl : forall P, P |-- SysSafe SpecR.
  Proof.
    pose proof amin_lt_0.
    intros.
    apply SysSafe_rule; apply always_tauto.
    enable_ex_st. repeat eexists; solve_linear.
  Qed.

  Lemma indInvPremise : forall v V a t T , (v <= ubv ->
                                            v - V = a * (T - t) -> 
                                            V + a * (T -t) <= ubv)%R.
  Proof.
    intros.
    solve_nonlinear.
  Qed.
  
  Lemma indInvPremise2 : forall t T, (t <= T -> T <= d -> 0 <= t -> 0 <= T - t <= d)%R.
  Proof.  
    intros. solve_linear.
  Qed.
  
  Lemma simplProof : forall x , ((x * (x * 1)) >= R0)%R.    
  Proof.
    intros.
    solve_nonlinear.
  Qed.
  
  Lemma simplProof3 : forall y Y s1 s2, (y - Y <= s1 -> Y + s1 + s2 <= ub -> s2 >= 0 -> y <=ub)%R.  
  Proof.
    intros.
    solve_linear.
  Qed.

  Lemma simplProof2 : forall x y, (x >= R0 -> y < R0 ->  x * (0 - / 2) * / y >= R0)%R. 
  Proof.
    intros.
    z3 solve_dbg.
  Admitted.

  Theorem ctrl_safe :
   []"v" <= ubv |-- Spec -->> []Safe.
  Proof.
    pose proof amin_lt_0 as amin_lt_0.
    pose proof d_gt_0 as d_gt_0.
    tlaIntro.
    eapply PartialSys_by_induction
    with (IndInv:=IndInv) (A:="v" <= ubv).
    - tlaIntuition.
    - unfold Spec, SpecR. tlaAssume.
    - tlaIntuition.
    - charge_apply ind_inv_init. charge_tauto.
    - tlaIntuition.
    - charge_apply inv_safe. charge_tauto.
    - unfold InvariantUnder, IndInv, Max. simpl.
      restoreAbstraction. unfold tdist, sdist.
      solve_linear; rewrite_next_st; solve_linear;
      specialize (H3 x); solve_linear.
    - simpl BasicProofRules.next. restoreAbstraction.
      repeat charge_split;
      try (apply lforallR; intro).
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:="v" - "V" <= "a"*tdiff)
                                 (G:=unnext GG)
        end; try solve [ tlaIntuition |
                         unfold World; tlaAssume |
                         solve_linear ].
        eapply diff_ind with (Hyps:=TRUE);
          try solve [ tlaIntuition |
                         unfold World; tlaAssume |
                         solve_linear ]. solve_nonlinear.
        solve_nonlinear. }
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=TRUE)
                                 (G:=unnext GG)
        end; try solve [ tlaIntuition |
                         unfold World; tlaAssume |
                         solve_linear ]. solve_nonlinear. }
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=TRUE)
                                 (G:=unnext GG)
        end; try solve [ tlaIntuition |
                         unfold World; tlaAssume |
                         solve_linear ].
        - unfold IndInv;
          simpl; restoreAbstraction; unfold tdist, sdist;
          solve_linear; rewrite_next_st; solve_linear;
          specialize (H5 x); solve_linear.
        - simpl deriv_formula. restoreAbstraction.
          charge_intros; repeat charge_split;
          charge_intros; repeat charge_split.
          { eapply zero_deriv with (x:="a");
            [ charge_tauto | tlaIntuition | ].
            eapply zero_deriv with (x:="V");
              [ charge_tauto | tlaIntuition | ].
            solve_linear; rewrite_next_st;
            solve_linear. }
          { eapply zero_deriv with (x:="a");
            [ charge_tauto | tlaIntuition | ].
            eapply zero_deriv with (x:="V");
              [ charge_tauto | tlaIntuition | ].
            solve_linear; rewrite_next_st;
            solve_linear. }
          { charge_intros; repeat charge_split;
            charge_intros.
            { eapply zero_deriv with (x:="a");
              [ charge_tauto | tlaIntuition | ].
              eapply zero_deriv with (x:="V");
                [ charge_tauto | tlaIntuition | ].
              solve_linear; rewrite_next_st;
              solve_linear. }
            { eapply zero_deriv with (x:="a");
              [ charge_tauto | tlaIntuition | ].
              eapply zero_deriv with (x:="V");
                [ charge_tauto | tlaIntuition | ].
              solve_linear; rewrite_next_st;
              solve_linear. } }
          { solve_linear. rewrite H6. rewrite H8. rewrite H7.
            solve_linear. }
          { charge_intros; repeat charge_split;
            charge_intros.
            { eapply zero_deriv with (x:="a");
              [ charge_tauto | tlaIntuition | ].
              eapply zero_deriv with (x:="V");
                [ charge_tauto | tlaIntuition | ].
              solve_linear; rewrite_next_st;
              solve_linear. }
            { eapply zero_deriv with (x:="a");
              [ charge_tauto | tlaIntuition | ].
              eapply zero_deriv with (x:="V");
                [ charge_tauto | tlaIntuition | ].
              solve_linear; rewrite_next_st;
              solve_linear. } }
          { solve_linear. rewrite H6. rewrite H8. rewrite H7.
            solve_linear. } }
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=TRUE)
                                 (G:=unnext GG)
        end; try solve [ tlaIntuition |
                         unfold World; tlaAssume |
                         solve_linear ]. }
      { unfold World. eapply zero_deriv with (x:="T");
            [ charge_tauto | tlaIntuition | ].
        solve_linear. }
    - repeat charge_split.
      { solve_linear; rewrite_next_st; R_simplify; solve_linear. }
      { solve_linear; rewrite_next_st; R_simplify; solve_linear. }
      { fold BasicProofRules.next. unfold Discr, Ctrl, Max.
        decompose_hyps.
        { tlaAssert ("a"! <= 0 \\// "a"! >= 0);
          [ solve_linear | tlaIntro ].
          apply lforallR. intro x.
          simpl next. restoreAbstraction. charge_intros.
          charge_split; repeat decompose_hyps.
          - simpl. restoreAbstraction. charge_intros.
            tlaAssert (tdist "V"! "a"! x +
                       (sdist ("V"! + "a"!*x)) <=
                       tdist "v" 0 d + sdist ("v" + 0 * d)).
            + pose proof (tdist_sdist_incr "V"! "v" "a"! 0 x d).
              charge_apply H. solve_linear.
            +
              breakAbstraction.  intros. decompose [and] H. clear H.
              pose proof indInvPremise as indInvPremise.
              specialize (indInvPremise (Stream.hd tr "v") (Stream.hd tr "V") (Stream.hd tr "a") (Stream.hd tr "t") (Stream.hd tr "T") H4 H1).
              specialize (H8 (Stream.hd tr "T" - Stream.hd tr "t")%R indInvPremise).
              pose proof indInvPremise2 as indInvPremise2.
              specialize (indInvPremise2  (Stream.hd tr "t") (Stream.hd tr "T") H9 H11 H7).
              destruct (Rge_dec ( Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) R0).
              {
                apply Rge_le in r.
                (* proving  0 <= T-t <=d*)
                pose proof conj as conjIndInvPremise.
                specialize (conjIndInvPremise (0 <= Stream.hd tr "T" - Stream.hd tr "t" <= d)%R (0 <= Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t"))%R indInvPremise2 r).
                decompose [and] H8.
                specialize (H conjIndInvPremise). 
  
                pose proof simplProof as sProof.
                specialize (sProof  (Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t"))%R).
                pose proof simplProof2 as sProof2.
                specialize (sProof2  ((Stream.hd tr "V" +
                                       Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
                                      ((Stream.hd tr "V" +
                                        Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1))%R amin sProof amin_lt_0).
                pose proof simplProof3 as sProof3.
                specialize (sProof3 (Stream.hd tr "y") (Stream.hd tr "Y")  
                                    (Stream.hd tr "V" * (Stream.hd tr "T" - Stream.hd tr "t") +
                                     / 2 * Stream.hd tr "a" *
                                     ((Stream.hd tr "T" - Stream.hd tr "t") *
                                      ((Stream.hd tr "T" - Stream.hd tr "t") * 1)))%R
                                    ((Stream.hd tr "V" +
                                      Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
                                     ((Stream.hd tr "V" +
                                       Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
                                     (0 - / 2) * / amin)%R H6 H sProof2).
                clear sProof sProof2.
                
                specialize (H23 H5).
                revert H23. intros.
                
                rewrite <- H14 in H23, sProof3. rewrite <- H16 in H23.
                rewrite <- H16 in H0.
                clear -H2 H25 amin_lt_0 H5 sProof3 H23 H0. 
                z3 solve_dbg.
                admit.
              }
              {
                z3 solve_dbg.
                solve_nonlinear.
                admit.
              }
          - 
            breakAbstraction. intros. 
            decompose [and] H.  specialize (H20 H4). rewrite <- H13 in H20. rewrite <- H15 in H20.
            decompose [and] H0.
            clear -H4 H20 H25 H23 amin_lt_0.
            z3 solve_dbg.
            admit.
          -
            breakAbstraction.  intros. decompose [and] H. clear H. 
            pose proof indInvPremise as indInvPremise.
            specialize (indInvPremise (Stream.hd tr "v") (Stream.hd tr "V") (Stream.hd tr "a") (Stream.hd tr "t") (Stream.hd tr "T") H2 H3).
            specialize (H7 (Stream.hd tr "T" - Stream.hd tr "t")%R indInvPremise).
            
            pose proof indInvPremise2 as indInvPremise2.
            specialize (indInvPremise2  (Stream.hd tr "t") (Stream.hd tr "T") H8 H10 H6).

            destruct (Rge_dec ( Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) R0).
            {
              apply Rge_le in r.
              (* proving  0 <= T-t <=d*)
              pose proof conj as conjIndInvPremise.
              specialize (conjIndInvPremise (0 <= Stream.hd tr "T" - Stream.hd tr "t" <= d)%R (0 <= Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t"))%R indInvPremise2 r).
              decompose [and] H7.
              specialize (H conjIndInvPremise). 
              clear H16.
              pose proof simplProof as sProof.
              specialize (sProof  (Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t"))%R).
              pose proof simplProof2 as sProof2.
              specialize (sProof2  ((Stream.hd tr "V" +
                                     Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
                                    ((Stream.hd tr "V" +
                                      Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1))%R amin sProof amin_lt_0).
              pose proof simplProof3 as sProof3.
              specialize (sProof3 (Stream.hd tr "y") (Stream.hd tr "Y")  
                                  (Stream.hd tr "V" * (Stream.hd tr "T" - Stream.hd tr "t") +
                                   / 2 * Stream.hd tr "a" *
                                   ((Stream.hd tr "T" - Stream.hd tr "t") *
                                    ((Stream.hd tr "T" - Stream.hd tr "t") * 1)))%R
                                  ((Stream.hd tr "V" +
                                    Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
                                   ((Stream.hd tr "V" +
                                     Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
                                   (0 - / 2) * / amin)%R H5 H sProof2).
              clear sProof sProof2.
              specialize (H22 H4).
              rewrite <- H13 in H22, sProof3. rewrite <- H15 in H22.
              clear H8 H10 H6 H12 H11 H14 H9 H15 H13 H15. clear H19 H18 H17 H21 H20.
              clear H1. clear H4 H2. clear H5 H7 H3 H indInvPremise indInvPremise2 conjIndInvPremise r d_gt_0.
              clear -amin_lt_0 x tr H0 H22 sProof3.
              decompose [and] H0. clear H0.
              z3 solve_dbg.
              admit.
            }
            {

              apply Rnot_ge_lt in n.
              decompose [and] H7.
              pose proof conj as conjIndInvPremise.
              specialize (conjIndInvPremise (0 <= Stream.hd tr "T" - Stream.hd tr "t" <= d)%R (Stream.hd tr "V" +  Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t") < 0)%R indInvPremise2 n).
              specialize (H16 conjIndInvPremise).  
              rewrite <- H13 in H5. rewrite <- H15 in H3.
              clear -amin_lt_0 H0 H5 H3 H16 conjIndInvPremise.
              z3 solve_dbg.
              admit.
            }
          - 
            breakAbstraction. intros. decompose [and] H. clear H. 
            pose proof indInvPremise as indInvPremise.
            specialize (indInvPremise (Stream.hd tr "v") (Stream.hd tr "V") (Stream.hd tr "a") (Stream.hd tr "t") (Stream.hd tr "T") H2 H3).
            specialize (H7 (Stream.hd tr "T" - Stream.hd tr "t")%R indInvPremise).
            
            pose proof indInvPremise2 as indInvPremise2.
            specialize (indInvPremise2  (Stream.hd tr "t") (Stream.hd tr "T") H8 H10 H6).
            destruct (Rge_dec ( Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) R0).
            {
              clear -amin_lt_0 x tr H0 H4 H3 H15 r.  
              z3 solve_dbg.
              admit.
            }
            {
              apply Rnot_ge_lt in n.
              decompose [and] H7.
              pose proof conj as conjIndInvPremise.
              specialize (conjIndInvPremise (0 <= Stream.hd tr "T" - Stream.hd tr "t" <= d)%R (Stream.hd tr "V" +  Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t") < 0)%R indInvPremise2 n).
              specialize (H16 conjIndInvPremise).  
              rewrite <- H13 in H5. rewrite <- H15 in H3.
              clear -amin_lt_0 H0 H5 H3 H16 conjIndInvPremise.
              z3 solve_dbg.
              admit.
            }
        }
        {
          
          admit.
           (*
           breakAbstraction. intros. decompose [and] H. clear H.
           pose proof indInvPremise as indInvPremise.
           specialize (indInvPremise (Stream.hd tr "v") (Stream.hd tr "V") (Stream.hd tr "a") (Stream.hd tr "t") (Stream.hd tr "T") H1 H3).
           specialize (H5 (Stream.hd tr "T" - Stream.hd tr "t")%R indInvPremise).

           pose proof indInvPremise2 as indInvPremise2.
           specialize (indInvPremise2  (Stream.hd tr "t") (Stream.hd tr "T") H6 H8 H4).
           destruct (Rge_dec ( Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) R0).
           {
              apply Rge_le in r.
               (* proving  0 <= T-t <=d*)
               pose proof conj as conjIndInvPremise.
               specialize (conjIndInvPremise (0 <= Stream.hd tr "T" - Stream.hd tr "t" <= d)%R (0 <= Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t"))%R indInvPremise2 r).
               decompose [and] H5. clear H5.
               specialize (H conjIndInvPremise). 
               clear H18.
               pose proof simplProof as sProof.
               specialize (sProof  (Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t"))%R).
               pose proof simplProof2 as sProof2.
               specialize (sProof2  ((Stream.hd tr "V" +
                                      Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
                                     ((Stream.hd tr "V" +
                                       Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1))%R amin sProof amin_lt_0).
               pose proof simplProof3 as sProof3.
               specialize (sProof3 (Stream.hd tr "y") (Stream.hd tr "Y")  
                                   (Stream.hd tr "V" * (Stream.hd tr "T" - Stream.hd tr "t") +
                                    / 2 * Stream.hd tr "a" *
                                    ((Stream.hd tr "T" - Stream.hd tr "t") *
                                     ((Stream.hd tr "T" - Stream.hd tr "t") * 1)))%R
                                   ((Stream.hd tr "V" +
                                     Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
                                    ((Stream.hd tr "V" +
                                      Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
                                    (0 - / 2) * / amin)%R H2 H sProof2). 
               clear sProof sProof2.
               split.
               intros.
              *)
         }
       }
      {
        breakAbstraction.
        intros.
        decompose [and] H.
        clear -H16.
        solve_nonlinear.
      }
      {
        breakAbstraction.
        intros.
        decompose [and] H.
        clear -H12 H16.
        solve_nonlinear.
      }
  Qed.
  
 
Admitted.
(*
          - simpl. restoreAbstraction. charge_intros.
            tlaAssert ("v" >= 0 \\// "v" <= 0);
              [ solve_linear | tlaIntro ].
            decompose_hyps.
            + simpl. restoreAbstraction.
              tlaAssert (tdist "v" "a"! x <= tdist "v" 0 d).
              * pose proof (tdist_incr "v" "v" "a"! 0 x d).
                charge_apply H. solve_linear.
                rewrite_real_zeros.
                apply Rmult_0_le; solve_linear.
              * tlaIntro. solve_linear.
                eapply Rle_trans; eauto.
                repeat rewrite Rplus_assoc.
                apply Rplus_le_compat.
                { solve_linear. }
                { rewrite_next_st. eapply Rle_trans; eauto.
                  repeat rewrite <- Rplus_assoc. apply Rplus_le_r.
                  rewrite Rmult_assoc.
                  apply Rmult_0_le; solve_linear.
                  apply pow_0_le.
                  clear - amin_lt_0.
                  assert (/ amin < 0)%R by solve_linear.
                  solve_linear. }
            + tlaAssert ("y" <= ub).
              { rewrite <- inv_safe. charge_tauto. }
              { tlaAssert (tdist "v" "a"! x <= 0).
                - pose proof (tdist_vel_neg "v" "a"! x).
                  charge_apply H. solve_linear.
                - solve_linear. rewrite_next_st. solve_linear. }
          - tlaIntro. charge_split.
            + simpl; restoreAbstraction. tlaIntro.
              tlaAssert (tdist "V"! "a"! x +
                         (sdist ("V"! + "a"!*x)) <=
                         tdist "v" "a"! d +
                         sdist ("v" + "a"! * d)).
              *  pose proof (tdist_sdist_incr "V"! "v"
                                              "a"! "a"! x d).
                 charge_apply H. solve_linear.
              * solve_linear.
            + tlaAssert ("y" <= ub).
              * rewrite <- inv_safe. charge_tauto.
              * simpl; restoreAbstraction. tlaIntro.
                reason_action_tac. intuition.
                repeat match goal with
                       | [ H : eq (post _) _ |- _ ]
                         => try rewrite H in *; clear H
                       end.
                assert (pre "v" <= 0)%R;
                  [ solve_nonlinear | intros ].
                clear - H2 H3 H4 H1 H5. solve_nonlinear. }
          - unfold IndInv. unfold History.
            tlaIntro. charge_split; simpl; restoreAbstraction.
            + charge_intros.
              tlaAssert (0 <= "V" + "a" * tdiff).
              * solve_nonlinear.
              * tlaAssert (0 <= tdiff <= d);
                [ solve_linear | charge_intros ].
                reason_action_tac. intuition.
                specialize (H10 (pre "T" - pre "t"))%R.
                intuition.
                eapply Rle_trans; eauto.
                repeat match goal with
                       | [ H : eq (post _) _ |- _ ]
                         => rewrite H in *; clear H
                       end.
                rewrite Rplus_assoc.
                apply Rplus_le_compat.
                { solve_linear. }
                { pose proof (sdist_tdist_tdist "v" x).
                  breakAbstraction. unfold eval_comp in *;
                                    simpl in *.
                  specialize (H14 (Stream.Cons pre
                                               (Stream.Cons
                                                  post tr))).
                  intuition. simpl in *.
                  pose proof (sdist_incr "v" ("V" + "a"*tdiff)).
                  breakAbstraction. unfold eval_comp in *;
                                    simpl in *.
                  specialize (H14 (Stream.Cons pre
                                               (Stream.Cons
                                                  post tr))).
                  intuition. simpl in *.
                  eapply Rle_trans; [ | apply H14 ].
                  { eapply Rle_trans; eauto.
                    apply Rplus_le_compat.
                    { apply Rplus_le_compat_l.
                      repeat rewrite Rmult_assoc.
                      apply Rmult_le_compat_l; solve_linear.
                      apply Rmult_le_compat_pos_r;
                        solve_nonlinear. }
                    { apply Rmult_le_compat_neg_r;
                      solve_linear.
                      apply Rmult_le_compat_neg_r;
                      solve_linear.
                      apply Rle_sq_pos; solve_linear.
                      solve_nonlinear. } }
                  { solve_nonlinear. }
                  { solve_nonlinear. } }
            + tlaAssert ("v" >= 0 \\// "v" <= 0);
              [ solve_linear | tlaIntro ].
              decompose_hyps.
              { reason_action_tac. intuition.
                intuition.
                specialize (H8 (pre "T" - pre "t"))%R.
                intuition.
                repeat match goal with
                       | [ H : eq (post _) _ |- _ ]
                         => rewrite H in *; clear H
                       end.
                repeat match type of H22 with
                       | ?H -> _ =>
                         let HH := fresh "H" in
                         assert H as HH by solve_linear;
                           specialize (H22 HH); clear HH
                       end.
                eapply Rle_trans; eauto.
                apply Rplus_le_compat.
                { solve_linear. }
                { pose proof (sdist_tdist "v" x).
                  breakAbstraction. unfold eval_comp in *;
                                    simpl in *.
                  specialize (H12 (Stream.Cons pre
                                               (Stream.Cons
                                                  post tr))).
                  intuition. simpl in *.
                  pose proof (sdist_incr "v" ("V" + "a"*tdiff)).
                  breakAbstraction.
                  specialize (H12 (Stream.Cons pre
                                               (Stream.Cons
                                                  post tr))).
                  intuition. simpl in *.
                  eapply Rle_trans; [ | apply H12 ].
                  { eapply Rle_trans; eauto.
                    apply Rplus_le_compat; solve_linear.
                    repeat rewrite Rmult_assoc.
                    apply Rmult_le_compat_l;
                      solve_linear.
                    apply Rmult_le_compat_pos_r;
                      solve_linear.
                    solve_nonlinear. }
                  { solve_nonlinear. }
                  { solve_nonlinear. } } }
            { tlaAssert ("y" <= ub).
              - rewrite <- inv_safe. charge_tauto.
              - reason_action_tac. intuition.
                repeat match goal with
                     | [ H : eq (post _) _ |- _ ]
                       => rewrite H in *; clear H
                     end.
                eapply Rle_trans; eauto.
                clear - H3 amin_lt_0 H2 H6 H17.
                solve_nonlinear. } }
      { solve_linear. }
      { solve_linear. }
  Qed.
*)

(* This was an idea for showing that the system
   is a refinement of another system that does not have
   a continuous evolution but instead replaces the continous
   evolution with the solution to the differential equations.
   This is specified by Evolve. However, I couldn't
   figure out how to prove refinement. *)

(*
  Definition Evolve : Formula :=
         "y"! = "y" + tdist "v" "a" ("t" - "t"!)
    //\\ "v"! = "v" + "a"*("t" - "t"!).

  Definition AbstractNext :=
         Evolve
    \\// (Ctrl //\\ History).

  Definition AbstractSys : Formula :=
    I //\\ []AbstractNext.

  Theorem refinement :
    |-- Spec -->> AbstractSys.
  Proof.
    unfold Spec, SpecR, AbstractSys. charge_intros.
    charge_split.
    - charge_assumption.
    - unfold SysD. simpl. restoreAbstraction.
      unfold sysD. tlaRevert. apply BasicProofRules.always_imp.
      unfold Next, AbstractNext. charge_intros.
      decompose_hyps.
      + apply lorR1. unfold Evolve.
        *)

End SecondDerivShimCtrl.

Close Scope HP_scope.
Close Scope string_scope.