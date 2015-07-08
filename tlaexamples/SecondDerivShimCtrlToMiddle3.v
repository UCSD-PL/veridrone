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
  Parameter ub_ubv : (ubv*d + ubv*ubv*(0 - / 2)*(/amin) <= ub)%R.


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
    assert (/ y < 0)%R by solve_linear.
    assert (0 - / 2 < 0)%R by solve_linear.
    generalize dependent (/y)%R.
    generalize dependent (0 - / 2)%R.
    solve_nonlinear.
  Qed.

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
                 specialize (H23 H5).
                 revert H23. intros.

                 rewrite <- H14 in H23. rewrite <- H16 in H23.
                 rewrite <- H16 in H0.
                 clear - H23 H0 amin_lt_0.
                 assert (/amin < 0)%R by solve_linear.
                 assert (0 - / 2 < 0)%R by solve_linear.
                 assert (/ 2 > 0)%R by solve_linear.
                 simpl in *.
                 Print plus_assoc_reverse.
                 Lemma simplPlus : forall x y z:R, (x + y + z)%R = (x + (y + z))%R.
                 Proof.
                   solve_linear.
                 Qed.
                 intros.
                 rewrite simplPlus in H23.
                 remember (Stream.hd (Stream.tl tr) "V" * d + / 2 * 0 * (d * (d * 1)) +
                           (Stream.hd (Stream.tl tr) "V" + 0 * d) *
                           ((Stream.hd (Stream.tl tr) "V" + 0 * d) * 1) * 
                           (0 - / 2) * / amin)%R.
                 rewrite simplPlus.
                 remember (Stream.hd (Stream.tl tr) "V" * x +
                           / 2 * Stream.hd (Stream.tl tr) "a" * (x * (x * 1)) +
                           (Stream.hd (Stream.tl tr) "V" + Stream.hd (Stream.tl tr) "a" * x) *
                           ((Stream.hd (Stream.tl tr) "V" + Stream.hd (Stream.tl tr) "a" * x) * 1) *
                           (0 - / 2) * / amin)%R.
                 clear Heqr0 Heqr.
                 generalize dependent (/amin)%R.
                 generalize dependent (0 - / 2)%R.
                 generalize dependent (/ 2)%R.
                 solve_nonlinear.
               }
               {

                 clear -amin_lt_0 x tr H5 H1 H16 H24 H2 n.


                 assert (/amin < 0)%R by solve_linear.
                 assert (0 - / 2 < 0)%R by solve_linear.
                 assert (/ 2 > 0)%R by solve_linear.
                 generalize dependent (/amin)%R.
                 generalize dependent (0 - / 2)%R.
                 generalize dependent (/ 2)%R.
                 solve_nonlinear.
               }
           -
             breakAbstraction. intros. 
             decompose [and] H.  specialize (H20 H4). rewrite <- H13 in H20. rewrite <- H15 in H20.
             decompose [and] H0.
             clear -H4 H20 H25 H23 H24 amin_lt_0.
             
             rewrite simplPlus in H20.
             rewrite simplPlus.
             pose proof (tdist_sdist_incr).
             repeat match goal with
                      | [ _ : context [Stream.hd (Stream.tl tr) ?a] |- _ ]
                        => generalize dependent (Stream.hd (Stream.tl tr) a)
                    end; intros.
              repeat match goal with
                      | [ _ : context [Stream.hd (Stream.tl tr) ?a] |- _ ]
                        => generalize dependent (Stream.hd (Stream.tl tr) a)
                    end; intros.
              specialize (H v0 v0 v v x d).
              breakAbstraction.
              specialize (H tr).
              intuition.
              assert (v0 <= v0)%R by solve_linear. 
              assert (v <= v)%R by solve_linear.
              apply Rge_le in H4.
              specialize (H0 H H1 H25 H4 H24 H23).
              solve_linear.
              
          -
            unfold SafeAcc.
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
          
              clear -amin_lt_0 x tr H0 H22 sProof3.
              
              decompose [and] H0. clear H0.
              Check Rle_dec.
              repeat match goal with
                       | [ _ : context [(Stream.hd (Stream.tl tr) ?x)] |- _ ]
                         => generalize dependent (Stream.hd (Stream.tl tr) x)
                     end; intros.
              repeat match goal with
                       | [ _ : context [(Stream.hd (Stream.tl tr) ?x)] |- _ ]
                         => generalize dependent (Stream.hd (Stream.tl tr) x)
                     end; intros.
              remember v as y.
              clear v Heqy.
              remember v0 as v.
              clear Heqv v0.
              remember v1 as a.
              clear Heqa v1.
              destruct (Rle_dec v R0).
              solve_nonlinear.
              SearchAbout (~(_ <= _) -> (_ > _ ))%R.
              apply Rnot_le_gt in n.
              assert (a < 0)%R.
              solve_nonlinear.
              assert ((/ 2 * a * (x * (x * 1)) <= 0))%R.
              solve_nonlinear.
              assert ( (v + 0 * d) * ((v + 0 * d) * 1)  * (0 - / 2) * / amin > 0)%R.

              SearchAbout (0 * _)%R.
              rewrite Rmult_0_l.
              SearchAbout (_ + 0)%R.
              rewrite Rplus_0_r.
              rewrite Rmult_1_r.
              assert (0 - / 2 < 0)%R by solve_linear.
              
              clear -n H amin_lt_0.
              rewrite Rmult_assoc.
              rewrite Rmult_assoc.
              clear H.
              
              SearchAbout (_ * _ > 0 )%R.
              apply Rmult_gt_0_compat.
              intuition.
              apply Rmult_gt_0_compat.
              intuition.
              assert (0 - / 2 < 0)%R by solve_linear.
              assert (/amin < 0)%R by solve_linear.
              remember (0 - / 2)%R.
              remember (/amin)%R.
              solve_nonlinear.
              
              assert (v * d + / 2 * 0 * (d * (d * 1)) >= (v * x + / 2 * a * (x * (x * 1))))%R.
             
              rewrite Rmult_assoc.
              rewrite  Rmult_0_l.
              rewrite Rmult_0_r.
              rewrite Rplus_0_r.
              remember (/ 2 * a * (x * (x * 1)))%R.
              assert (v * d >= v * x)%R.
              solve_nonlinear.
              solve_linear.
              solve_linear.
             
            }
            {

              apply Rnot_ge_lt in n.
              decompose [and] H7.
              pose proof conj as conjIndInvPremise.
              specialize (conjIndInvPremise (0 <= Stream.hd tr "T" - Stream.hd tr "t" <= d)%R (Stream.hd tr "V" +  Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t") < 0)%R indInvPremise2 n).
              specialize (H16 conjIndInvPremise).  
              rewrite <- H13 in H5. rewrite <- H15 in H3.
              clear -amin_lt_0 H0 H5 H3 H16 conjIndInvPremise.
              decompose [and] H0. clear H0. 
              decompose [and] conjIndInvPremise. clear conjIndInvPremise.
              clear H4 H6 H7.
              z3 solve_dbg.
              
              repeat match goal with
                       | [ _ : context [Stream.hd (Stream.tl tr) ?t] |- _ ]
                         => generalize dependent (Stream.hd  (Stream.tl tr) t)
                     end; intros;
              repeat match goal with
                       | [ _ : context [Stream.hd  (Stream.tl tr) ?t] |- _ ]
                         => generalize dependent (Stream.hd  (Stream.tl tr) t)
                     end; intros.
              repeat match goal with
                       | [ _ : context [Stream.hd tr ?t] |- _ ]
                         => generalize dependent (Stream.hd tr t)
                     end; intros;
              repeat match goal with
                       | [ _ : context [Stream.hd tr ?t] |- _ ]
                         => generalize dependent (Stream.hd tr t)
                     end; intros;
              
               repeat match goal with
                       | [ _ : context [Stream.hd tr ?t] |- _ ]
                         => generalize dependent (Stream.hd tr t)
                     end; intros.

                repeat match goal with
                       | [ _ : context [Stream.hd tr ?t] |- _ ]
                         => generalize dependent (Stream.hd tr t)
                     end; intros.
              repeat match goal with
                       | [ _ : context [Stream.hd tr ?t] |- _ ]
                         => generalize dependent (Stream.hd tr t)
                     end; intros.
              
              
              Lemma tdistNeg : forall v' y' a' x ub, 
                  |-- y' <= ub -->> v' < 0 -->> 0 <= x -->> v' + a' * x < 0 -->> 
                      (y' + (v' * x + / 2 * a' * (x * (x * 1))) <= ub).
              Proof.
                pose proof tdist_vel_neg.
                breakAbstraction ; intros.
                specialize (H v' a' x tr). intuition.
                repeat match goal with
                         | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
                           => generalize dependent (eval_term t s1 s2)
                       end; intros;
                repeat match goal with
                         | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
                           => generalize dependent (eval_term t s1 s2)
                       end; intros.
                assert (r1 <= 0)%R.
                solve_linear.
                solve_linear.
              Qed.
              
              pose proof (tdistNeg).
              specialize (H v0 v v1 x ub).
              breakAbstraction.
              specialize (H tr).
              intuition.
              assert (v <= ub)%R.
              solve_linear.
              assert (v0 < 0)%R.
              solve_linear.
              specialize (H4 H H6 H2 H1).
              solve_linear.
              
              
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
               assert (/amin < 0)%R by solve_linear.
              assert (0 - / 2 < 0)%R by solve_linear.
              assert (/ 2 > 0)%R by solve_linear.
              generalize dependent (/amin)%R.
              generalize dependent (0 - / 2)%R.
              generalize dependent (/ 2)%R.
              solve_nonlinear.
            }
            {
              apply Rnot_ge_lt in n.
              decompose [and] H7.
              pose proof conj as conjIndInvPremise.
              specialize (conjIndInvPremise (0 <= Stream.hd tr "T" - Stream.hd tr "t" <= d)%R (Stream.hd tr "V" +  Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t") < 0)%R indInvPremise2 n).
              specialize (H16 conjIndInvPremise).  
              rewrite <- H13 in H5. rewrite <- H15 in H3.
              clear -amin_lt_0 H0 H5 H3 H16 conjIndInvPremise.
              decompose [and] conjIndInvPremise.
              clear conjIndInvPremise.
               clear H4 H2.  z3 solve_dbg.
              decompose [and] H0. clear H0.
              clear H6.  
              
               repeat match goal with
                       | [ _ : context [(Stream.hd (Stream.tl tr) ?x)] |- _ ]
                         => generalize dependent (Stream.hd (Stream.tl tr) x)
                     end; intros;
              repeat match goal with
                       | [ _ : context [(Stream.hd (Stream.tl tr) ?x)] |- _ ]
                         => generalize dependent (Stream.hd (Stream.tl tr) x)
                     end; intros;
               repeat match goal with
                       | [ _ : context [(Stream.hd tr ?x)] |- _ ]
                         => generalize dependent (Stream.hd tr x)
                     end; intros;
              repeat match goal with
                       | [ _ : context [(Stream.hd tr ?x)] |- _ ]
                         => generalize dependent (Stream.hd tr x)
                     end; intros;
              repeat match goal with
                       | [ _ : context [(Stream.hd tr ?x)] |- _ ]
                         => generalize dependent (Stream.hd tr x)
                     end; intros;
              repeat match goal with
                       | [ _ : context [(Stream.hd tr ?x)] |- _ ]
                         => generalize dependent (Stream.hd tr x)
                     end; intros.
              repeat match goal with
                       | [ _ : context [(Stream.hd tr ?x)] |- _ ]
                         => generalize dependent (Stream.hd tr x)
                     end; intros.
             
              
              pose proof tdistNeg.
              specialize (H v0 v v1 x ub).
              breakAbstraction. specialize (H tr).
              intuition. 
              assert (v <= ub)%R.
              solve_linear.
              assert (v0 < 0)%R.
              solve_linear.
              specialize (H0 H H6 H4 H2).
              solve_linear.
            
            }
        }
        {
          tlaAssert (("y" > 0 //\\ "v" > 0 //\\ "a"! <= amin) \\//
                                                              ("y" > 0 //\\ "v" <= 0 //\\ "a"! <= 0) \\//
                                                              "y" <= 0);
          [ solve_linear | charge_intros; decompose_hyps ].
          {
            
            breakAbstraction. intros. decompose [and] H. clear H.
            pose proof indInvPremise as indInvPremise.
            specialize (indInvPremise (Stream.hd tr "v") (Stream.hd tr "V") (Stream.hd tr "a") (Stream.hd tr "t") (Stream.hd tr "T") H3 H1).
            specialize (H6 (Stream.hd tr "T" - Stream.hd tr "t")%R indInvPremise).
            
            pose proof indInvPremise2 as indInvPremise2.
            specialize (indInvPremise2  (Stream.hd tr "t") (Stream.hd tr "T") H7 H9 H5).
            destruct (Rge_dec ( Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) R0).
            {
              apply Rge_le in r.
              
              (* proving  0 <= T-t <=d*)
              pose proof conj as conjIndInvPremise.
              specialize (conjIndInvPremise (0 <= Stream.hd tr "T" - Stream.hd tr "t" <= d)%R (0 <= Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t"))%R indInvPremise2 r).
              decompose [and] H6. clear H6.
              specialize (H conjIndInvPremise). 
              split. 
              {
                intros. z3 solve_dbg.
                rewrite H12 in *. rewrite H14 in *.

                clear -amin_lt_0 d_gt_0 x tr H4 H1 H15 H19 H22 H H6.
                decompose [and] H6.
                clear H6. clear H5. 
                clear H15. clear H19.
                clear d_gt_0.
                
                Lemma tdistLessThanAmin : forall v' a' d2, 
                    |-- 0 <= d2  -->> a' <= amin -->> v' + a' * d2 >= 0-->> tdist v' a' d2 + sdist (v' + a'*d2) <= sdist v' .
                  pose proof amin_lt_0.
                  breakAbstraction.
                  intros.
                  repeat match goal with
                           | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
                             => generalize dependent (eval_term t s1 s2)
                         end; intros;
                  repeat match goal with
                           | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
                             => generalize dependent (eval_term t s1 s2)
                         end; intros.
                  clear v' a' d2.
                 remember r1 as v'.
                 remember r as d1.
                 remember r0 as a'.
                 clear Heqv' Heqd1 Heqa' r1 r0 r.
                 pose proof sdist_tdist_tdist.
                 specialize (H4 v' d1).
                 breakAbstraction.
                 specialize (H4 tr). intuition.
                 
                 assert (/ 2 * amin * (d1 * (d1 * 1)) >= / 2 * a' * (d1 * (d1 * 1)) )%R.
                 
                 clear H5.
                 solve_nonlinear.
                 
                 assert (((v' + amin * d1) * ((v' + amin * d1) * 1) * (0 - / 2) * / amin) >= ((v' + a' * d1) * ((v' + a' * d1) * 1) * (0 - / 2) * / amin))%R.
                 clear H5 H4.
                 assert (v' >= 0)%R.
                 solve_nonlinear.
                 assert ((v' + amin * d1) >= (v' + a' * d1))%R.
                 solve_nonlinear.
                 SearchAbout (_ * _)%R.
                 SearchAbout (_ * _ >= _ * _)%R.
                  assert (/amin < 0)%R by solve_linear.
                 assert (0 - / 2 < 0)%R by solve_linear.
                 generalize dependent (/amin)%R.
                 generalize dependent (0 - / 2)%R. 
                 intros.
                 SearchAbout (_ * _ >= _ * _)%R.
                 remember ((v' + amin * d1) * ((v' + amin * d1) * 1) * r * r0)%R.
                 remember ((v' + a' * d1) * ((v' + a' * d1) * 1) * r * r0)%R.
                 Check Rmult_assoc.
                 repeat rewrite Rmult_assoc in Heqr1.
                 repeat rewrite Rmult_assoc in Heqr2.
                 rewrite Heqr1.
                 rewrite Heqr2.
                 apply Rmult_ge_compat.
                 apply H3.
                 assert((1* (r * r0))>=0)%R.
                 remember (1 * (r * r0))%R.
                 rewrite Rmult_1_l in Heqr3.
                 clear -H7 H6 Heqr3.
                 solve_nonlinear.
                 clear -H3 H8.
                 generalize dependent (v' + a' * d1)%R.
                 generalize dependent (1 * (r * r0))%R.
                 solve_nonlinear.
                 apply H5.
                 apply Rmult_ge_compat.
                 apply H3.
                 remember (1 * (r * r0))%R.
                 rewrite Rmult_1_l in Heqr3.
                 clear -H7 H6 Heqr3.
                 solve_nonlinear.
                 apply H5.
                 intuition.
                 solve_linear.
                Qed.
                pose proof tdistLessThanAmin.
                specialize (H0 (Stream.hd tr "v") ( Stream.hd (Stream.tl tr) "a") x).
                breakAbstraction.
                specialize (H0 tr).
                intuition.
                SearchAbout (_ <= _ -> _ >= _)%R.
                apply Rle_ge in H2.
                specialize (H5 H2).
                Local Close Scope HP_scope.
                unfold value.
                assert ((Stream.hd tr "v")%R =  (Stream.hd tr "V" + 
                         (Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t"))%R)%R)%R.
                clear -H1.
                unfold Value.
                solve_linear.
                rewrite <- H0 in H.
                remember (Stream.hd tr "y" +
                          (Stream.hd tr "v" * x +
                           / 2 * Stream.hd (Stream.tl tr) "a" * (x * (x * 1))) +
                          (Stream.hd tr "v" + Stream.hd (Stream.tl tr) "a" * x) *
                          ((Stream.hd tr "v" + Stream.hd (Stream.tl tr) "a" * x) * 1) * 
                          (0 - / 2) * / amin)%R.
                repeat rewrite Rplus_assoc in Heqr.
                repeat rewrite Rplus_assoc in H5.
             
                z3 solve_dbg.
                solve_linear.
               
              }
              {
                intros.
                rewrite H12 in *. rewrite H14 in *.
                clear H12 H14 H18 H17 H16 H20. clear H19 H2. clear indInvPremise indInvPremise2 r conjIndInvPremise. clear H21 H6. clear H0 H3. clear H7 H9 H5 H11 H10 H13 H8. clear H15. 
                clear -amin_lt_0 x tr H4 H1 H22 H.
                
                Open Scope HP_scope.
                Lemma tdistLessThanAmin2 : forall v a x, |-- a <= amin -->> tdist v a x <= sdist v.
                Proof.
                  breakAbstraction. intros. pose proof amin_lt_0. z3 solve_dbg.
                  remember (eval_term v (Stream.hd tr) (Stream.hd (Stream.tl tr))) as v'.
                  remember (eval_term a (Stream.hd tr) (Stream.hd (Stream.tl tr))) as a'.
                  remember (eval_term x (Stream.hd tr) (Stream.hd (Stream.tl tr))) as x'.
                  clear Heqa' Heqx' Heqv'. clear v a x.
                  pose proof tdist_incr_acc.
                  pose proof sdist_tdist.
                  specialize (H2 a' amin v' x').
                  specialize (H3 v' x').
                  breakAbstraction.
                  specialize (H2 tr). specialize (H3 tr).
                  intuition.
                  solve_linear.
                Qed.
                pose proof tdistLessThanAmin2.
                specialize (H0 (Stream.hd tr "v") (Stream.hd (Stream.tl tr) "a") x).
                breakAbstraction.
                specialize (H0 tr). intuition.
                Close Scope HP_scope.
                remember ((Stream.hd tr "v" * x +
                           / 2 * Stream.hd (Stream.tl tr) "a" * (x * (x * 1))))%R.
                remember (Stream.hd tr "Y" +
       (Stream.hd tr "V" * (Stream.hd tr "T" - Stream.hd tr "t") +
        / 2 * Stream.hd tr "a" *
        ((Stream.hd tr "T" - Stream.hd tr "t") *
         ((Stream.hd tr "T" - Stream.hd tr "t") * 1))) +
       (Stream.hd tr "V" +
        Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
       ((Stream.hd tr "V" +
         Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
       (0 - / 2) * / amin)%R.
                repeat rewrite Rplus_assoc in Heqr.
                repeat rewrite <- Rplus_assoc in Heqr0.
                repeat rewrite Rplus_assoc in H4.
                assert ((Stream.hd tr "v")%R =  (Stream.hd tr "V" + 
                         (Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t"))%R)%R)%R.
                clear -H1.
                unfold Value.
                
                solve_linear.
                assert (Stream.hd tr "y" + (Stream.hd tr "V" +
                                            Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
                                           ((Stream.hd tr "V" +
                                             Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
                                           (0 - / 2) * / amin <= ub)%R.
                solve_linear.
                rewrite <- H2 in H3.
                solve_linear.
              }
            }
            {
              split.
              intros.
              rewrite H12 in *.
              rewrite H14 in *.
              clear -amin_lt_0 H0 H1 n H2.
              assert (/amin < 0)%R by solve_linear.
              assert (0 - / 2 < 0)%R by solve_linear.
              assert (/ 2 > 0)%R by solve_linear.
              generalize dependent (/amin)%R.
              generalize dependent (0 - / 2)%R.
              generalize dependent (/ 2)%R.
              solve_nonlinear.
              clear -amin_lt_0 H0 H1 n H2.
              intros.
              assert (/amin < 0)%R by solve_linear.
              assert (0 - / 2 < 0)%R by solve_linear.
              assert (/ 2 > 0)%R by solve_linear.
              generalize dependent (/amin)%R.
              generalize dependent (0 - / 2)%R.
              generalize dependent (/ 2)%R.
              solve_nonlinear.
            }
          }
          {
             breakAbstraction. intros. decompose [and] H. clear H.
            pose proof indInvPremise as indInvPremise.
            specialize (indInvPremise (Stream.hd tr "v") (Stream.hd tr "V") (Stream.hd tr "a") (Stream.hd tr "t") (Stream.hd tr "T") H3 H1).
            specialize (H6 (Stream.hd tr "T" - Stream.hd tr "t")%R indInvPremise).
            
            pose proof indInvPremise2 as indInvPremise2.
            specialize (indInvPremise2  (Stream.hd tr "t") (Stream.hd tr "T") H7 H9 H5).
            destruct (Rge_dec ( Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) R0).
            {
              apply Rge_le in r.
              
              (* proving  0 <= T-t <=d*)
              
              pose proof conj as conjIndInvPremise.
              specialize (conjIndInvPremise (0 <= Stream.hd tr "T" - Stream.hd tr "t" <= d)%R (0 <= Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t"))%R indInvPremise2 r).
              decompose [and] H6. clear H6.
              specialize (H conjIndInvPremise). 
              split. 
              {
                intros. 
                rewrite H12 in *. rewrite H14 in *.
                clear -amin_lt_0 H4 H6 H2 H22 H.
                decompose [and] H6. clear H6.
                assert (Stream.hd tr "v" + Stream.hd (Stream.tl tr) "a" * x = 0)%R.
                solve_nonlinear.
                rewrite H0 in *.
                Local Open Scope HP_scope.
             (*   Lemma yLessThanUb : forall a y Y V T t,|-- y - Y <= V * (T - t) + / 2 * a * ((T - t) * ((T -t)*1)) -->> Y + (V * (T-t) + /2 * a * ((T - t) * ((T -t) *1))) + ( V + a * (T - t) * ((V + a * (T - t)) * 1) * (0 -/ 2) * /amin) <= ub -->> y <= ub.
                 Proof.
                   breakAbstraction.
                   intros.
                   simpl in *.
                    repeat match goal with
                           | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
                             => generalize dependent (eval_term t s1 s2)
                         end; intros;
                  repeat match goal with
                           | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
                             => generalize dependent (eval_term t s1 s2)
                         end; intros;
                     repeat match goal with
                           | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
                             => generalize dependent (eval_term t s1 s2)
                         end; intros;
                  repeat match goal with
                           | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
                             => generalize dependent (eval_term t s1 s2)
                         end; intros.
                     repeat match goal with
                           | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
                             => generalize dependent (eval_term t s1 s2)
                         end; intros.
                  repeat match goal with
                           | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
                             => generalize dependent (eval_term t s1 s2)
                         end; intros.
                  
                   rewrite Rmult_1_r in H1.
                   pose proof amin_lt_0.
                   assert (/amin < 0)%R by solve_linear.
                assert (0 - / 2 < 0)%R by solve_linear.
                generalize dependent (/amin)%R.
                generalize dependent (0 - / 2)%R.
                intros.
                assert (((r1 - r2) * ((r1 - r2) * 1)) >= 0)%R.
                rewrite Rmult_1_r.
                solve_nonlinear.
                
               
                
                admit.
                Qed.*)
                    assert (Stream.hd tr "y" <= ub)%R.
                remember (Stream.hd tr "Y" +
                          (Stream.hd tr "V" * (Stream.hd tr "T" - Stream.hd tr "t") +
                           / 2 * Stream.hd tr "a" *
                           ((Stream.hd tr "T" - Stream.hd tr "t") *
                            ((Stream.hd tr "T" - Stream.hd tr "t") * 1))) +
                          (Stream.hd tr "V" +
                           Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
                          ((Stream.hd tr "V" +
                            Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
                          (0 - / 2) * / amin)%R.
                remember (Stream.hd tr "V" * (Stream.hd tr "T" - Stream.hd tr "t") +
          / 2 * Stream.hd tr "a" *
          ((Stream.hd tr "T" - Stream.hd tr "t") *
           ((Stream.hd tr "T" - Stream.hd tr "t") * 1)))%R.
                assert ( (Stream.hd tr "V" +
           Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
          ((Stream.hd tr "V" +
            Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
          (0 - / 2) * / amin >= 0)%R.
                
                remember ((Stream.hd tr "V" +
                           Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
                          ((Stream.hd tr "V" +
                            Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
                          (0 - / 2) * / amin)%R.
                rewrite Rmult_1_r in Heqr1.
                remember ((Stream.hd tr "V" +
            Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")))%R.
                clear -Heqr1 amin_lt_0.
                
                 assert (/amin < 0)%R by solve_linear.
                assert (0 - / 2 < 0)%R by solve_linear.
                generalize dependent (/amin)%R.
                generalize dependent (0 - / 2)%R.
                intros.
                assert (r2 * r2 >= 0)%R.
                clear.
                
                solve_nonlinear.
                remember (r2 * r2)%R.
                assert (r * r0 > 0)%R.
                solve_nonlinear.
                rewrite Rmult_assoc in Heqr1.
                remember (r * r0)%R.
                clear -H1 H2 Heqr1.
                solve_nonlinear.
                solve_linear.
                assert (Stream.hd tr "v" * x  <= R0)%R.
                clear -H2 H1 H3.
                solve_nonlinear.
                assert (( / 2 * Stream.hd (Stream.tl tr) "a" * (x * (x * 1))) +
                        0 * (0 * 1) * (0 - / 2) * / amin <= R0)%R.
                repeat rewrite Rmult_0_l.
                repeat rewrite Rplus_0_r.
                repeat rewrite <- Rmult_assoc.
                rewrite Rmult_1_r.
                assert (x*x >= 0)%R.
                solve_nonlinear.
                solve_nonlinear.
                solve_linear.
                
              }
              {
                intros.
                rewrite H12 in *. rewrite H14 in *.
                clear -amin_lt_0 H4 H6 H2 H.
                decompose [and] H6. clear H6.
                clear H5. 
                z3 solve_dbg.
                   assert (Stream.hd tr "y" <= ub)%R.
                remember (Stream.hd tr "Y" +
                          (Stream.hd tr "V" * (Stream.hd tr "T" - Stream.hd tr "t") +
                           / 2 * Stream.hd tr "a" *
                           ((Stream.hd tr "T" - Stream.hd tr "t") *
                            ((Stream.hd tr "T" - Stream.hd tr "t") * 1))) +
                          (Stream.hd tr "V" +
                           Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
                          ((Stream.hd tr "V" +
                            Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
                          (0 - / 2) * / amin)%R.
                remember (Stream.hd tr "V" * (Stream.hd tr "T" - Stream.hd tr "t") +
          / 2 * Stream.hd tr "a" *
          ((Stream.hd tr "T" - Stream.hd tr "t") *
           ((Stream.hd tr "T" - Stream.hd tr "t") * 1)))%R.
                assert ( (Stream.hd tr "V" +
           Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
          ((Stream.hd tr "V" +
            Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
          (0 - / 2) * / amin >= 0)%R.
                
                remember ((Stream.hd tr "V" +
                           Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
                          ((Stream.hd tr "V" +
                            Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
                          (0 - / 2) * / amin)%R.
                rewrite Rmult_1_r in Heqr1.
                remember ((Stream.hd tr "V" +
            Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")))%R.
                clear -Heqr1 amin_lt_0.
                
                 assert (/amin < 0)%R by solve_linear.
                assert (0 - / 2 < 0)%R by solve_linear.
                generalize dependent (/amin)%R.
                generalize dependent (0 - / 2)%R.
                intros.
                assert (r2 * r2 >= 0)%R.
                clear.
                
                solve_nonlinear.
                remember (r2 * r2)%R.
                assert (r * r0 > 0)%R.
                solve_nonlinear.
                rewrite Rmult_assoc in Heqr1.
                remember (r * r0)%R.
                clear -H1 H2 Heqr1.
                solve_nonlinear.
                solve_linear.
                solve_nonlinear.
              }
            }
          
            {
              split.
              {
                intros. 
                rewrite H12 in *. rewrite H14 in *.
                clear -amin_lt_0 H1 H n H22 .
                decompose [and] H. clear H.
                clear H4.
                z3 solve_dbg.
                solve_nonlinear.
                
              }
              {
                apply Rnot_ge_lt in n.
                decompose [and] H6. clear H6.
                pose proof conj as conjIndInvPremise.
                specialize (conjIndInvPremise (0 <= Stream.hd tr "T" - Stream.hd tr "t" <= d)%R (Stream.hd tr "V" +  Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t") < 0)%R indInvPremise2 n).
                specialize (H21 conjIndInvPremise).                
                intros.
                rewrite H12 in *. rewrite H14 in *.
                clear conjIndInvPremise indInvPremise indInvPremise2.
                clear H12 H14 H18 H17 H16 H20 H7 H9 H5 H11 H10 H13 H8 H15.
                z3 solve_dbg.
                clear -amin_lt_0 H1 H4 n  H6  H21.
                decompose [and] H6. clear H6.
                clear H3. z3 solve_dbg.
                  assert (Stream.hd tr "y" <= ub)%R.
                remember (Stream.hd tr "Y" +
                          (Stream.hd tr "V" * (Stream.hd tr "T" - Stream.hd tr "t") +
                           / 2 * Stream.hd tr "a" *
                           ((Stream.hd tr "T" - Stream.hd tr "t") *
                            ((Stream.hd tr "T" - Stream.hd tr "t") * 1))) +
                          (Stream.hd tr "V" +
                           Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
                          ((Stream.hd tr "V" +
                            Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
                          (0 - / 2) * / amin)%R.
                remember (Stream.hd tr "V" * (Stream.hd tr "T" - Stream.hd tr "t") +
          / 2 * Stream.hd tr "a" *
          ((Stream.hd tr "T" - Stream.hd tr "t") *
           ((Stream.hd tr "T" - Stream.hd tr "t") * 1)))%R.
                assert ( (Stream.hd tr "V" +
           Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
          ((Stream.hd tr "V" +
            Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
          (0 - / 2) * / amin >= 0)%R.
                
                remember ((Stream.hd tr "V" +
                           Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) *
                          ((Stream.hd tr "V" +
                            Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) * 1) *
                          (0 - / 2) * / amin)%R.
                rewrite Rmult_1_r in Heqr1.
                remember ((Stream.hd tr "V" +
            Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")))%R.
                clear -Heqr1 amin_lt_0.
                
                 assert (/amin < 0)%R by solve_linear.
                assert (0 - / 2 < 0)%R by solve_linear.
                generalize dependent (/amin)%R.
                generalize dependent (0 - / 2)%R.
                intros.
                assert (r2 * r2 >= 0)%R.
                clear.
                
                solve_nonlinear.
                remember (r2 * r2)%R.
                assert (r * r0 > 0)%R.
                solve_nonlinear.
                rewrite Rmult_assoc in Heqr1.
                remember (r * r0)%R.
                clear -H1 H2 Heqr1.
                solve_nonlinear.
                 solve_linear.
                solve_nonlinear.
               
              }
            }
          }
          {
            breakAbstraction. intros. decompose [and] H. clear H.
            pose proof indInvPremise as indInvPremise.
            specialize (indInvPremise (Stream.hd tr "v") (Stream.hd tr "V") (Stream.hd tr "a") (Stream.hd tr "t") (Stream.hd tr "T") H3 H1).
            specialize (H6 (Stream.hd tr "T" - Stream.hd tr "t")%R indInvPremise).
            
            pose proof indInvPremise2 as indInvPremise2.
            specialize (indInvPremise2  (Stream.hd tr "t") (Stream.hd tr "T") H7 H9 H5).
            destruct (Rge_dec ( Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t")) R0).
            { 
              apply Rge_le in r.
              (* proving  0 <= T-t <=d*)
              pose proof conj as conjIndInvPremise.
              specialize (conjIndInvPremise (0 <= Stream.hd tr "T" - Stream.hd tr "t" <= d)%R (0 <= Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t"))%R indInvPremise2 r).
              decompose [and] H6. clear H6.
              specialize (H conjIndInvPremise). 
              clear H19.
              split.
              intros.
              decompose [and] H6.
              pose proof ub_ubv.
              rewrite H14 in *.
              clear H14.
              rewrite H12 in *.
              clear -amin_lt_0 x tr H0 H2 H3 H21 H22 H23 H19.
              assert ((Stream.hd tr "v" * x + / 2 * Stream.hd (Stream.tl tr) "a" * (x * (x * 1))) <= ubv * d)%R.
              
              z3 solve_dbg.
              clear -H0 amin_lt_0 H22 H23 H3 H21. 
              z3 solve_dbg.
              solve_nonlinear.
              
              assert ((Stream.hd tr "v" + Stream.hd (Stream.tl tr) "a" * x) *
                      ((Stream.hd tr "v" + Stream.hd (Stream.tl tr) "a" * x) * 1) * 
                      (0 - / 2) * / amin <= ubv * ubv * (0 - / 2) * / amin)%R.
              
              rewrite Rmult_1_r.
              z3 solve_dbg.
              clear -H0 H3 H22 H23  H21 amin_lt_0.
              z3 solve_dbg.
              
              clear H3.
              z3 solve_dbg.
              SearchAbout (_ * _ <= _ * _)%R.
              remember ( ubv * ubv * (0 - / 2) * / amin)%R.
              rewrite Rmult_assoc in Heqr.
              
              rewrite Rmult_assoc.
              rewrite Heqr.
              apply Rmult_le_compat_pos_r.
              assert (/amin < 0)%R by solve_linear.
              assert (0 - / 2 < 0)%R by solve_linear.
              solve_nonlinear.
              solve_linear.
              rewrite  Rplus_assoc.
              remember(Stream.hd tr "v" * x +
       / 2 * Stream.hd (Stream.tl tr) "a" * (x * (x * 1)))%R.
              remember ((Stream.hd tr "v" + Stream.hd (Stream.tl tr) "a" * x) *
        ((Stream.hd tr "v" + Stream.hd (Stream.tl tr) "a" * x) * 1) *
        (0 - / 2) * / amin)%R.
              solve_linear.
              
              

              
             
              intros.
              pose proof ub_ubv.
              rewrite H12 in *. rewrite H14 in *. clear H12 H14 H18 H17 H16. 
              clear H7 H9 H5 H11 H10 H13. clear H4 H1 H8 H15 H20. 
              clear conjIndInvPremise.
              clear indInvPremise2. clear H. clear d_gt_0.
              clear -amin_lt_0 x tr H2 H3 indInvPremise r H6 H19.
              decompose [and] H6.
              clear H6.
              

              
              z3 solve_dbg.
                assert ((Stream.hd tr "v" * x + / 2 * Stream.hd (Stream.tl tr) "a" * (x * (x * 1))) <= ubv * d)%R.
              
              solve_nonlinear.
              remember (Stream.hd tr "v" * x +
       / 2 * Stream.hd (Stream.tl tr) "a" * (x * (x * 1)))%R.
              assert ( ubv * ubv * (0 - / 2) * / amin  >= 0)%R.
              assert (ubv * ubv >= 0)%R.
              solve_nonlinear.
              remember (ubv * ubv)%R.
              assert (/amin < 0)%R by solve_linear.
              assert (0 - / 2 < 0)%R by solve_linear.
              generalize dependent (/amin)%R.
              generalize dependent (0 - / 2)%R.
              intros.
              clear -H5 H6 H7.              
              solve_nonlinear.

              solve_linear.
            
            }
            {
              rewrite H12 in *. rewrite H14 in *.
              split.
              intros.
              pose proof ub_ubv.
              clear -amin_lt_0 H0 H2 H3 H H19.

              assert ((Stream.hd tr "v" * x + / 2 * Stream.hd (Stream.tl tr) "a" * (x * (x * 1))) <= ubv * d)%R.
              
              z3 solve_dbg.
              z3 solve_dbg.
              solve_nonlinear.
              
              assert ((Stream.hd tr "v" + Stream.hd (Stream.tl tr) "a" * x) *
                      ((Stream.hd tr "v" + Stream.hd (Stream.tl tr) "a" * x) * 1) * 
                      (0 - / 2) * / amin <= ubv * ubv * (0 - / 2) * / amin)%R.
              
              rewrite Rmult_1_r.
              z3 solve_dbg.
              
              clear H3.
              z3 solve_dbg.
              SearchAbout (_ * _ <= _ * _)%R.
              remember ( ubv * ubv * (0 - / 2) * / amin)%R.
              rewrite Rmult_assoc in Heqr.
              
              rewrite Rmult_assoc.
              rewrite Heqr.
              apply Rmult_le_compat_pos_r.
              assert (/amin < 0)%R by solve_linear.
              assert (0 - / 2 < 0)%R by solve_linear.
              solve_nonlinear.
              solve_linear.
              rewrite  Rplus_assoc.
              remember(Stream.hd tr "v" * x +
       / 2 * Stream.hd (Stream.tl tr) "a" * (x * (x * 1)))%R.
              remember ((Stream.hd tr "v" + Stream.hd (Stream.tl tr) "a" * x) *
        ((Stream.hd tr "v" + Stream.hd (Stream.tl tr) "a" * x) * 1) *
        (0 - / 2) * / amin)%R.
              solve_linear.
              
              

              
            
              intros. pose proof ub_ubv.
              decompose [and] H6.
              apply Rnot_ge_lt in n.
              pose proof conj as conjIndInvPremise.
              specialize (conjIndInvPremise (0 <= Stream.hd tr "T" - Stream.hd tr "t" <= d)%R (Stream.hd tr "V" + Stream.hd tr "a" * (Stream.hd tr "T" - Stream.hd tr "t") < 0)%R indInvPremise2 n).
              specialize (H22 conjIndInvPremise). 
              clear -amin_lt_0 H2 H3 H H19 H22 H4.
              decompose [and] H. clear H.
              
              assert (Stream.hd tr "y" <= ub)%R.
              solve_linear.
              clear H22. clear H4.
              z3 solve_dbg.
              

              destruct (Rge_dec (Stream.hd tr "v") 0).
              assert(Stream.hd (Stream.tl tr) "a" <= 0 )%R.
              solve_nonlinear.
              assert ( / 2 * Stream.hd (Stream.tl tr) "a" * (x * (x * 1) ) <= 0)%R.
              rewrite Rmult_1_r.
              assert (/ 2 > 0)%R by solve_linear.
              generalize dependent (/ 2)%R.
              intros.
              SearchAbout (_ * _ <= 0)%R.
              rewrite Rmult_assoc.
              apply Rmult_le_0.
              solve_linear.
              rewrite Rmult_comm.
              apply Rmult_le_0.
              solve_nonlinear.
              apply H0.
              assert (Stream.hd tr "v" * x <= ubv * d)%R.
              solve_nonlinear.
              assert ( ubv * ubv * (0 - / 2) * / amin  >= 0)%R.
              assert (ubv * ubv >= 0)%R.
              solve_nonlinear.
              remember (ubv * ubv)%R.
              assert (/amin < 0)%R by solve_linear.
              assert (0 - / 2 < 0)%R by solve_linear.
              generalize dependent (/amin)%R.
              generalize dependent (0 - / 2)%R.
              intros.
              solve_linear.
              z3 solve_dbg.
              clear -H8 H10 H9.
              solve_nonlinear.
              
              solve_linear.
              
              assert ((Stream.hd tr "v" * x <= 0))%R.
              SearchAbout (~(_>=_) )%R.
              SearchAbout (_ >= _)%R.
              apply Rnot_ge_lt in n.
            
               z3 solve_dbg.
              solve_nonlinear.
              solve_nonlinear.
           
               
            
            }
          }
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