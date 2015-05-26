Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Import LibNotations.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import Examples.System.

Open Scope HP_scope.
Open Scope string_scope.

Section VelCtrl.

  (* Upper bound on velocity. *)
  Variable ub : R.
  (* Max time between executions of the
     controller. *)
  Variable d : R.
  Hypothesis d_gt_0 : (d > 0)%R.
  Variable err : R.

  (* The continuous dynamics of the system *)
  Definition w : list DiffEq :=
    ["v"' ::= "a"].
Require Import Coq.Reals.R_sqrt.
Require Import Coq.Reals.Ratan.
  Print sqrt.
  Print Formula.
  Definition aDef ax ay:= SqrtT (ax * ax + ay * ay).
  Definition thetaDef ax ay := ArctanT (ay * (InvT ax)).
 Print SqrtT.
 Print eval_term.
  Definition premise := 
    "a" = aDef "ax" "ay"
      //\\  "a"  > R0
      //\\ "theta" =  thetaDef "ax" "ay"
      //\\ ((Continuous (["vx"'::= "a" * CosT "theta",
                         "vy"'::= "a" * SinT "theta",
                         "a"' ::= 0,
                         "theta"' ::= 0]))
              \\//
              (Continuous (["vx"'::= --"a" * CosT "theta",
                            "vy"'::= --"a" * SinT "theta",
                            "a"' ::= 0,
                            "theta"' ::= 0])) 
              \\//
              (Continuous (["vx"'::= --"a" * CosT "theta",
                            "vy"'::= "a" * SinT "theta",
                            "a"' ::= 0,
                            "theta"' ::= 0]))
              \\//
              (Continuous (["vx"'::= "a" * CosT "theta",
                            "vy"'::= --"a" * SinT "theta",
                            "a"' ::= 0,
                            "theta"' ::= 0])) 

           ).

  Definition conc := Continuous (["vx"' ::= "ax", 
                                  "vy"' ::= "ay",
                                  "ax"' ::= 0, 
                                  "ay"' ::= 0]) .

  Lemma polarCordProof : forall tr, eval_formula (premise -->> conc) tr .
    simpl in *.
    unfold tlaEntails.
    unfold premise,conc.
    simpl in *.
    unfold eval_comp in *.
    unfold aDef in *.
    unfold thetaDef in *.
    simpl in *.
    intros.
    remember (Stream.hd tr "a") as a.
    remember (Stream.hd tr "ax") as ax.
    remember (Stream.hd tr "ay") as ay.
  
    
    remember (Stream.hd tr "vx") as vx.
    remember (Stream.hd tr "vy") as vy.
    remember (Stream.hd tr "theta") as theta.
    decompose [and] H.
    destruct H4.
    {
      assert (mainPremise:=H3).
      destruct H3.
      destruct H3. 
      exists x.
      exists x0.
      decompose [and] H3.
      split.
      {
        apply H3.
      }
      {
        split.
        {
          Require Import Coq.Reals.Rtrigo_def.
          Lemma subProof : forall (ax ay a theta:R), (a > 0 -> a = sqrt (ax*ax + ay*ay) -> 
                                                      theta  = atan (ay/ax) -> 
                                                      (ax = a * cos theta \/ ax = -a * cos theta) /\ ay = a * sin theta)%R.
          Proof.
            intros.
            split.
            {
              SearchAbout atan.
              Lemma tanInv : forall (theta val:R), theta = atan val -> Rtrigo1.tan theta = val.  
              Proof.
                intros.
                pose proof atan_right_inv.
                specialize (H0 val).
                rewrite H.
                apply H0.
              Qed.
              intros.
              apply tanInv in H1.
              pose proof Rtrigo1.sin2_cos2.
              unfold Rtrigo1.tan in *.
              Lemma translate1 : forall (theta ay ax:R), (ax <> 0 -> sin theta / cos theta = ay / ax -> ay = (ax * sin theta)/ cos theta)%R. 
                intros. 
                Require Import Coq.micromega.Psatz.
                clear d_gt_0.
                remember (sin theta) as sin.
                remember (cos theta) as cos.
                Require Import Coq.Reals.RIneq.
                SearchAbout (Rmult).
                Close Scope HP_scope.
                Lemma translate3 : forall (x y z:R), (x = y */ z)%R -> (z <> 0)%R -> (y = x * z)%R.
                Proof. 
                  intros.
                  pose proof Rmult_eq_compat_r.
                  specialize (H1 z x (y */ z)%R H).
                  pose proof Rinv_l_sym.
                  specialize (H2 z H0).
                  SearchAbout Rmult.
                  SearchAbout ((_ * _ * _)= (_ * (_ * _)))%R.
                  rewrite Rmult_assoc in H1.
                  rewrite <- H2 in H1.
                  rewrite RIneq.Rmult_1_r in H1.
                  pose proof eq_sym.
                  apply eq_sym.
                  apply H1.
                Qed.
                intros.
                unfold Rdiv in H0.
                specialize (translate3 (sin */ cos)%R ay ax H0 H).
                intros.
                Lemma multCommt : forall (x y:R), ((x*y)%R = (y* x)%R)%R.
                  intros.
                  psatz R.
                Qed.
                intros.
                rewrite multCommt in H1.
                unfold Rdiv.
                rewrite <- Rmult_assoc in H1.
                apply H1.
              Qed.
              intros.
              destruct (RiemannInt.Req_EM_T ax 0).
              {
                
                rewrite e in H0.
                destruct (RiemannInt.Req_EM_T (cos theta) 0).
                {
                  subst.
                  Print Rtrigo1.tan.
                  psatz R.
                }
                {
                  SearchAbout Rinv.
                  admit.
                }  
              }
              {
                pose proof Rmult_le_reg_r.
                pose proof translate1.
                specialize (H4 theta ay ax n H1).
                rewrite H4 in H1.
                destruct (RiemannInt.Req_EM_T (cos theta) R0).
                {
                  admit.
                }
                {
                  
                  Lemma translate2 : forall (theta ay ax :R),  (cos theta <> 0)%R -> (ax * ax + ax * sin theta /cos theta * (ax * sin theta /cos theta))%R =  ((ax */ cos theta)%R * (ax */ cos theta )%R * (  sin theta * sin theta + cos theta * cos theta))%R.
                  Proof.
                    intros.
                    remember  (ax * ax + ax * sin theta / cos theta * (ax * sin theta / cos theta))%R.
                    pose proof Rmult_eq_compat_l.
                    apply (H0 (cos theta * cos theta)%R) in Heqr.
                    pose proof translate3.
                    SearchAbout Rmult.
                    
                    rewrite Rmult_plus_distr_l in Heqr.
                    unfold Rdiv in *. 
                    Lemma multSimpl2 : forall x y z:R, (x * y * z * (x * y * z) = z * z * (x * x * (y * y)))%R. 
                      intros.
                      psatz R.
                    Qed.
                    intros.
                    rewrite multSimpl2 in Heqr.
                    Lemma multSimpl3 : forall x y z , (x * x * (y* y * (z)) = (y * x) * (y* x) * z)%R.
                      intros.
                      psatz R.
                    Qed.
                    intros.
                    rewrite multSimpl3 in Heqr.
                    rewrite <- Rinv_l_sym in Heqr.
                    Lemma multSimpl4 : forall x, (1 * 1 * x = x)%R.
                      intros.
                      psatz R.
                    Qed.
                    intros.
                    rewrite multSimpl4 in Heqr.
                    Lemma multSimpl5 : forall x y z, (((x * x * (z*z)) + ((z*z) *(y*y))) = (z * z) *(x*x + y*y))%R.
                      intros.
                      psatz R.
                    Qed.
                    intros.
                    rewrite multSimpl5 in Heqr.
                    Lemma translate4 : forall (x y z:R), (z * x = y)%R -> (z <> 0)%R -> (x = y */ z)%R.
                    Proof. 
                      intros.
                      pose proof Rmult_eq_compat_r.
                      pose proof Rmult_eq_reg_r.
                      apply (Rmult_eq_reg_r z).
                      rewrite Rmult_assoc.
                      rewrite  <- Rinv_l_sym.
                      rewrite RIneq.Rmult_1_r.
                      psatz R.
                      apply H0.
                      apply H0.
                    Qed.

                    intros.
                    rewrite Rmult_assoc in Heqr.
                    specialize (translate4 (cos theta * r)%R (ax * ax * (cos theta * cos theta + sin theta * sin theta))%R (cos theta) Heqr H).
                    
                    intros.
                    specialize (translate4 (r)  (ax * ax * (cos theta * cos theta + sin theta * sin theta) */ cos theta)%R (cos theta) H2 H).
                    intros.
                    Lemma multSimpl6 : forall x y z, (x * x * (y) * z * z = x * z * (x* z) * y)%R.
                      intros.
                      psatz R.
                    Qed.
                    intros.
                    rewrite multSimpl6 in H3.
                    Lemma plusSimpl : forall x y, (x + y = y + x)%R.
                      intros.
                      psatz R.
                    Qed.
                    intros.
                    rewrite plusSimpl.
                    apply H3.
                    apply H.
                  Qed.
                  pose proof sqrt_Rsqr_abs.
                  rewrite H4 in H0.
                  
                  specialize (translate2 theta ay ax  n0).
                  intros.
                  rewrite H6 in H0.
                  pose proof Rtrigo1.sin2_cos2.
                  specialize (H7 theta ).
                  unfold Rsqr in H7.                
                  rewrite H7 in H0.
                  rewrite RIneq.Rmult_1_r in H0.
                  specialize (H5 (ax */ cos theta)%R).
                  unfold Rsqr in H5.
                  rewrite H5 in H0.
                  revert H0. intros.
                  unfold Rbasic_fun.Rabs in H0.
                  destruct Rbasic_fun.Rcase_abs.
                  Lemma simplMod : forall x y,  (x = -y -> -x = y)%R.
                    intros.
                    psatz R.
                  Qed.
                  intros.
                  apply simplMod in H0.
                  
                  pose proof translate3.
                  specialize (H8 (-a)%R ax  (cos theta) H0 n0).
                  constructor 2.
                  apply H8.
                  pose proof translate3.
                  specialize (H8 a ax (cos theta) H0 n0).
                  constructor 1.
                  apply H8.
              }
            }
          }
          {
            admit.
          }
          Qed.
        intros.
        unfold is_solution in *.
        unfold solves_diffeqs in *.
        revert H6.
        intros.
        remember ((["vx" '  ::= "a" * cos("theta"),
                        "vy" '  ::= "a" * sin("theta"), 
                        "a" '  ::= 0, "theta" '  ::= 0])%HP) as diffEqList.
        pose proof unchanged_continuous_aux as unchanged_vars.
        specialize (unchanged_vars diffEqList).
        simpl in unchanged_vars.
        assert (miniMainPremise := H6).
        unfold tlaEntails in unchanged_vars.
        simpl in unchanged_vars.
        specialize (unchanged_vars tr I).
        revert mainPremise.
        intros.
        unfold is_solution in unchanged_vars.
        unfold eval_comp in unchanged_vars.
        simpl in unchanged_vars.
        unfold solves_diffeqs in unchanged_vars.
        rewrite HeqdiffEqList in unchanged_vars.
        unfold Semantics.eval_formula in unchanged_vars.
        simpl in unchanged_vars.
        unfold eval_comp in unchanged_vars.
        simpl in unchanged_vars.
        rewrite HeqdiffEqList in mainPremise.
        rewrite Heqvx in *.
        rewrite Heqvy in *.
        rewrite Heqa in *.
        rewrite Heqtheta in *.
        specialize (unchanged_vars mainPremise).
        



        simpl in unchanged_vars.
        unfold Semantics.eval_formula in unchanged_vars.
        

        destruct H6.     
        exists x1.
        
        intros.
        simpl in *.
        destruct H15.
        {
          inversion H15.
          rewrite HeqdiffEqList in H6.
          specialize (H6 "vx" ("a" * cos("theta"))%HP st).          
          simpl in H6.
          Lemma inList1 : List.In ("vx" ' ::= ("a"*cos("theta"))%HP)%HP (["vx" '  ::= "a" * cos("theta"),
                                                                          "vy" '  ::= "a" * sin("theta"), "a" '  ::= 0,
                                                                          "theta" '  ::= 0])%HP.
            intros.
            simpl.
            intuition.
          Qed.
          intros.
          specialize (H6 inList1).
          rewrite H6.
          simpl.
          Lemma subProof2 : forall (ax ay a theta:R), (a > 0 -> a = sqrt (ax*ax + ay*ay) -> 
                                                      theta  = atan (ay/ax) -> 
                                                      (ax = a * cos theta) /\ ay = a * sin theta)%R.
          admit.
          Qed.
          pose proof subProof2 as subProof.
          specialize (subProof (x0 z "ax") (x0 z "ay") (x0 z "a") (x0 z "theta")).
          SearchAbout Ranalysis1.derive_pt.
          assert (mainPremise2 := mainPremise).
          assert (miniMainPremise2 := miniMainPremise).
          revert miniMainPremise.
         
          intros.
          destruct miniMainPremise.
          rewrite HeqdiffEqList in H18.
          specialize (H18 "a" 0 st).
           Lemma inList2 : List.In ("a" ' ::= 0)%HP (["vx" '  ::= "a" * cos("theta"),
                                                                          "vy" '  ::= "a" * sin("theta"), "a" '  ::= 0,
                                                                          "theta" '  ::= 0])%HP.
            intros.
            simpl.
            intuition.
          Qed.
           intros.
           specialize (H18 inList2).
           
           simpl in H18.
           Lemma nullDerivativeProof : forall x0 var z x (x3 :  forall x3 : Var, Ranalysis1.derivable (fun t : R => x0 t x3)),  
        (0 <= z <= x)%R ->
        (forall z0, (R0<=z0<=x)%R -> Ranalysis1.derive (fun t : R => x0 t var) (x3 var) z0 = 0%R) -> x0 z var=x0 R0 var. 
             intros.
             pose proof MVT.null_derivative_loc as nullDerivative.
             specialize (nullDerivative (fun t : R => x0 t var) R0 x).           
             unfold Ranalysis1.derivable in x3.
           Lemma derivableSimple : forall x0  x (var:Var), (forall x4, Ranalysis1.derivable_pt (fun t : R => x0 t var ) x4) -> 
                                               forall x4 : R,
                          (0 < x4 < x)%R ->
                          Ranalysis1.derivable_pt (fun t : R => x0 t var) x4.  
             intros.
             specialize (H x4).
             apply H.
           Qed.
           intros.
           pose proof derivableSimple.
           specialize (H1 x0 x).
           assert (derivableProof := x3).
           specialize (derivableProof var).
           specialize (H1 var derivableProof).
           specialize (nullDerivative H1).
           
           Check Ranalysis1.derivable_pt.
           Check Ranalysis1.derive_pt.
           
           Lemma derivableSimple2 : forall x0  x (var:Var), (forall x4, Ranalysis1.derivable_pt (fun t : R => x0 t var ) x4) -> 
                                               forall x4 : R,
                          (0 <= x4 <= x)%R ->
                          Ranalysis1.continuity_pt (fun t : R => x0 t var) x4.  
             intros.
             specialize (H x4).
             apply Ranalysis1.derivable_continuous_pt.
             
             apply H.
           Qed.
           pose proof derivableSimple2.
           specialize (H2 x0 x var derivableProof).
           specialize (nullDerivative H2).
           unfold Ranalysis1.derive in H0.
           
           
           Lemma derivableSimple3 : forall (x:R) var
                                           x0
                                           (H21:forall x4 : R,(0 < x4 < x)%R -> Ranalysis1.derivable_pt (fun t : R => x0 t var) x4) 
                                           (x3 :forall (x3 : Var) (x4 : R), Ranalysis1.derivable_pt (fun t : R => x0 t x3) x4),
               (forall z0 : R,
                   (0 <= z0 <= x)%R ->
                   Ranalysis1.derive_pt (fun t : R => x0 t var) z0 (x3 var z0) = 0%R) ->  (forall (x4 : R) (P : (0 < x4 < x)%R),
                                                                                              Ranalysis1.derive_pt (fun t : R => x0 t var) x4
                                                                                                                   (H21 x4 P) = 0%R).
             intros.
             SearchAbout (Ranalysis1.derive_pt _ _ _ = Ranalysis1.derive_pt _ _ _).
             rewrite Ranalysis1.pr_nu with (pr2 := x3 var x4).
             assert (x3Copy := x3).
             specialize (x3Copy var x4).
             specialize (H x4).
             Lemma simpl : forall x1 x, (0 < x1 < x)%R -> (0 <= x1 <=x)%R.
               intros.
               psatz R.
             Qed.
             intros.
             apply simpl in P.
             specialize (H P).
             intuition.
           Qed.
           intros.
           pose proof derivableSimple3.
           specialize (H3 x var x0 H1 x3 H0). 
           
           specialize (nullDerivative H3).
           unfold Ranalysis1.constant_D_eq in *.
           
           specialize (nullDerivative z H).
           intuition.
           Qed.
           intros.
           pose proof nullDerivativeProof.
           specialize (H21 x0 "a" z x x3 H17 H18).
           
           revert miniMainPremise2.
           intros.
           destruct miniMainPremise2.
           rewrite  HeqdiffEqList in H22.
           specialize (H22 "theta" 0 st).
            Lemma inList3 : List.In ("theta" ' ::= 0)%HP (["vx" '  ::= "a" * cos("theta"), "vy" '  ::= "a" * sin("theta"), "a" '  ::= 0, "theta" '  ::= 0])%HP.
             
              intuition.
              
            Qed.
            intros.
            specialize (H22 inList3).
            simpl in H22.
            pose proof nullDerivativeProof.
            specialize (H23 x0 "theta" z x x4 H17 ).
            specialize (H23 H22).
            clear H22 x4 x3 H18.
            revert H2. 
            revert H0.
            revert H1.
            revert H9.
            revert H10.
            intros.
            rewrite <- H21 in H9. 
            rewrite H9 in H0.
            rewrite <- H23 in H10. 
            rewrite H10 in H1. 
            rewrite H9 in H2.
            rewrite Heqax in H0.
            rewrite Heqay in H0.
            rewrite Heqay in H1.
            rewrite Heqax in H1.
            assert (H1copy := H1).
            assert (H0copy := H0).
            rewrite H23 in H1copy. 
            rewrite H21 in H0copy.
            
            Lemma simpl2 : forall x0 z tr, 
                x0 0 "a" = sqrt (Stream.hd tr "ax" * Stream.hd tr "ax" + Stream.hd tr "ay" * Stream.hd tr "ay") 
                /\   x0 0%R "theta" = atan (Stream.hd tr "ay" * / Stream.hd tr "ax")
                /\   x0 z "a" = x0 0%R "a" /\ x0 z "theta" = x0 0%R "theta" 
                /\   
                   

            
            specialize (subProof H2 ).
            intros.
            revert 

           destruct mainPremise2.
           destruct H23.
           destruct H23.
           decompose [and] H24.
           destruct H25.
           specialize (H25 "theta" 0 st).1
           
           pose proof.

           specialize (H22 x0 "theta"  z x x3 H17 H18).

            unfold Ranalysis1.derivable in x3.
           specialize (H21 x "a" x0 ).
          
           
           rewrite <- H9 in nullDerivative.
           rewrite <- nullDerivative in H2.
           specialize (subProof H2).

           eapply derivableSimple3 in H18.
           
             rewrite Ranalysis1.pr_nu with (pr2 := x3Copy).
             
             Check Ranalysis1.derive_pt.
           
           
            Lemma derivableSimple3 : forall x0 
                                            (x:R) 
                                            (H21:forall x4 : R, (0 < x4 < x)%R -> Ranalysis1.derivable_pt (fun t : R => x0 t "a") x4)
                                            (x3 : (forall (x3 : Var) (x4 : R), Ranalysis1.derivable_pt (fun t : R => x0 t x3) x4)), 
               (forall (z0:R),
               (0 <= z0 <= x)%R ->
               Ranalysis1.derive_pt (fun t : R => x0 t "a") z0 (x3 "a" z0) = 0%R) ->
               
              (forall (x4 : R) (P : (0 < x4 < x)%R),
                    Ranalysis1.derive_pt (fun t : R => x0 t "a") x4
                      (H21 x4 P) = 0%R).
              intros.
              intuition.
              assert (x3Copy := x3).
              specialize (x3Copy "a" x4).
              assert (H21Copy := H21).
              specialize (H21Copy x4 P).
              SearchAbout Ranalysis1.derivable_pt.
              SearchAbout (Ranalysis1.derivable_pt _ _  ).

              unfold Ranalysis1.derivable_pt in *.
              Print Ranalysis1.derivable_pt.
              Lemma simpl : forall x4 , let Ranalysis1.derivable_pt
              Print .
              Check Ranalysis1.derivable_pt_abs.
              

              unfold Ranalysis1.derivable_pt_abs in *.
              

              Print Ranalysis1.derive_pt.
              unfold Ranalysis1.derive_pt in *.
              unfold proj1_sig in *.
              SearchAbout Ranalysis1.derivable_pt.
              specialize (H x4).
              rewrite <- H.
              
              unfold Ranalysis1.derivable_pt in *.
              Check Ranalysis1.derivable_pt_abs.
              unfold Ranalysis1.derivable_pt_abs in *.
              unfold Ranalysis1.derivable_pt_lim in *.
              
              Print nat.
              
              remember (H21 x4 P).
              assert (newH21 := H21).
              
              specialize (newH21 x4 P).
              
              rewrite Heqd0.
              Check Ranalysis1.derivable_pt (fun t : R => x0 t "a") x4.
              
              Lemma simpl3 : forall x4 x x0 (P:(0<x4<x)%R) (H21:forall x4 : R,
        (0 < x4 < x)%R -> Ranalysis1.derivable_pt (fun t : R => x0 t "a") x4) (newH21: Ranalysis1.derivable_pt (fun t : R => x0 t "a") x4), 4.                
                intros.
                
                simpl in *.
                dependent inversion. 
                destruct H21.
              intuition.
              
              SearchAbout Ranalysis1.derive_pt.
              
              unfold Ranalysis1.derive_pt in *.
              unfold proj1_sig in *.
              Check Ranalysis1.derivable_pt.
              admit.
            Qed.
              intros.
              specialize (derivableSimple3 x0 x).
              intros.
              specialize (H23 H21 x3).
              Check Rle_dec.
              SearchAbout ({_}+{_})%R.
              destruct (Rlt_dec 0  z).
              destruct (Rlt_dec z x).
              Lemma simpl : forall x z, ((0 < z) -> (z < x) -> (0<z<x))%R.
                intros.
                psatz R.
              Qed.
              intros.
              specialize (simpl x z r r0).
              intros.
              Lemma simpl2 :  forall x (x4:R) x0 (H21:forall x4 : R,
        (0 < x4 < x)%R -> Ranalysis1.derivable_pt (fun t : R => x0 t "a") x4),((forall (x4 : R) (P : (0 < x4 < x)%R),
                    Ranalysis1.derive_pt (fun t : R => x0 t "a") x4
                      (H21 x4 P) = 0%R)) = True.

              intros.
              Admitted.
              rewrite simpl2 in nullDerivative.
              specialize (nullDerivative I).
              unfold Ranalysis1.constant_D_eq in *.
              
              
              specialize (simpl2 z x0 x x3).
              specialize (nullDerivative z H24 ).

              specialize (H23 H18 H17).
              
              unfold Ranalysis1.derivable_pt in *.
              unfold Ranalysis1.derivable_pt_abs in *.
              unfold Ranalysis1.derivable_pt_lim in *.
              SearchAbout proj1_sig.
              simpl.
              simpl.
 
           specialize (nullDerivative H18).
           apply derivableSimple in x3.
             apply 
               
             specialize (nullDerivative(fun t : R => x0 t "a") (x3 "a")).
           unfold Ranalysis1.derive in H18.
           SearchAbout Ranalysis1.derive_pt.
           specialize (nullDerivative ).
           apply H18 in nullDerivative.

           apply nullDerivative in H18.

          specialize (miniMainPremise ).
          specialize (miniMainPremise x1).
          
          apply subProof.
          
          Lemma derivZeroImp : forall x2 x3,
              (forall x1 : Var, Ranalysis1.derivable (fun t : R => x3 t x1)) ->
                  (exists
                     is_derivable : forall x4 : Var,
                                    Ranalysis1.derivable
                                      (fun t : R => x3 t x4),
                     forall (x4 : Var) (d0 : Term) (st0 : state),
                     ("vx" '  ::= "a" * cos("theta"))%HP = (x4 '  ::= d0)%HP \/
                     ("vy" '  ::= "a" * sin("theta"))%HP = (x4 '  ::= d0)%HP \/
                     ("a" '  ::= 0)%HP = (x4 '  ::= d0)%HP \/
                     ("theta" '  ::= 0)%HP = (x4 '  ::= d0)%HP \/ False ->
                     forall z : R,
                     (0 <= z <= x2)%R ->
                     x3 z "a" x3 
                  ->
          .
            intros.
            exists H.
            intros.
            
            
          specialize (subProof ).

          unchanged_continuous_aux).
        destruct H6.
        exists x1.
        
        intros.
        simpl in H15.
        
        destruct H15.
        inversion H15.
        pose proof Ranalysis1.derive_pt_mult as deriveMult.
        
        assert (premise1 := H6).
        assert (premise2 := H6).
        clear H6.
        specialize (premise1 "vx" ("a" * cos("theta"))%HP st).
        
        
        
        
      
        intros.
        specialize (premise1 inList1).
        rewrite premise1.
        pose proof subProof as subProof.
        specialize (subProof (x0 z "ax") (x0 z "ay") (x0 z "a") (x0 z "theta")).
        specialize (H2 (Stream.Cons (x0 z) tr)).
        specialize (H0  (Stream.Cons (x0 z) tr)).
        specialize (H1 (Stream.Cons (x0 z) tr)).
        specialize (subProof H2 H0 H1).
        simpl.
        


        specialize (subProof H0).
        specialize (premise2 inList2).
        pose proof subProof as subProof.
        specialize (subProof (x0 z "ax") (x0 z "ay") (x0 z "a") (x0 z "theta")).
        revert H2. intros.
        Check unchanged_continuous_aux.
        pose proof unchanged_continuous_aux as unchanged_vars.
        remember (["vx" '  ::= "a" * cos("theta"),
                "vy" '  ::= "a" * sin("theta"), "a" '  ::= 0,
                "theta" '  ::= 0])%HP as diffEq.
        specialize (unchanged_vars diffEq).
        simpl in unchanged_vars.
        unfold tlaEntails in unchanged_vars.
        simpl in unchanged_vars.
        specialize (unchanged_vars (Stream.Cons (Stream.hd tr) (Stream.Cons (x0 z) tr))).
        

        rewrite HeqdiffEq in unchanged_vars.
        specialize (unchanged_vars I).
        simpl in unchanged_vars.
        
        unfold Semantics.eval_formula in unchanged_vars.
simpl in unchanged_vars.

        specialize (subProof ).
        remember (["vx" '  ::= "a" * cos("theta"),
                "vy" '  ::= "a" * sin("theta"), "a" '  ::= 0,
                "theta" '  ::= 0])%HP as diffEqList.
        revert mainPremise.
        intros.
        unfold is_solution in *.
        unfold solves_diffeqs in *.
        unfold eval_comp in unchanged_vars.
        simpl in unchanged_vars.
        simpl in unchanged_vars.
        rewrite  Heqvx in mainPremise.
        rewrite Heqvy in mainPremise.
        rewrite Heqa in mainPremise.
        rewrite Heqtheta in mainPremise.
        rewrite HeqdiffEq in mainPremise.
        specialize (H2 (Stream.Cons (x0 z) tr)).
        specialize (H0  (Stream.Cons (x0 z) tr)).
        specialize (H1 (Stream.Cons (x0 z) tr)).
        simpl in *.
        specialize (subProof H2 H0 H1).
        decompose [and] subProof. 
        destruct H6.
        {
          
        }

        specialize (unchanged_vars mainPremise).
        
        

        specialize (unchanged_vars diffEqList).
        simpl in unchanged_vars.
        unfold tlaEntails in unchanged_vars.
        rewrite HeqdiffEqList in unchanged_vars.
        specialize (unchanged_vars tr).
        simpl in unchanged_vars.
        destruct. 
        unfold Semantics.eval_formula in unchanged_vars.
        simpl in unchanged_vars.

        pose proof subProof as subProof.
        
        Print Ranalysis1.mult_fct.
        Check Ranalysis1.derivable_pt_mult.
        
        specialize (subProof (x0 z "ax") (x0 z "ay") (x0 z "a") (x0 z "theta")).
        Print Unchanged.
        specialize (unchanged_continuous_aux)
        apply unchanged_continuous_aux in premise1. 
        SearchAbout unchanged_vars.


        simpl in *.
       
        
        apply premise1.

        admit.
        
        admit.
        admit.
        inversion H15. 
        rewrite Heqax in subProof.
        
        rewrite Heq.
        specialize (H6 x2 "ax" st).
        simpl in H6.
        rewrite <-H20 in H6.
        simpl.
        
        apply H6.
        
        

        simpl.
        
        rewrite H21 in H6.
        


        specialize (H6 x2 d0 st).
        simpl in H6.
        
        
        


        apply H6.
        simpl in *.
        destruct H17.
        inversion H17.
        rewrite H20.
        rewrite H21.
        revert H15.
        intros.
        destruct H15.
        

        simpl in *.
       
        destruct H17.
        constructor 1.
        revert H15.
        intros.
        decompose [and] H15.
        destruct H17.
        revert H17.
        intros.
        rewrite Heqax in H17.
        rewrite Heqa in H17.
        rewrite Heqtheta in H17.
        rewrite H18.        

        rewrite <- H17.                                         
        
        Set Printing All.
        
        rewrite <- H17.
        admit.
       
        Set Printing All.
        admit.
        auto.
        simpl in H17.
        destruct H17.
        Local Open Scope HP_scope.
        specialize (H6 "vx" ("a" * cos("theta")) (Stream.hd tr)).
        simpl in H6.
        
        
        
        Lemma simpl : forall (x2:Var) (d0:Term), ("vx" '  ::= "ax")%HP = (x2 '  ::= d0)%HP -> x2 = "vx".
          intros.
          SearchAbout (DiffEqC _ _).
          reflexivity.
        Set Printing All.
     
        specialize (H6 "vx" (MultT "a" ( CosT ("theta"))) (Stream.hd tr)).
        revert H6.
        intros.
        simpl in *.
        Local Open Scope HP_scope.
        
        
        intros.
        rewrite  simpl1 in H6.

          reflexivity.
        simpl in H6.
        
        exists x1.
        intros.
        simpl in *.
        specialize (H6 x2 d0 st).
        revert H6.
        intros.
        destruct H17.
        

        
        Lemma orProof : forall (x1 x2 x3 x4 x5:Prop), x1 -> (x1 \/ x2 \/ x3 \/ x4 \/ x5).
          intros.
          intuition.
        Qed.
        
        intros.
        decompose [and] H15.
        {
          destruct H19.
          {
            
            assert (derivableAssert := x1).
            specialize (derivableAssert).
            unfold Ranalysis1.derivable in derivableAssert.
            SearchAbout Ranalysis1.derivable_pt. 
            pose proof Ranalysis1.derivable_derive.
            specialize (derivableAssert x2 z).
            specialize (H21 (fun t : R => x0 t x2) z).
            specialize (H21 derivableAssert).
            unfold Ranalysis1.derive.
            destruct H21.
            rewrite <- H17 in H6. 
            rewrite Heqax in H19. 
            rewrite Heqa in H19.
            rewrite Heqtheta in H19.
            SearchAbout CosT.
            simpl in H19.
            destruct H21.
            Set Printing All.
            rewrite H19 in H6. 
            specialize ()
            Print Ranalysis1.derive
            unfold Ranalysis1.derivable_pt in derivableAssert.
            unfold Ranalysis1.derivable_pt_abs in derivableAssert.
            unfold Ranalysis1.derivable_pt_lim in derivableAssert.
            unfold Ranalysis1.derive.
            unfold Ranalysis1.derive_pt.
            
            specialize (x1 "ax").
            Print DiffEq.
            
            Set Printing All.
           
            Print DiffEq.
            unfold DiffEqC in H17.
          }
        }
        destruct H4.
        specialize (orProof ).
        Print List.In.

        SearchAbout solves_diffeqs.
        
        SearchAbout is_solution.
        rewrite <- Rtrigo1.sin2_cos2 in H0.
                rewrite H5 in H1.
                pose proof Rtrigo1.sin2_cos2.
                specialize (H7 theta).
                unfold Rsqr in H7.
                rewrite H7 in H1.
                rewrite RIneq.Rmult_1_r in H1.
                pose proof sqrt_square.
                assert (sqrtPos := H).
                pose proof sqrt_lt_0_alt.
                rewrite H1 in sqrtPos.
                pose proof sqrt_0.
                
                specialize (H9 R0 (ax * / cos theta * (ax * / cos theta))%R).
                rewrite H10 in H9.
                apply Rgt_lt in sqrtPos.
                specialize (H9 sqrtPos).
                

                SearchAbout ((_>_)%R -> (_<_)%R).
                
                pose proof sqrt_le_1_alt.
                
                SearchAbout  (forall x, (0 <= x)%R -> sqrt _ =  _).
                SearchAbout sqrt.
                pose proof sqrt_Rsqr_abs.
                unfold Rsqr in H12.
                specialize (H12 (ax */ cos theta)%R).
                unfold Rbasic_fun.Rabs in H12.
                destruct Rbasic_fun.Rcase_abs. 
                {
                  
                }
                Set Printing All.

                rewrite sqrt_square in H1.
                Close Scope HP_scope.
                Lemma translate3 : forall (x y z:R), (x = y */ z)%R -> (z <> 0)%R -> (y = x * z)%R.
                Proof. 
                  intros.
                  pose proof Rmult_eq_compat_r.
                  specialize (H1 z x (y */ z)%R H).
                  pose proof Rinv_l_sym.
                  specialize (H2 z H0).
                  SearchAbout Rmult.
                  SearchAbout ((_ * _ * _)= (_ * (_ * _)))%R.
                  rewrite Rmult_assoc in H1.
                  rewrite <- H2 in H1.
                  rewrite RIneq.Rmult_1_r in H1.
                  pose proof eq_sym.
                  apply eq_sym.
                  apply H1.
                Qed.
                intros.
                specialize (translate3 a ax (cos theta) H1 n0).
                intros.
                apply H12.
                
                
                  rewrite eq_sym in H1.
                  SearchAbout (forall x y,(x=y)%R -> (y=x)%R)%R.
                  
                  pose proof Rmult_eq_reg_r.    
                  SearchAbout Rmult.

                pose proof RIneq.Rmult_1_r.

                Set Printing All.
                rewrite Rtrigo1.sin2_cos2 in H1.
                
                Set Printing All.
               
                rewrite  H6 in H1.
            
              
            }

               
                Lemma Rmult_le_algebra : forall r1 r2 r3,
                    (r2 > 0 -> r1 <= r2*r3 -> r1 * (/r2) <= r3)%R.
                Proof. 
                  intros. 
                  pose proof Rmult_le_reg_r.
                  apply (Rmult_le_reg_r r2); solve_linear.
                  rewrite Rmult_assoc.
                  rewrite <- Rinv_l_sym; solve_linear.
                Qed.
                intros.
                SearchAbout Rtrigo1.tan.
                pose proof Rmult_le_reg_r.
                pose proof Rinv_l_sym.
                
                contradict H2.
                pose proof Rtrigo1.SIN_bound.
                specialize (H2 theta).
                
                z3 solve_dbg.
                SearchAbout (_*/0)%R.
                Lemma zeroProof : forall (a b c:R), c = R0 -> a = R0 ->(a / b)%R = (c / b)%R.
                  intros.
                  
                  SearchAbout cos.
                destruct  (RiemannInt.Req_EM_T ay 0).
                {
                  subst.
                  
                  SearchAbout (sqrt).
                  pose proof sqrt_0.
                  Lemma simplifyZero : (0 * 0 + 0 * 0)%R = R0.
                    psatz R.
                  Qed.
                  intros.
                  rewrite simplifyZero.
                  rewrite H1.
                  pose proof Rtrigo1.COS_bound.
                  specialize (H5 theta).
                  SearchAbout (_ * 0)%R.
                  Lemma simplifyZero2 : forall r, (0 * r)%R = 0%R.
                    intros.
                    psatz R.
                  Qed.
                  intros.
                  rewrite simplifyZero2.
                  reflexivity.
                }
                {
                  rewrite e in H1.
                  pose proof Rtrigo1.SIN_bound.
                  specialize (H5 theta).
                  
                  Lemma simple : forall (a b c:R), (a / b)%R = (c / 0)%R.
                  Proof.
                    intros.
                    clear d_gt_0.
                    psatz R.
                }
                    
                  psatz R.
                }
              }
              
                SearchAbout (cos).
              }
              
              destruct (Rle_dec theta 0). 
              

              SearchAbout (Rtrigo1.tan).
              
              SearchAbout (cos).              
              subst.
              
              Lemma  zeroProof1 : forall (x y z:R), (x/y)%R = (z/0)%R -> y%R=R0.
              Proof.
                intros.
                SearchAbout (_*/R0)%R.
                SearchAbout (_/_)%R.
                SearchAbout (/0)%R.
                Require Import QArith.
                Check Qeq.
                remember (/ 0)%R.
                SearchAbout Rinv.
                Print Rtrigo1.tan.
                SearchAbout (_/_)%R.
                Check Rtrigo1.tan. 
                rewrite <- Heqr in H.
                unfold Qeq in *.
                Lemma inv_zero_is_zero: (/ 0) == 0. 
                Proof. unfold Qeq. reflexivity. Qed.
              Qed.
              intros.
              
              SearchAbout (_ */ _)%R.
            }
            specialize (H6 theta ay ax H H4).
            rewrite H6 in H3.
            Lemma translate2 : forall (theta ay ax :R), ((cos theta <> 0) -> (ax * ax + ax * sin theta /cos theta * (ax * sin theta /cos theta)) =  (ax */ cos theta) * (ax */ cos theta ) * (  sin theta * sin theta + cos theta * cos theta))%R.
            Proof.
              intros.
            Admitted.
            intros.
            pose proof translate2. 
            specialize (H7 theta ay ax H2).
            rewrite H7 in H3.
            SearchAbout cos.
            pose proof Rtrigo1.sin2_cos2.
            unfold RIneq.Rsqr in *.
            specialize (H8 theta).
            rewrite H8 in H3.
            SearchAbout sqrt. 
            pose proof sqrt_square.          
            specialize (H9 (ax * / cos theta)%R H0).
            SearchAbout Rmult.
            pose proof RIneq.Rmult_1_r.
            specialize (H10 (ax * / cos theta * (ax * / cos theta))%R).
            rewrite H10 in H3.
            rewrite H9 in H3.
            Lemma translate3 : forall a ax theta, a = (ax * / cos theta)%R -> ax = (a * cos theta)%R. 
              intros. 
            Admitted.
            intros.
            apply translate3 in H3.
            apply H3.
          }
          {
            intros.
            apply tanInv in H4.
            pose proof Rtrigo1.sin2_cos2.
            unfold Rtrigo1.tan in *.
            Lemma translate4 : forall (theta ay ax:R), (ax <> 0 -> sin theta / cos theta = ay / ax -> ax = (ay * cos theta)/ sin theta)%R. 
              intros. 
              Require Import Coq.micromega.Psatz.
              clear d_gt_0.
              remember (sin theta) as sin.
              remember (cos theta) as cos.
              clear Heqsin.
              clear Heqcos.
              SearchAbout Rinv.
              pose proof RIneq.Rinv_mult_simpl.
            Admitted.
            pose proof translate4.
            specialize (H6 theta ay ax H H4).
            rewrite H6 in H3.
            Lemma translate5 : forall (theta ay ax :R), ((cos theta <> 0) -> (ay * cos theta / sin theta * (ay * cos theta / sin theta) + ay * ay) =  (ay */ sin theta) * (ay */ sin theta ) * (  sin theta * sin theta + cos theta * cos theta))%R.
              intros.
            Admitted.
            intros.
            pose proof translate5.
            specialize (H7 theta ay ax H2).
            rewrite H7 in H3.
            pose proof Rtrigo1.sin2_cos2.
            unfold RIneq.Rsqr in *.
            rewrite H8 in H3.
            rewrite  RIneq.Rmult_1_r in H3.
            pose proof sqrt_square.
            specialize (H9 ( ay * / sin theta)%R H1).
            rewrite H9 in H3.
            Lemma translate6 : forall a ay theta, a = (ay * / sin theta)%R -> ay = (a * sin theta)%R. 
              intros. 
            Admitted.
            intros.
            apply translate6 in H3.
            apply H3. 
            
          }
          Qed.
        intros.
        pose proof subProof.
        
            
      }
    }


    Print Continuous.
    exists d.
    specialize (H3 d).
    Print is_solution.
    Print solves_diffeqs.
    
    Print eval_term.
    

    Print Ranalysis1.derive.
    Print Ranalysis1.derivable. 
    Print Ranalysis1.derivable_pt.
    Print Ranalysis1.derivable_pt_abs.

  Definition Ctrl : Formula :=
       ("A"*d + "Vmax" <= ub //\\ "a"! = "A")
    \\// ("a"! <= 0).

  Definition I : Formula :=
    "v" <= ub //\\ "v" + "a"*d <= ub //\\
    0 <= "t" <= d //\\ "Vmax" >= "v".

  Definition Safe : Formula :=
    "v" <= ub.

  Definition Con

  Definition Evolve : Formula :=
    Continuous (["h"' ::= "v",
                 "v"' ::= 0,
                 "t"' ::= 1,
                 "H"' ::= 0,
                 "TC"' ::= 0,
                 "TR"' ::= 0]).


  Definition IndInv : Formula :=
       ("a" <  0 -->> Safe)
    //\\ ("a" >= 0 -->> "a"*"t" + "v" <= ub).

  Variable WC : Formula.

  Definition SpecR : SysRec :=
    {| dvars := ("a"::nil);
       cvars := ("v"::nil);
       Init := I;
       Prog := Ctrl;
       world := w;
       WConstraint := WC;
       maxTime := d |}.

  Definition Spec := SysD SpecR.

  Theorem ctrl_safe :
    []"Vmax" >= "v" |-- Spec -->> []"v" <= ub.
  Proof.
    tlaIntro.
    eapply Sys_by_induction
    with (IndInv:=IndInv) (A:="Vmax" >= "v").
    - tlaIntuition.
    - unfold Spec, SpecR. tlaAssume.
    - solve_nonlinear.
    - tlaIntuition.
    - solve_nonlinear.
    - unfold InvariantUnder. solve_linear.
      rewrite_next_st. solve_linear.
    - eapply diff_ind with (Hyps:=TRUE).
      + tlaIntuition.
      + tlaIntuition.
      + unfold World. tlaAssume.
      + tlaIntuition.
      + tlaAssume.
      + tlaIntuition.
      + repeat tlaSplit;
        try solve [solve_linear |
                   tlaIntro; eapply unchanged_continuous;
                     [ tlaAssume | solve_linear ] ].
    - solve_nonlinear.
  Qed.

End VelCtrl.

Close Scope HP_scope.
Close Scope string_scope.