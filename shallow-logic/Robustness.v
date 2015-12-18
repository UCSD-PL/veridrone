Require Import Coq.Reals.Rdefinitions.
Require Import ExtLib.Data.Fun.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Require Import ExtLib.Structures.Applicative.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import ChargeTactics.Tactics.
Require Import SLogic.Logic.
Require Import SLogic.LTLNotation.
Require Import SLogic.Instances.
Require Import SLogic.BasicProofRules.
Require Import SLogic.Tactics.
Require Import SLogic.BoundingFunctions.

Section Robustness.

  Variable state : Type.
  (* Input cost - this quantifies the disturbance. *)
  Variable IC : StateVal state R.
  (* Output cost - this quantifies the deviation
     from the nominal behavior. *)
  Variable OC : StateVal state R.
  (* The StateVal tracking time. *)
  Variable t : StateVal state R.
  
  Record disturbance : Type :=
    { d : R;
      td : R }.

  Record dist_state : Type :=
  { ds : list disturbance }.

  Local Open Scope LTL_scope.

  Definition dist (gamma : R -> R)
    : StateVal state disturbance :=
    `Build_disturbance (`gamma (`Rabs IC)) t.

  Definition init_dist (gamma : R -> R)
    : StateProp (dist_state * state) :=
    (fst#ds) `= snd#(dist gamma) `:: pure List.nil.

  Definition acc_dist (gamma : R -> R)
    : ActionProp (dist_state * state) :=
    (fst#ds)! `= (snd#(dist gamma))! `:: !fst#ds.

  Definition max_R : list R -> R :=
    fold_right Rmax 0%R.

  Definition flip {A B C} (f : A -> StateVal B C)
    : StateVal B (A -> C) :=
    fun b a => f a b.

  Definition bounded (mu : R -> R -> R) (rho : R)
    : StateProp (dist_state * state) :=
    snd#OC `<=
    `max_R
    (lift2 (@map disturbance R)
           (flip (fun p =>
                    (`mu (pure p.(d))
                      (snd#t `- (pure p.(td)))%R)))
           fst#ds)
    `+ `rho.

  (* The bounds on the functions (K, KL, KLD) are
     meaningless unless the time [StateVal] is
     reasonable. *)
  Definition sensible_time : TraceProp state :=
    [`R0 `<= !t] //\\ [][!t `<= t!].

  Definition mu_gamma_rho_robust
             ( mu : R -> R -> R) (gamma : R -> R) (rho : R)
    : TraceProp (dist_state * state) :=
    [!(init_dist gamma)] //\\
    [][acc_dist gamma //\\ !(bounded mu rho)].
    

  (* This is the definition of robustness from the
     Tabuada paper. The property sensible_time
     appear explicitly in our definition of [robust],
     while in the Tabuada paper, this appear in the
     model of cyber-physical systems. *)
  Definition robust : TraceProp state :=
    sensible_time //\\
    Exists gamma : R -> R,   embed (K_fun gamma) //\\
    Exists mu : R -> R -> R, embed (KLD_fun mu)  //\\
    Exists rho : R,          embed (0 <= rho)%R  //\\
      TExists dist_state ,
         mu_gamma_rho_robust mu gamma rho.

  (* Now we write a definition of robustness that is
     equivalent to the Tabuada one, but easier to
     work with. *)

  (* For the equivalent definition of robustness,
     we only need to store a single pair of disturbance
     and time rather than a list of pairs. *)

  Definition dist2 (mu : R -> R -> R) (gamma : R -> R)
    : StateVal state R :=
    `mu (`gamma (`Rabs IC)) `R0.

  Definition init_dist2 (mu : R -> R -> R) (gamma : R -> R)
    : StateProp (disturbance * state) :=
    fst#d `= snd#(dist2 mu gamma) //\\
    fst#td `= snd#t.

  Definition acc_dist2 (mu : R -> R -> R) (gamma : R -> R)
    : ActionProp (disturbance * state) :=
    let prev := `mu (!(fst#d)) (((snd#t)! `- !(snd#t))) in
    let new := snd#(dist2 mu gamma)! in
    (new `<= prev -->>
       ((fst#d)! `= prev //\\ (fst#td)! `= !(fst#td))) //\\
    (prev `< new -->>
       ((fst#d)! `= new //\\ (fst#td)! `= !(snd#t))).

  Definition bounded2 (rho : R)
    : StateProp (disturbance * state) :=
    snd#OC `<= fst#d `+ `rho.

  Definition mu_gamma_rho_robust2
             ( mu : R -> R -> R) (gamma : R -> R) (rho : R)
    : TraceProp (disturbance * state) :=
    [!(init_dist2 mu gamma)] //\\
    [][acc_dist2 mu gamma //\\ !(bounded2 rho)].

  Definition robust2 : TraceProp state :=
    sensible_time //\\
    Exists gamma : R -> R,   embed (K_fun gamma) //\\
    Exists mu : R -> R -> R, embed (KLD_fun mu)  //\\
    Exists rho : R,          embed (0 <= rho)%R  //\\
      TExists disturbance ,
          mu_gamma_rho_robust2 mu gamma rho.

  Definition IndInv (mu : R -> R -> R) (gamma : R -> R)
    : StateProp (list disturbance * disturbance * state) :=
    lift2 List.Forall
      (flip (fun p => pure 0 `<= pure p.(d) //\\
                      pure 0 `<= pure p.(td) //\\
                      pure p.(td) `<= snd#t)%R)
      (snd#(dist gamma) `:: fst#fst) //\\
    fst#snd#d `=
    `max_R
    (lift2 (@map disturbance R)
           (flip (fun p =>
                    (`mu (pure p.(d))
                      (snd#t `- (pure p.(td)))%R)))
           (snd#(dist gamma) `:: fst#fst)).


  Lemma max_R_bound :
    forall b,
      (b <= 0)%R ->
      forall l,
        List.Forall (Rle b) l ->
        (b <= max_R l)%R.
  Proof.
    induction l.
    { auto. }
    { simpl. intros. inversion H0.
      unfold Rmax. destruct_ite; auto. }
  Qed.

  Lemma max_R_strict_increasing :
    forall f,
      strict_increasing_bound f R0 ->
      f R0 = R0 ->
      forall l,
        List.Forall (Rle R0) l ->
        f (max_R l) = max_R (map f l).
  Proof.
    induction l.
    { auto. }
    { simpl in *. intros. inversion H1.
      rewrite <- IHl; auto.
      unfold strict_increasing_bound in H.
      unfold Rmax. repeat destruct_ite; try reflexivity.
      { destruct r.
        { specialize (H a (max_R l)). psatzl R. }
        { subst. reflexivity. } }
      { destruct r; auto.
        specialize (H (max_R l) a).
        apply max_R_bound in H5; psatzl R. } }
  Qed.

  (* TODO: Move *)
  Lemma map_ext_strong :
    forall (A B : Type) (f g : A -> B) (l : list A),
      (forall a : A, List.In a l -> f a = g a) ->
      map f l = map g l.
  Proof.
    induction l.
    { auto. }
    { simpl. intros.
      rewrite H; [ rewrite IHl; [ reflexivity | ] | ].
      { intros. apply H; auto. }
      { auto. } }
  Qed.

  Theorem robust2_robust :
    robust2 |-- robust.
  Proof.
    unfold robust2, robust.
    repeat rewrite landC with (P:=sensible_time).
    repeat (repeat rewrite landexistsD;
            apply lexists_lentails_m; red; intros;
            repeat rewrite landA;
            charge_revert; apply embedPropL; intros;
            charge_intros; charge_split;
            [ apply embedPropR; assumption | ]).
    repeat rewrite landC with (Q:=sensible_time).
    repeat rewrite trace_prop_land_texists.
    match goal with
    |- TExists _ , ?P |-- _ =>
    rewrite (add_history P snd#(dist a))
    end.
    rewrite texists_texists.
    eapply refinement_mapping
    with (f:=fun st => Build_dist_state
                         (List.cons (dist a (snd st))
                                    (fst (fst st)))).
    unfold sensible_time, mu_gamma_rho_robust,
    mu_gamma_rho_robust2. simpl CoFunctor.cofmap.
    rewrite_focusT.
    charge_split; [ charge_assumption | charge_split ].
    { reason_action_tac.
      Local Transparent ILInsts.ILFun_Ops ILInsts.ILPre_Ops.
      unfold focusA, focusS. simpl.
      destruct pre_st as [[pre_hist [pre_d pre_t]] pre_st].
      intros. compute. compute in H6. congruence. }
    { charge_assert ([][!(IndInv a0 a)]).
      { eapply discrete_induction.
        { clear_not_always. repeat rewrite always_and.
          charge_assumption. }
        { reason_action_tac.
          Local Transparent ILInsts.ILFun_Ops
                ILInsts.ILPre_Ops.
          Local Opaque Rabs Rle.
          unfold focusA, focusS. simpl.
          destruct pre_st
            as [[pre_hist [pre_d pre_t]] pre_st].
          destruct post_st
            as [[post_hist [post_d post_t]] post_st].
          unfold pre, IndInv, max_R, init_dist2. simpl.
          intros. rewrite H6. compute. compute in *.
          split.
          { constructor; [ | constructor ].
            split.
            { apply K_fun_pos;
              [assumption | apply Rabs_pos]. }
            { psatzl R. } }
          { destruct H4. rewrite H4.
            rewrite Rplus_opp_r.
            destruct_ite.
            { destruct r; [ | congruence ].
              pose proof (KLD_fun_pos
                            _ H0 (a (Rabs (IC pre_st))) R0)
                as HKLD.
              pose proof (K_fun_pos _ H (Rabs (IC pre_st)))
                as HK.
              pose proof (Rabs_pos (IC pre_st)).
              specialize_arith_hyp HK.
              specialize_arith_hyp HKLD.
              psatzl R. }
            { reflexivity. } } }
        { charge_clear. apply always_tauto.
          rewrite next_starts_pre. repeat rewrite curry.
          repeat rewrite starts_impl. apply starts_tauto.
          unfold focusA, focusS. simpl. intros pre_st post_st.
          destruct pre_st
            as [[pre_hist [pre_d pre_t]] pre_st].
          destruct post_st
            as [[post_hist [post_d post_t]] post_st].
          unfold pre, post. simpl. intros.
          unfold acc_dist2, IndInv, PreFun.compose,
          _liftn, flip, Rmax, pre, post in *.
          split.
          { simpl in *. intuition. subst. inversion H7.
            constructor.
            { split.
              { compute; apply K_fun_pos;
                [assumption | apply Rabs_pos]. }
              { compute in *. psatzl R. } }
            { constructor.
              { compute; split.
                { apply K_fun_pos;
                  [assumption | apply Rabs_pos]. }
                { compute in *; psatzl R. } }
              { eapply Forall_impl. 2: apply H11.
                simpl. intros. psatzl R. } } }
          { cbv beta iota zeta delta
            - [ max_R map KLD_fun K_fun L_fun ] in *.
            intuition.
            assert (0 <= a (Rabs (IC pre_st)))%R
              as Ha.
            { apply K_fun_pos;
              [assumption | apply Rabs_pos]. }
            pose (f:=(fun x =>
                          a0 x
                             (t post_st + - t pre_st)%R)).
            assert (strict_increasing_bound f R0)
              as Hincr.
            { apply KLD_fun_increasing_nonneg; auto;
              psatzl R. }
            assert (f R0 = R0) as HfR0.
            { apply KLD_fun_0; auto; psatzl R. }
            destruct (Rle_dec
                        (dist2 a0 a post_st)
                        (a0 pre_d (t post_st - t pre_st)))%R.
            { intuition. subst.
              pose proof (max_R_strict_increasing f)
                as Hmax_R_f. subst f.
              rewrite Hmax_R_f; auto; rewrite Hmax_R_f in r;
              auto; clear Hmax_R_f.
              { rewrite map_map in *. simpl in *.
                unfold dist2 in *.
                repeat rewrite Rplus_opp_r in *.
                match goal with
                | [ |- _ = Rmax ?e1 ?e2 ] =>
                  rewrite (Rmax_right e1 e2)
                end.
                { f_equal.
                  { unfold KLD_fun in *. intuition.
                    specialize (H4 _ Ha).
                    intuition congruence. }
                  { f_equal. apply map_ext_strong. intros.
                    inversion H7.
                    rewrite Forall_forall in H11.
                    specialize (H11 _ H3). destruct a2.
                    unfold KLD_fun in *. intuition.
                    specialize (H13 d0 H8). intuition.
                    rewrite <- H18; try psatzl R. f_equal.
                    psatzl R. } }
                { cbv beta iota zeta delta
                  - [ max_R Rmax map KLD_fun K_fun L_fun ]
                    in r.
                  eapply Rle_trans; eauto. right.
                  f_equal.
                  { unfold KLD_fun in *. intuition.
                    specialize (H4 _ Ha).
                    intuition congruence. }
                  { f_equal. apply map_ext_strong. intros.
                    inversion H7.
                    rewrite Forall_forall in H11.
                    specialize (H11 _ H3). destruct a2.
                    unfold KLD_fun in *. intuition.
                    specialize (H13 d0 H8). intuition.
                    rewrite <- H18; try psatzl R. f_equal.
                    psatzl R. } } }
              { apply Forall_forall. intros.
                apply in_map_iff in H3. destruct H3.
                destruct H3.
                rewrite Forall_forall in H7.
                specialize (H7 x0 H4). subst.
                destruct x0.
                apply KLD_fun_pos; auto; psatzl R. }
              { apply Forall_forall. intros.
                apply in_map_iff in H3. destruct H3.
                destruct H3.
                rewrite Forall_forall in H7.
                specialize (H7 x0 H4). subst.
                destruct x0.
                apply KLD_fun_pos; auto; psatzl R. }
              { apply Forall_forall. intros.
                apply in_map_iff in H3. destruct H3.
                destruct H3.
                rewrite Forall_forall in H7.
                specialize (H7 x0 H4). subst.
                destruct x0.
                apply KLD_fun_pos; auto; psatzl R. } }
            { compute in n. specialize_arith_hyp H10.
              intuition. subst. simpl. rewrite Rmax_left.
              { rewrite Rplus_opp_r. reflexivity. }
              { rewrite Rplus_opp_r. apply Rnot_le_lt in n.
                left. eapply Rle_lt_trans; eauto. right.
                pose proof (max_R_strict_increasing f)
                as Hmax_R_f. subst f.
                rewrite Hmax_R_f; auto; clear Hmax_R_f.
                { rewrite map_map. simpl in *.
                f_equal.
                { unfold KLD_fun in *. intuition.
                  specialize (H4 _ Ha).
                  destruct H4. rewrite <- H4.
                  { f_equal. psatzl R. }
                  { psatzl R. }
                  { psatzl R. } }
                { f_equal. apply map_ext_strong. intros.
                  inversion H7.
                  rewrite Forall_forall in H11.
                  specialize (H11 _ H3). destruct a2.
                  unfold KLD_fun in *. intuition.
                  specialize (H13 d0 H10). intuition.
                  rewrite <- H18; try psatzl R. f_equal.
                  psatzl R. } }
                { apply Forall_forall. intros.
                  apply in_map_iff in H3. destruct H3.
                  destruct H3.
                  rewrite Forall_forall in H7.
                  specialize (H7 x0 H4). subst.
                  destruct x0.
                  apply KLD_fun_pos;
                    auto; psatzl R. } } } } } }
      { charge_intros. clear_not_always.
        repeat rewrite always_and. charge_revert.
        rewrite <- always_impl. apply always_tauto.
        repeat rewrite curry. reason_action_tac.
        unfold focusA. simpl.
        destruct pre_st
          as [[pre_hist [pre_d pre_t]] pre_st].
        destruct post_st
          as [[post_hist [post_d post_t]] post_st].
        unfold pre, post. simpl. intros.
        split.
        { unfold acc_dist. simpl. subst. reflexivity. }
        { unfold bounded, bounded2, IndInv in *.
          cbv beta iota zeta delta
          - [ max_R Rmax map KLD_fun K_fun L_fun ] in *.
          psatzl R. } } }
  Qed.

  Theorem robust2_mu_gamma_rho_robust2 :
    forall P,
      P |-- sensible_time ->
      (exists gamma mu rho,
          K_fun gamma /\ KLD_fun mu /\ (0 <= rho)%R /\
          focusT snd P //\\ [!(init_dist2 mu gamma)]
          //\\ [][acc_dist2 mu gamma] |--
          [][!(bounded2 rho)]) ->
      P |-- robust2.
  Proof.
    intros P Ht H. unfold robust2.
    destruct H
      as [gamma [mu [rho [Hmu [Hgamma [Hrho Hrobust]]]]]].
    charge_split; [ assumption | ].
    apply lexistsR with (x:=gamma);
      charge_split; [ apply embedPropR; assumption | ].
    apply lexistsR with (x:=mu);
      charge_split; [ apply embedPropR; assumption | ].
    apply lexistsR with (x:=rho);
      charge_split; [ apply embedPropR; assumption | ].
  Admitted.

End Robustness.