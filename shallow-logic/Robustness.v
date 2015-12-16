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

  Record dist_state : Type :=
  { ds : list (R * R) }.

  Local Open Scope LTL_scope.

  Definition dist (gamma : R -> R)
    : StateVal state (R * R) :=
    `pair t (`gamma (`Rabs IC)).

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
    (lift2 (@map (R * R) R)
           (flip (fun p =>
                    (`mu (pure (snd p))
                      (snd#t `- (pure (fst p)))%R)))
           fst#ds)
    `+ `rho.

  (* This is the definition of robustness from the
     Tabuada paper. *)
  Definition robust : TraceProp state :=
    Exists gamma : R -> R,   embed (K_fun gamma) //\\
    Exists mu : R -> R -> R, embed (KLD_fun mu)  //\\
    Exists rho : R,          embed (0 <= rho)%R  //\\
      TExists dist_state ,
         [!(init_dist gamma)] //\\
         [][acc_dist gamma //\\ !(bounded mu rho)].

  (* Now we write a definition of robustness that is
     equivalent to the Tabuada one, but easier to
     work with. *)

  (* For the equivalent definition of robustness,
     we only need to store a single pair of disturbance
     and time rather than a list of pairs. *)
  Record dist_state2 : Type :=
    { d : R;
      td : R }.

  Definition dist2 (mu : R -> R -> R) (gamma : R -> R)
    : StateVal state R :=
    `mu (`gamma (`Rabs IC)) `R0.

  Definition init_dist2 (mu : R -> R -> R) (gamma : R -> R)
    : StateProp (dist_state2 * state) :=
    fst#d `= snd#(dist2 mu gamma) //\\
    fst#td `= snd#t.

  Definition acc_dist2 (mu : R -> R -> R) (gamma : R -> R)
    : ActionProp (dist_state2 * state) :=
    let prev := `mu (!(fst#d)) (((snd#t)! `- !(fst#td))) in
    let new := snd#(dist2 mu gamma)! in
    (new `<= prev -->>
       ((fst#d)! `= prev //\\ (fst#td)! `= !(fst#td))) //\\
    (prev `< new -->>
       ((fst#d)! `= new //\\ (fst#td)! `= !(snd#t))).

  Definition bounded2 (rho : R)
    : StateProp (dist_state2 * state) :=
    snd#OC `<= fst#d `+ `rho.

  Definition robust2 : TraceProp state :=
    Exists gamma : R -> R,   embed (K_fun gamma) //\\
    Exists mu : R -> R -> R, embed (KLD_fun mu)  //\\
    Exists rho : R,          embed (0 <= rho)%R  //\\
      TExists dist_state2 ,
          [!(init_dist2 mu gamma)] //\\
          [][acc_dist2 mu gamma //\\ !(bounded2 rho)].

  Definition IndInv (mu : R -> R -> R)
    : StateProp (list (R * R) * dist_state2 * state) :=
    lift1
      (List.Forall (fun p => 0 <= fst p //\\ 0 <= snd p)%R)
      fst#fst //\\
    fst#snd#d `=
    `max_R
    (lift2 (@map (R * R) R)
           (flip (fun p =>
                    (`mu (pure (snd p))
                      (snd#t `- (pure (fst p)))%R)))
           fst#fst).

  Theorem robust2_robust :
    robust2 |-- robust.
  Proof.
    repeat (apply lexists_lentails_m; red; intros;
            charge_revert; apply embedPropL; intros;
            charge_intros; charge_split;
            [ apply embedPropR; assumption | ]).
    rewrite (add_history _ snd#(dist a)).
    rewrite texists_texists. simpl CoFunctor.cofmap.
    eapply refinement_mapping
    with (f:=fun st => Build_dist_state (fst (fst st))).
    rewrite_focus.
    charge_split.
    { repeat rewrite landA. rewrite landC. charge_revert.
      rewrite landC. repeat rewrite landA. rewrite landC.
      charge_revert. charge_clear.
      repeat rewrite starts_impl. apply starts_tauto.
      Local Transparent ILInsts.ILFun_Ops.
      Local Transparent ILInsts.ILPre_Ops.
      unfold focusA, focusS. simpl. intros pre_st post_st.
      destruct pre_st as [[pre_hist [pre_d pre_t]] pre_st].
      intros. compute in *. assumption. }
    { charge_assert ([][!(IndInv a0)]).
      { eapply discrete_induction.
        { (* This is some pretty annoying manipulation
             required because of a lack of a proper
             tactic language. *)
          repeat rewrite landA. rewrite landC.
          repeat rewrite landA. rewrite landC.
          charge_revert.
          repeat rewrite landA. rewrite landC.
          repeat rewrite landA. rewrite landC.
          charge_revert. charge_clear. charge_intros.
          rewrite always_and. charge_assumption. }
        { repeat rewrite landA. rewrite landC. charge_revert.
          rewrite landC. repeat rewrite landA. rewrite landC.
          charge_revert. charge_clear.
          repeat rewrite starts_impl. apply starts_tauto.
          Local Transparent ILInsts.ILFun_Ops.
          Local Transparent ILInsts.ILPre_Ops.
          Local Opaque Rabs Rle.
          unfold focusA, focusS. simpl. intros pre_st post_st.
          destruct pre_st
            as [[pre_hist [pre_d pre_t]] pre_st].
          unfold pre, IndInv, max_R, init_dist2. simpl.
          intros. rewrite H3. compute. compute in H4, H3.
          split.
          { constructor; [ | constructor ].
            split.
            { (* This is unprovable because we don't know
                 anything about t. *) admit. }
            { apply K_fun_pos;
              [assumption | apply Rabs_pos]. } }
          { destruct H4. rewrite H4.
            rewrite Rplus_opp_r.
            match goal with
              |- context [ if ?e then _ else _ ] =>
              destruct e
            end.
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
          _liftn, flip, Rmax, pre, post in *. simpl in *.
          split.
          { intuition. subst. constructor; [ | assumption ].
            { split.
              { (* This is unprovable because we don't know
                 anything about t. *) admit. }
              { compute; apply K_fun_pos;
                [assumption | apply Rabs_pos]. } } }
          { intuition.
            destruct (Rle_dec
                        (dist2 a0 a post_st)
                        (a0 pre_d (t post_st - pre_t)))%R.
            { intuition. subst. clear - H H0 r H6. simpl.
              unfold KLD_fun in *. unfold Rminus.
              rewrite Rplus_opp_r.
              (* We need some lemma that allows us to move
                 the outer application of a0 inside the
                 map. *) admit. }
            { intuition. specialize_arith_hyp H9. intuition.
              subst. unfold dist2. simpl.
              (* We need the same sort of lemma for this
                 case as well. *) admit. } } } }
      { (* We need to use bounded2 and IndInv to prove
           bounded. *) admit. } }
  Admitted.

End Robustness.