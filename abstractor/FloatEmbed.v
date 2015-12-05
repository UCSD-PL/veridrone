(* Specialization of the Embedding framework to our floating-point language *)
Require Import Source.
Require Import Embed.
Require Import Logic.Syntax.
Require Import Logic.Semantics.
Require Import Coq.Reals.Rbase.
Require Import Coq.Strings.String.
Require Import micromega.Psatz.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Option.
Require Import RelDec.

Inductive fexpr :=
| FVar : Var -> fexpr
| FConst : Source.float -> fexpr
| FPlus : fexpr -> fexpr -> fexpr
| FMinus : fexpr -> fexpr -> fexpr
| FMult : fexpr -> fexpr -> fexpr
(*| FDiv : fexpr -> fexpr -> fexpr*)
.
(* TODO - other ops? *)

Definition fplus : Source.float -> Source.float -> Source.float :=
  Fappli_IEEE.Bplus custom_prec custom_emax custom_precGt0
                    custom_precLtEmax custom_nan Fappli_IEEE.mode_NE.

Definition fminus : Source.float -> Source.float -> Source.float :=
  Fappli_IEEE.Bminus custom_prec custom_emax custom_precGt0
                     custom_precLtEmax custom_nan Fappli_IEEE.mode_NE.

Definition fmult : Source.float -> Source.float -> Source.float :=
  Fappli_IEEE.Bmult custom_prec custom_emax custom_precGt0
                    custom_precLtEmax custom_nan Fappli_IEEE.mode_NE.

Definition fdiv : Source.float -> Source.float -> Source.float :=
  Fappli_IEEE.Bdiv custom_prec custom_emax custom_precGt0
                   custom_precLtEmax custom_nan Fappli_IEEE.mode_NE.

(* TODO pretty sure we need to do variable translation here *)
Fixpoint fexprD (fx : fexpr) (sf : fstate) : option Source.float :=
  match fx with
    | FVar s         => fstate_lookup sf s
    | FConst f       => Some f
    | FPlus fx1 fx2  => lift2 fplus  (fexprD fx1 sf) (fexprD fx2 sf)
    | FMinus fx1 fx2 => lift2 fminus (fexprD fx1 sf) (fexprD fx2 sf)
    | FMult fx1 fx2  => lift2 fmult  (fexprD fx1 sf) (fexprD fx2 sf)
    (*| FDiv fx1 fx2   => lift2 fdiv   (fexprD fx1 sf) (fexprD fx2 sf)*)
  end.

Inductive fcmd : Type :=
| FSeq   : fcmd -> fcmd -> fcmd
| FSkip  : fcmd
| FAsn   : Var -> fexpr -> fcmd
| FIte   : fexpr -> fcmd -> fcmd -> fcmd
| FFail  : fcmd
.

(*Definition fzero := Eval compute in (nat_to_float 0).*)
Definition fzero : float := Fappli_IEEE.B754_zero 24 128 false.
Definition fnegzero : float := Fappli_IEEE.B754_zero 24 128 true.

Require Import compcert.flocq.Core.Fcore_ulp.

Definition F2OR (f : float) : option R :=
  match f with
    | Fappli_IEEE.B754_zero   _       => Some (FloatToR f)
    | Fappli_IEEE.B754_finite _ _ _ _ => Some (FloatToR f)
    | _                               => None
  end.

Definition float_lt (f1 f2 : float)  : Prop :=
  (FloatToR f1 < FloatToR f2)%R.

Definition float_ge (f1 f2 : float) : Prop :=
  (FloatToR f1 >= FloatToR f2)%R.

Inductive feval : fstate -> fcmd -> fstate -> Prop :=
| FESkip : forall s, feval s FSkip s
| FESeqS : forall s s' os'' a b,
    feval s a s' ->
    feval s' b os'' ->
    feval s (FSeq a b) os''
| FEAsnS : forall s v e val,
    fexprD e s = Some val ->
    feval s (FAsn v e) ((fstate_set s v val))
| FEIteT :
    forall s os' ex c1 c2 f,
      fexprD ex s = Some f ->
      float_lt f fzero ->
      feval s c1 os' ->
      feval s (FIte ex c1 c2) os'
| FEIteF:
    forall s os' ex c1 c2 f,
      fexprD ex s = Some f ->
      float_ge f fzero ->
      feval s c2 os' ->
      feval s (FIte ex c1 c2) os'
.

Require Import compcert.flocq.Appli.Fappli_IEEE.

Inductive pl_eq : float -> float -> Prop :=
| pl_zero : forall b b', pl_eq (B754_zero _ _ b) (B754_zero _ _ b')
| pl_inf : forall b b', pl_eq (B754_infinity _ _ b) (B754_infinity _ _ b')
| pl_nan : forall b b' p p', pl_eq (B754_nan _ _ b p) (B754_nan _ _ b' p')
| pl_except : forall b b' p, pl_eq (B754_infinity _ _ b) (B754_nan _ _ b' p)
| pl_refl : forall (p1 : float), pl_eq p1 p1
| pl_symm : forall p1 p2, pl_eq p1 p2 -> pl_eq p2 p1
| pl_trans : forall p1 p2 p3, pl_eq p1 p2 -> pl_eq p2 p3 -> pl_eq p1 p3
.

Definition real_float (r : R) (f : float): Prop :=
  (F2OR f = Some r)%type.

(* Instantiate our general embedding module for our particular case
   (floating-point, non-looping, imperative language) *)
Module FloatEmbed <: EMBEDDING.
  Definition ast := fcmd.
  Definition pl_data := float.
  Definition eval := feval.
  Definition istate := list (string * float).
  Definition pl_equ := pl_eq.
  Definition pl_equ_refl : forall p : pl_data, pl_equ p p := pl_refl.
  Definition pl_equ_trans : forall p p' p'' : pl_data, pl_equ p p' -> pl_equ p' p'' -> pl_equ p p'' := pl_trans.
  Definition pl_equ_symm : forall p p' : pl_data, pl_equ p p' -> pl_equ p' p := pl_symm.

  (* Definition required by EMBEDDING *)
  Definition states_iso (st st' : istate) : Prop :=
    forall (s : string),
      match (fm_lookup st s), (fm_lookup st' s) with
      | None, None => True
      | Some f1, Some f2 => pl_equ f1 f2
      | _, _ => False
      end.

  (* Definition we use for our purposes; equivalent to the above *)
  Definition states_iso' (st st' : istate) : Prop :=
    forall (s : string),
      match fm_lookup st s with
      | None => fm_lookup st' s = None
      | Some f =>
        exists f', fm_lookup st' s = Some f' /\
              F2OR f = F2OR f'
      end.

  Lemma pl_eq_F2OR :
    forall a b,
      pl_eq a b ->
      F2OR a = F2OR b.
  Proof.
    induction 1; simpl; try reflexivity; auto.
    rewrite IHpl_eq1. auto.
  Qed.

  Lemma bpow_nonzero :
    forall radix2 e, (~Fcore_Raux.bpow radix2 e = 0)%R.
  Proof.
    intros. intro.
    destruct e.
    - simpl in *. lra.
    - simpl in *.
      destruct radix2.
      generalize (Fcore_Zaux.Zpower_pos_gt_0); intro Hzpg.
      simpl in H.
      specialize (Hzpg radix_val p).
      apply Zle_bool_imp_le in radix_prop.
      assert (0 < radix_val)%Z by lia. specialize (Hzpg H0).
      apply Fcore_Raux.Z2R_lt in Hzpg.
      simpl in Hzpg. lra.
    - simpl in *.
      destruct radix2.
      simpl in H.
      generalize (Rinv_neq_0_compat (Fcore_Raux.Z2R (Z.pow_pos radix_val p))%R); intro Hin0.
      assert (~Fcore_Raux.Z2R (Z.pow_pos radix_val p) = 0)%R.
      { intro.
        generalize (Fcore_Zaux.Zpower_pos_gt_0); intro Hzpg.
        apply Zle_bool_imp_le in radix_prop.
        assert (0 < radix_val)%Z by lia.
        specialize (Hzpg radix_val p H1).
        apply Fcore_Raux.Z2R_lt in Hzpg.
        simpl in Hzpg. lra. }
      specialize (Hin0 H0).
      lra.
  Qed.
  
  Require Import ArithFacts.
  Require Import compcert.flocq.Core.Fcore_float_prop.
  
  Lemma F2OR_pl_eq :
    forall f f',
      F2OR f = F2OR f' ->
      pl_eq f f'.
  Proof.
    intros.
    unfold F2OR in H.
    consider f; consider f'; intros; subst; simpl in *; try constructor; try congruence.
    { consider b; intros; subst.
      { simpl in *.
        unfold Fcore_defs.F2R, Fcore_Raux.Z2R, Fcore_defs.Fnum in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        simpl in H0.
        inversion H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. }
      { simpl in *.
        unfold Fcore_defs.F2R, Fcore_Raux.Z2R, Fcore_defs.Fnum in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        simpl in H0. inversion H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. } }
    { constructor. }
    (* copypasta *)
    { consider b0; intros; subst.
      { simpl in *.
        unfold Fcore_defs.F2R, Fcore_Raux.Z2R, Fcore_defs.Fnum in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        simpl in H0.
        inversion H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. }
      { simpl in *.
        unfold Fcore_defs.F2R, Fcore_Raux.Z2R, Fcore_defs.Fnum in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        simpl in H0. inversion H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. } }
    { pose proof e0 as e0'. pose proof e2 as e2'.
      unfold Fappli_IEEE.bounded in e0', e2'.
      apply Bool.andb_true_iff in e2'. apply Bool.andb_true_iff in e0'.
      forward_reason.
      inversion H1.
      generalize (Fcore_generic_fmt.canonic_unicity radix2 (Fcore_FLT.FLT_exp (3 - custom_emax - custom_prec) custom_prec)); intro Huni.
      eapply canonic_canonic_mantissa in H2. eapply canonic_canonic_mantissa in H.
      symmetry in H5.
      specialize (Huni _ _ H2 H H5).
      inversion Huni.
      subst.
      eapply F2R_eq_reg in H5.
      consider b; consider b0; intros; subst; try solve [simpl in *; congruence].
      { simpl in H6. inversion H6.
        subst.
        clear.
        cutrewrite (eq e2 e0).
        - apply pl_refl.
        - generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
          intros.
          auto. }
      { simpl in H6. inversion H6.
        subst.
        clear.
        cutrewrite (eq e0 e2).
        - apply pl_refl.
        - generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
          intros. auto. } }
  Qed.
  
  Lemma states_iso_iso' : forall (st st' : istate),
      states_iso st st' <-> states_iso' st st'.
  Proof.
    intros.
    split.
    { intros. unfold states_iso, states_iso' in *.
      intro s. specialize (H s).
      consider (fm_lookup st s); intros; subst.
      { consider (fm_lookup st' s); intros; subst; try contradiction.
        apply pl_eq_F2OR in H1. eexists; split; eauto. }
      { consider (fm_lookup st' s); intros; subst; try contradiction; try reflexivity. } }
    { intros. unfold states_iso, states_iso' in *.
      intro s. specialize (H s).
      consider (fm_lookup st s); intros; subst.
      { consider (fm_lookup st' s); intros; subst.
        { apply F2OR_pl_eq. forward_reason. inversion H1. auto. }
        { forward_reason. congruence. } }
      { rewrite H0. auto. } }
  Qed.

  Definition asReal (f : float) (r : R) :=
    (F2OR f = Some r)%type.

  Definition asReal_is : asReal = (fun f r => F2OR f = Some r)%type := eq_refl.

  (* we may perhaps need a notion of validity *)
  Lemma states_iso_nil :
    forall ist,
      states_iso nil ist <-> ist = nil.
  Proof.
    split.
    - rewrite states_iso_iso'.
      intros. simpl in H.
      induction ist.
      * reflexivity.
      * simpl in H. destruct a.
        specialize (H s). simpl in *.
        consider (string_dec s s); intros; try congruence.
    - intros. subst. rewrite states_iso_iso'. unfold states_iso'. simpl. auto.
  Qed.

  Lemma fstate_lookup_update_match :
    forall fst v val,
      Some val = fstate_lookup (fstate_set fst v val) v.
  Proof.
    intros.
    induction fst.
    - simpl. rewrite rel_dec_eq_true; eauto with typeclass_instances.
    - simpl. destruct a.
      consider (v ?[eq] v0); intro; subst.
      + simpl. rewrite rel_dec_eq_true; eauto with typeclass_instances.
      + simpl. rewrite rel_dec_neq_false; eauto with typeclass_instances.
  Qed.

  Lemma fstate_lookup_irrelevant_update :
    forall fst v v' val,
      v <> v' ->
      fstate_lookup fst v = fstate_lookup (fstate_set fst v' val) v.
  Proof.
    intros.
    induction fst.
    - simpl. rewrite rel_dec_neq_false; eauto with typeclass_instances.
    - simpl. destruct a.
      consider (v ?[eq] v0); intros; subst.
      + rewrite rel_dec_neq_false; eauto with typeclass_instances.
        simpl. rewrite rel_dec_eq_true; eauto with typeclass_instances.
      + consider (v' ?[eq] v0); intros; subst.
        * simpl. rewrite rel_dec_neq_false; eauto with typeclass_instances.
        * simpl. rewrite rel_dec_neq_false; eauto with typeclass_instances.
  Qed.
  
  Lemma fstate_lookup_fm_lookup :
    forall fst v,
      fstate_lookup fst v = fm_lookup fst v.
  Proof.
    induction fst.
    - reflexivity.
    - simpl. intros.
      destruct a.
      consider (v ?[eq] v0); intro; subst.
      + consider (string_dec v0 v0); try congruence.
      + consider (string_dec v v0); try congruence.
  Qed.

  Lemma pl_eq_asReal' :
    forall (p1 p2 : pl_data) (r : R),
      pl_equ p1 p2 -> (asReal p1 r <-> asReal p2 r).
  Proof.
    unfold pl_equ.
    induction 1; split; auto;
    try solve [destruct IHpl_eq; auto];
    try solve [destruct IHpl_eq1; destruct IHpl_eq2; auto].
  Qed.

  Lemma pl_eq_asReal :
    forall (p1 p2 : pl_data) (r : R),
      pl_eq p1 p2 -> asReal p1 r -> asReal p2 r.
  Proof.
    intros.
    generalize (pl_eq_asReal' p1 p2 r H). intro Hplear.
    destruct Hplear. auto.
  Qed.

  Lemma states_iso_set' :
    forall ist ist',
      states_iso ist ist' ->
      forall val val', pl_eq val val' ->
                  forall v,
                    states_iso (fstate_set ist v val) (fstate_set ist' v val').
  Proof.
    intros.
    rewrite states_iso_iso' in H. rewrite states_iso_iso'.
    unfold states_iso' in *.
    induction H0.
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists. split; reflexivity.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        rewrite <- fstate_lookup_fm_lookup in H.
        consider (fstate_lookup ist s); intros; subst.
        + forward_reason. eexists. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; auto.
            rewrite <- fstate_lookup_fm_lookup in H0. eauto.
          * auto.
        + rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; auto.
          rewrite fstate_lookup_fm_lookup. auto. }
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        consider (fm_lookup ist s); intros; subst.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          forward_reason.
          exists x. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; eauto.
            rewrite fstate_lookup_fm_lookup. eauto.
          * auto.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          rewrite <- fstate_lookup_fm_lookup.
          erewrite <- fstate_lookup_irrelevant_update; eauto.
          rewrite fstate_lookup_fm_lookup. auto. }
    (* the following three are copy-paste of the previous block *)
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        consider (fm_lookup ist s); intros; subst.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          forward_reason.
          exists x. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; eauto.
            rewrite fstate_lookup_fm_lookup. eauto.
          * auto.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          rewrite <- fstate_lookup_fm_lookup.
          erewrite <- fstate_lookup_irrelevant_update; eauto.
          rewrite fstate_lookup_fm_lookup. auto. }
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        consider (fm_lookup ist s); intros; subst.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          forward_reason.
          exists x. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; eauto.
            rewrite fstate_lookup_fm_lookup. eauto.
          * auto.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          rewrite <- fstate_lookup_fm_lookup.
          erewrite <- fstate_lookup_irrelevant_update; eauto.
          rewrite fstate_lookup_fm_lookup. auto. }
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        consider (fm_lookup ist s); intros; subst.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          forward_reason.
          exists x. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; eauto.
            rewrite fstate_lookup_fm_lookup. eauto.
          * auto.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          rewrite <- fstate_lookup_fm_lookup.
          erewrite <- fstate_lookup_irrelevant_update; eauto.
          rewrite fstate_lookup_fm_lookup. auto. }
    (* interesting cases again *)
    { intros.
      specialize (IHpl_eq s).
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup in IHpl_eq. rewrite <- fstate_lookup_update_match in IHpl_eq.
        rewrite <- fstate_lookup_fm_lookup in IHpl_eq. rewrite <- fstate_lookup_update_match in IHpl_eq.
        forward_reason. inversion H1; subst.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        rewrite <- fstate_lookup_fm_lookup in IHpl_eq. rewrite <- fstate_lookup_irrelevant_update in IHpl_eq; [|auto].
        specialize (H s). rewrite <- fstate_lookup_fm_lookup in H.
        consider (fstate_lookup ist s); intros; subst.
        + rewrite <- fstate_lookup_fm_lookup.
          rewrite <- fstate_lookup_irrelevant_update; [|auto].
          rewrite fstate_lookup_fm_lookup. auto.
        + rewrite <- fstate_lookup_fm_lookup.
          rewrite <- fstate_lookup_irrelevant_update; [|auto].
          rewrite <- fstate_lookup_fm_lookup in H2.
          rewrite <- fstate_lookup_irrelevant_update in H2; auto. }
    { intros. specialize (IHpl_eq1 s). specialize (IHpl_eq2 s).
      consider (string_dec v s); intros; subst.
      - do 2 (rewrite <- fstate_lookup_fm_lookup; rewrite <- fstate_lookup_update_match).
        do 2 (rewrite <- fstate_lookup_fm_lookup in IHpl_eq1; rewrite <- fstate_lookup_update_match in IHpl_eq1).
        do 2 (rewrite <- fstate_lookup_fm_lookup in IHpl_eq2; rewrite <- fstate_lookup_update_match in IHpl_eq2).
        forward_reason.
        inversion H1; subst. inversion H0; subst.
        eexists.
        split; eauto. rewrite <- H2. auto.
      - do 2 (rewrite <- fstate_lookup_fm_lookup; rewrite <- fstate_lookup_irrelevant_update; [|auto]).
        do 2 (rewrite <- fstate_lookup_fm_lookup in IHpl_eq1; rewrite <- fstate_lookup_irrelevant_update in IHpl_eq1; [|auto]).
        do 2 (rewrite <- fstate_lookup_fm_lookup in IHpl_eq2; rewrite <- fstate_lookup_irrelevant_update in IHpl_eq2; [|auto]).
        specialize (H s). rewrite <- fstate_lookup_fm_lookup in H.
        consider (fstate_lookup ist s); intros; subst; eauto. }
  Qed.

  Ltac fwd := forward_reason.

  Definition pl_eq_lift (of1 of2 : option float) : Prop :=
    match of1, of2 with
    | None, None => True
    | Some f1, Some f2 => pl_eq f1 f2
    | _, _ => False
    end.

  Lemma INR_gt_zero :
    forall (n : nat), (INR n >= 0)%R.
  Proof.
    induction n.
    - simpl. lra.
    - simpl.
      destruct n.
      + lra.
      + lra.
  Qed.

  (* some copypasta in here as well *)
  Lemma pl_eq_finite_eq :
    forall b0 m0 e1 e2 b1 m1 e1' e2',
      let f  := B754_finite custom_prec custom_emax b0 m0 e1 e2 in
      let f' := B754_finite custom_prec custom_emax b1 m1 e1' e2' in
      pl_eq f f' ->
      f = f'.
  Proof.
    intros.
    apply pl_eq_F2OR in H.
    unfold f, f' in *. simpl in H.
    clear f f'.
    inversion H; clear H.
    generalize (Fcore_generic_fmt.canonic_unicity radix2 (Fcore_FLT.FLT_exp (3 - custom_emax - custom_prec) custom_prec)); intro Huni.
    apply Huni in H1.
    { inversion H1; subst.
      consider b0; intros.
      { consider b1; intros.
        { simpl in H1. inversion H1. subst.
          cutrewrite (eq e2 e2'); [reflexivity|].
          generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec). intros. auto. }
        { simpl in H1. inversion H1. } }
      { consider b1; intros.
        { simpl in H1. inversion H1. }
        { simpl in H1. inversion H1. subst.
          cutrewrite (eq e2 e2'); [reflexivity|].
          generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec). intros. auto. } } }
    { eapply canonic_canonic_mantissa.
      pose proof e2 as p2.
      apply Bool.andb_true_iff in p2. fwd. auto. }
    { eapply canonic_canonic_mantissa.
      pose proof e2' as p2'.
      apply Bool.andb_true_iff in p2'. fwd. auto. }
  Qed.
  
  (* For brutal case-analysis *)
  Ltac smash :=
    let rec smash' E :=
        match E with
        | context[match ?X with | _ => _ end] =>
          match X with
          | context[match ?Y with | _ => _ end] =>
            smash' X
          | _ => consider X; intros; subst
          end
            (* this branch could be smarter, but in practice we don't really use it here *)
        | context[if ?X then _ else _] =>
          consider X; intros; subst
        end
    in
    match goal with
    | |- ?G => smash' G
    end.

    Ltac smashs := repeat smash.

    Lemma pl_finite_neq_zero :
      forall b0 m e e0 b1,
        ~(pl_eq (B754_finite custom_prec custom_emax b0 m e e0)
                (B754_zero custom_prec custom_emax b1)).
    Proof.
      intros.
      intro.
      apply pl_eq_F2OR in H. simpl in H. inversion H; clear H.
      unfold Fcore_Zaux.cond_Zopp in H1. simpl in H1.
      consider b0; intros; subst.
      { unfold Fcore_defs.F2R in H0. simpl in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. }
      { unfold Fcore_defs.F2R in H0. simpl in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. }
    Qed.
    
  Lemma states_iso_fexprD :
    forall ist ist',
      states_iso ist ist' ->
      forall fx, pl_eq_lift (fexprD fx ist) (fexprD fx ist').
  Proof.
    induction fx; rewrite states_iso_iso' in H.
    { simpl. unfold pl_eq_lift.
      consider (fstate_lookup ist v); intros; subst;
      consider (fstate_lookup ist' v); intros; subst; try auto.
      { unfold states_iso' in H. specialize (H v). rewrite <- fstate_lookup_fm_lookup in H.
        rewrite H0 in H. forward_reason.
        apply F2OR_pl_eq in H2.
        eapply pl_equ_trans. apply H2.
        rewrite <- fstate_lookup_fm_lookup in H. rewrite H in H1. inversion H1; subst.
        constructor. }
      { unfold states_iso' in H. specialize (H v).
        rewrite <- fstate_lookup_fm_lookup in H.
        rewrite -> H0 in H. fwd.
        rewrite <- fstate_lookup_fm_lookup in H.
        congruence. }
      { unfold states_iso' in H. specialize (H v).
        rewrite <- fstate_lookup_fm_lookup in H.
        rewrite H0 in H.
        rewrite <- fstate_lookup_fm_lookup in H.
        congruence. } }
    { simpl. constructor. }
    { simpl.
      unfold pl_eq_lift in IHfx1. unfold pl_eq_lift in IHfx2.
      unfold lift2, pl_eq_lift.
      smashs; try congruence; auto.
      (* begin experiment *)
      unfold fplus, Bplus.
      smashs; try solve [constructor]; try solve [apply pl_symm; constructor];
      try solve [apply pl_eq_F2OR in IHfx1; simpl in IHfx1; congruence];
      try solve [apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_symm in IHfx1; apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_eq_F2OR in IHfx2; simpl in IHfx2; congruence];
      try solve [apply pl_finite_neq_zero in IHfx2; contradiction];
      try solve [apply pl_symm in IHfx2; apply pl_finite_neq_zero in IHfx2; contradiction].
      apply pl_eq_finite_eq in IHfx1. apply pl_eq_finite_eq in IHfx2.
      inversion IHfx1; inversion IHfx2; subst.
      apply pl_refl. }
    (* copypasta *)
    { simpl.
      unfold pl_eq_lift in IHfx1. unfold pl_eq_lift in IHfx2.
      unfold lift2, pl_eq_lift.
      smashs; try congruence; auto.
      (* begin experiment *)
      unfold fminus, Bplus, Bminus, Bplus. (* wtf *)
      smashs; try solve [constructor]; try solve [apply pl_symm; constructor];
      try solve [apply pl_eq_F2OR in IHfx1; simpl in IHfx1; congruence];
      try solve [apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_symm in IHfx1; apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_eq_F2OR in IHfx2; simpl in IHfx2; congruence];
      try solve [unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence;
                 apply pl_eq_F2OR in IHfx2; simpl in IHfx2; congruence];
      try solve [unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence;
                 apply pl_symm in IHfx2; apply pl_finite_neq_zero in IHfx2; contradiction];
      try solve [unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence;
                 apply pl_finite_neq_zero in IHfx2; contradiction].
      { unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence.
        apply pl_eq_finite_eq in IHfx2.
        inversion IHfx2; subst; clear IHfx2.
        inversion H7; subst; clear H7.
        inversion H2; subst; clear H2.
        cutrewrite (eq e0 e2); [apply pl_refl|].
        generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
        intros.
        auto. }
      { unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence.
        apply pl_eq_finite_eq in IHfx1.
        inversion IHfx1; subst; clear IHfx1.
        inversion H2; subst; clear H2.
        inversion H7; subst; clear H7.
        apply pl_eq_finite_eq in IHfx2.
        inversion IHfx2; subst; clear IHfx2.
        apply pl_refl. } }
    (* copypasta *)
    { simpl.
      unfold pl_eq_lift in IHfx1. unfold pl_eq_lift in IHfx2.
      unfold lift2, pl_eq_lift.
      smashs; try congruence; auto.
      unfold fmult, Bmult.
      smashs; try solve [constructor]; try solve [apply pl_symm; constructor];
      try solve [apply pl_eq_F2OR in IHfx1; simpl in IHfx1; congruence];
      try solve [apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_symm in IHfx1; apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_eq_F2OR in IHfx2; simpl in IHfx2; congruence];
      try solve [apply pl_finite_neq_zero in IHfx2; contradiction];
      try solve [apply pl_symm in IHfx2; apply pl_finite_neq_zero in IHfx2; contradiction].
      { apply pl_eq_finite_eq in IHfx1.
        inversion IHfx1; subst; clear IHfx1.
        apply pl_eq_finite_eq in IHfx2.
        inversion IHfx2; subst; clear IHfx2.
        cutrewrite (eq e0 e4).
        { cutrewrite (eq e2 e6).
          { apply pl_refl. }
          { generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
            intros.
            auto. } }
        { generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
          intros.
          auto. } } }
  Qed.

  (*
  Lemma  eval_det1:
    forall prg isti istf istf',
      eval isti prg istf ->
      eval isti prg istf' ->
      states_iso istf istf'.
  Proof.
    intros.
        
  Axiom eval_det2 :
    forall prg isti istf istf',
      (istf ~~ istf') ->
      eval isti prg istf ->
      exists isti', isti ~~ isti' /\ eval isti' prg istf'
*)
  
  Lemma eval_det :
    forall prg isti isti' istf,
      (states_iso isti isti') ->
      eval isti prg istf ->
      exists istf', states_iso istf istf' /\ eval isti' prg istf'.
  Proof.
    induction prg.
    - intros. inversion H0; subst; clear H0.
      specialize (IHprg1 _ _ _ H H4). forward_reason.
      specialize (IHprg2 _ _ _ H0 H6). forward_reason.
      eexists. split; eauto.
      econstructor; eauto.
    - intros.
      inversion H0; subst; clear H0.
      eexists; split; eauto. econstructor.
    - intros.
      inversion H0; subst; clear H0.
      generalize (states_iso_fexprD _ _ H f); intro Hsif.
      unfold pl_eq_lift in Hsif.
      rewrite H5 in Hsif.
      consider (fexprD f isti'); intros; try contradiction.
      exists (fstate_set isti' v f0).
      split.
      + eapply states_iso_set'; auto.
      + econstructor; auto.
    - intros.
      generalize (states_iso_fexprD _ _ H f); intro Hsif.
      inversion H0; subst; clear H0.
      + specialize (IHprg1 _ _ _ H H8).
        forward_reason.
        unfold pl_eq_lift in Hsif.
        rewrite H5 in Hsif.
        consider (fexprD f isti'); intros; try contradiction.
        exists x; split; eauto.
        eapply FEIteT; eauto.
        apply pl_eq_F2OR in Hsif.
        unfold float_lt in *.
        unfold F2OR in *.
        consider f0; consider f1; intros; subst; auto; simpl in *;
        try lra; try solve [inversion Hsif; lra].
      + specialize (IHprg2 _ _ _ H H8).
        forward_reason.
        unfold pl_eq_lift in Hsif.
        rewrite H5 in Hsif.
        consider (fexprD f isti'); intros; try contradiction.
        exists x; split; auto.
        eapply FEIteF; eauto.
        apply pl_eq_F2OR in Hsif.
        unfold float_ge in *.
        unfold F2OR in *.
        consider f0; consider f1; intros; subst; auto; simpl in *;
        try lra; try solve [inversion Hsif; lra].
    - intros.
      inversion H0.
  Qed.      
  
  Lemma asReal_det :
    forall (p p' : pl_data) (r : R),
      asReal p r ->
      asReal p' r ->
      pl_eq p p'.
  Proof.
    unfold asReal.
    intros. rewrite <- H in H0.
    apply F2OR_pl_eq in H0. apply pl_symm. auto.
  Qed.

  Definition models (vars : list string) (ist : istate) (sst : Syntax.state) : Prop :=
    forall (s : string),
      (In s vars ->
      exists (d : pl_data),
        fm_lookup ist s = Some d /\
        asReal d (sst s)) /\
      (~In s vars -> fm_lookup ist s = None).

  Definition embedding : Type := list string -> ast -> Syntax.Formula.

  Definition embedding_correct1 (embed : embedding) : Prop :=
    forall (v : list string) (prg : ast) (is is' : istate) (ls ls' : Syntax.state) (tr : Stream.stream Syntax.state),
      models v is ls ->
      models v is' ls' ->
      eval is prg is' ->
      Semantics.eval_formula
        (embed v prg)
        (Stream.Cons ls (Stream.Cons ls' tr)).

  Definition embedding_correct2 (embed : embedding) : Prop :=
    forall (v : list string) (prg : ast) (is : istate) (ls : Syntax.state) (tr : Stream.stream Syntax.state),
      models v is ls ->
      ~(exists is', eval is prg is') ->
      ~(Semantics.eval_formula
        (Enabled (embed v prg))
        (Stream.Cons ls tr)).

  (* Here is a correct embedding function.
     Note that its correctness depends on the semantics being
     deterministic *)
  Definition embed_ex (v : list string) (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun lpre lpost =>
                    exists cpre cpost,
                      models v cpre lpre /\
                      models v cpost lpost /\
                      eval cpre prg cpost).


  (** Next, some definitions for Hoare-style reasoning about programs.
      We use this to implement weakest-precondition.
   **)
  Section Hoare.
    Variables (P : istate -> Prop) (c : ast) (Q : istate -> Prop).

    Definition HoareProgress : Prop :=
      forall s, P s -> exists s', eval s c s'.

    Definition HoarePreservation : Prop :=
      forall s, P s ->
           forall s', eval s c s' ->
                 Q s'.

    (* safety no longer needed *)

    Definition Hoare' : Prop :=
      (HoareProgress /\ HoarePreservation)%type.

    Definition Hoare : Prop :=
      (forall s, P s ->
            (exists s', eval s c s') /\
            (forall s', eval s c s' -> Q s'))%type.

  End Hoare.
  
End FloatEmbed.

(* The following is a Hoare logic implementation for floating-point language *)
Require Import Bound.
Import FloatEmbed.

Definition vmodels := models.

(** This is the semantic side condition **)
(* slightly different way of stating models_det facts *)
Definition SEMR (vs : list Var) (P : Syntax.state -> Prop) : Prop :=
  forall (c : istate) (a b : Syntax.state), vmodels vs c a -> vmodels vs c b -> P a -> P b.

Definition Hoare_ := Hoare.

(* These are no longer used; we're performing the abstraction at the level
   of fwp rather than here. This was due to underlying changes to bound.v *)
  Definition HoareA_all (vs : list string)
             (P : Syntax.state -> Prop) (c : ast) (Q : Syntax.state -> Prop)
    : Prop :=
    Hoare_ (fun fst => forall rst : Syntax.state, vmodels vs fst rst -> P rst)%type
           c
           (fun fst => forall rst : Syntax.state, vmodels vs fst rst -> Q rst)%type.

  Definition HoareA_ex (vs : list string)
             (P : Syntax.state -> Prop) (c : ast) (Q : Syntax.state -> Prop)
    : Prop :=
    Hoare_ (fun fst => exists rst : Syntax.state, vmodels vs fst rst /\ P rst)%type
           c
           (fun fst => exists rst : Syntax.state, vmodels vs fst rst /\ Q rst)%type.

  Definition fembed_ex :=
    embed_ex. 

  Lemma Hoare__embed :
    forall P c Q vs,
      Hoare_ P c Q ->
      (|-- fembed_ex vs c -->>
           Embed (fun st st' =>
                    exists fst,
                      vmodels vs fst st /\
                      (P fst ->
                       exists fst',
                         vmodels vs fst' st' /\
                         Q fst'))).
  Proof.
    simpl. intros. unfold tlaEntails. simpl.
    intros.
    fwd.
    unfold Hoare_, Hoare in H.
    exists x. unfold vmodels. split; auto.
    intros.
    exists x0.
    split; auto.
    specialize (H _ H4). fwd.
    auto.
  Qed.
    
  Lemma Hoare__skip :
    forall (P : istate -> Prop),
      Hoare_ P FSkip P.
  Proof.
    red. red. intros.
    split.
    { eexists; constructor. }
    { intros. inversion H0. subst. auto. }
  Qed.

  Lemma Hoare__seq :
    forall P Q R c1 c2,
      Hoare_ P c1 Q ->
      Hoare_ Q c2 R ->
      Hoare_ P (FSeq c1 c2) R.
  Proof.
    unfold Hoare_, Hoare.
    intros.
    split.
    { eapply H in H1.
      forward_reason.
      specialize (H0 _ (H2 _ H1)).
      forward_reason.
      eexists. econstructor; eauto. }
    { intros. inversion H2; subst; clear H2.
      specialize (H _ H1). fwd.
      specialize (H2 _ H6).
      specialize (H0 _ H2).
      fwd; auto. }
  Qed.
  
  (* this plus consequence should be enough to get our real assignment rule
   that talks about bounds *)
  Lemma Hoare__asn :
    forall P v e,
      Hoare_
        (fun fs : fstate =>
           exists val : float,
             fexprD e fs = Some val /\
             P (fstate_set fs v val))%type
        (FAsn v e)
        P.
  Proof.
    intros. red. red.
    intros. fwd.
    split.
    - eexists. constructor. eassumption.
    - intros. inversion H1; subst; clear H1.
      rewrite H6 in H. inversion H; subst; clear H. assumption.
  Qed.

  Require Import Bound.

  (* Calculating bounds for expressions *)
  Fixpoint fexpr_to_NowTerm (fx : fexpr) : NowTerm :=
    match fx with
    (*| FVar v   => VarNowN (vtrans_flt2tla ivs v)*)
    | FVar v => VarNowN v
    | FConst f => FloatN f
    | FPlus fx1 fx2 =>
      PlusN (fexpr_to_NowTerm fx1) (fexpr_to_NowTerm fx2)
    | FMinus fx1 fx2 =>
      MinusN (fexpr_to_NowTerm fx1) (fexpr_to_NowTerm fx2)
    | FMult fx1 fx2 =>
      MultN (fexpr_to_NowTerm fx1) (fexpr_to_NowTerm fx2)
    end.

  Definition bound_fexpr (fx : fexpr) : list singleBoundTerm :=
    bound_term (fexpr_to_NowTerm fx).

  Definition bounds_to_formula (sbt : singleBoundTerm) (fs : fstate) : (Prop * (R -> Prop)) :=
    denote_singleBoundTermNew fs sbt.

  (* Used to translate between two different representations
   of floating-point state (since bounds proofs use a different one) *)
  
  (* Ensures the variable map only mentions variables in the given expression *)
  Fixpoint varmap_check_fexpr (ivs : list (Var * Var)) (e : fexpr) : Prop :=
    match e with
    | FVar v       => exists lv, In (lv, v) ivs
    | FConst _     => True
    | FPlus e1 e2  => varmap_check_fexpr ivs e1 /\
                     varmap_check_fexpr ivs e2
    | FMinus e1 e2 => varmap_check_fexpr ivs e1 /\
                     varmap_check_fexpr ivs e2
    | FMult e1 e2  => varmap_check_fexpr ivs e1 /\
                     varmap_check_fexpr ivs e2
    end%type.

  (* another lemma needed for bound_fexpr_sound *)
  Lemma fexpr_NowTerm_related_eval :
    forall fst,
    forall fx f,
      fexprD fx fst = Some f ->
      eval_NowTerm fst (fexpr_to_NowTerm fx) = Some f.
  Proof.
    induction fx; eauto;
    try (intros; simpl; simpl in *; fwd;
         unfold lift2 in *;
           consider (fexprD fx1 fst); intros; try congruence;
         consider (fexprD fx2 fst); intros; try congruence;
         erewrite IHfx1; eauto;
         erewrite IHfx2; eauto).
  Qed.

  Lemma bound_fexpr_sound : forall fx sbts,
      bound_fexpr fx = sbts ->
      List.Forall (fun sbt =>
                     forall (fst : fstate) f,
                       fexprD fx fst = Some f ->
                       let '(P,Pr) := bounds_to_formula sbt fst in
                       P -> exists fval, fexprD fx fst = Some fval
                                   /\ exists val,
                             F2OR fval = Some val /\ Pr val)%type
                  sbts.
  Proof.
    intros.
    generalize (bound_proof'). intro Hbp.
    apply Forall_forall. intros.
    specialize (Hbp (fexpr_to_NowTerm fx) fst). simpl in *. intros.
    exists f.
    split; auto.
    unfold boundDef' in Hbp. simpl in Hbp.
    generalize (fexpr_NowTerm_related_eval _ _ _ H1); intro Hentfxd.
    rewrite Hentfxd in Hbp.
    apply Forall_forall with (x := x) in Hbp.
    - consider (floatToReal f); intros.
      + exists r. split.
        * fwd. rewrite <- H3. reflexivity.
        * forward_reason. auto.
      + exfalso; auto.
    - unfold bound_fexpr in *. rewrite H. assumption.
  Qed.

  (* Useful prop combinator *)
  Fixpoint AnyOf (Ps : list Prop) : Prop :=
    match Ps with
    | nil => False
    | P :: Ps => P \/ AnyOf Ps
    end%type.

  (* perhaps unnecessary *)
  Fixpoint varmap_check_fcmd (ivs : list (Var * Var)) (c : fcmd) : Prop :=
    match c with
    | FSeq c1 c2   => varmap_check_fcmd ivs c1 /\
                     varmap_check_fcmd ivs c2
    | FSkip        => True
    | FAsn v e     => In (v, v) ivs /\ varmap_check_fexpr ivs e
    | FIte e c1 c2 => varmap_check_fexpr ivs e  /\
                     varmap_check_fcmd   ivs c1 /\
                     varmap_check_fcmd   ivs c2
    | FFail        => True
    end%type.

  (* Lemmas aboutt Forall, needed for HoareA_ex_asn *)
  Lemma Forall_impl : forall T (P Q : T -> Prop) ls,
      List.Forall (fun x => P x -> Q x) ls ->
      (List.Forall P ls -> List.Forall Q ls).
  Proof.
    induction 2.
    - constructor.
    - inversion H; clear H; subst.
      constructor; eauto.
  Qed.

  Lemma Forall_tauto : forall T (P : T -> Prop) ls,
      (forall x, P x) ->
      List.Forall P ls.
  Proof.
    induction ls; simpl; intros; eauto.
  Qed.

  Lemma floatConstValid_toR :
    forall val,
      isFloatConstValid val -> exists r,
        (F2OR val = Some r)%type.
  Proof.
    intros.
    unfold isFloatConstValid in H.
    destruct val; try contradiction; solve [eexists; reflexivity].
  Qed.

  Lemma Hoare__bound_asn :
    forall (P : _ -> Prop) v e,
      Hoare_ (fun fst : fstate =>
                exists res, fexprD e fst = Some res /\
                       AnyOf (List.map (fun sbt =>
                                          let '(pred,bound) := bounds_to_formula sbt fst in
                                          pred /\ forall (val : float) (r : R),
                                              F2OR val = Some r ->
                                              bound r ->
                                              P (fstate_set fst v val))
                                       (bound_fexpr e)))%type
             (FAsn v e)
             P.
  Proof.
    intros. red; red. intros.
    fwd.
    split.
    { consider (fexprD e s); intros.
      - eexists. econstructor. eassumption.
      - congruence. }
    { intros. inversion H1; subst; clear H1.
      simpl in H0.
      generalize (bound_fexpr_sound e _ eq_refl). intro Hbfs.
      induction (bound_fexpr e).
      { simpl in *. contradiction. }
      { simpl in *. destruct H0.
        { clear IHl.
          inversion Hbfs. fwd.
          subst.
          specialize (H3 _ _ H6 H0). fwd.
          rewrite H in H1. inversion H1. subst. clear H1.
          eapply H5.
          - rewrite H in H6. inversion H6. subst. eauto.
          - lra. }
        { inversion Hbfs; subst; clear Hbfs.
          eapply IHl; eauto. } } }
  Qed.        


  Lemma Hoare__conseq :
    forall (P P' Q Q' : fstate -> Prop) (c : fcmd),
      (forall (st : fstate), P st  -> P' st) ->
      (forall (st : fstate), Q' st -> Q  st) ->
      Hoare_ P' c Q' ->
      Hoare_ P c Q.
  Proof.
    intros. unfold Hoare_, Hoare in *.
    intros. apply H in H2. apply H1 in H2. fwd.
    split; try eexists; eauto.
  Qed.

  (* A couple of lemmas used for ITE rule *)
  Lemma Hoare__or :
    forall (P1 P2 Q : _ -> Prop) c,
      Hoare_ P1 c Q ->
      Hoare_ P2 c Q ->
      Hoare_ (fun st => P1 st \/ P2 st)%type c Q.
  Proof.
    intros.
    unfold Hoare_, Hoare in *.
    intros.
    destruct H1; eauto.
  Qed.    

  Lemma Hoare__False :
    forall (P : _ -> Prop) c,
      Hoare_ (fun _ => False) c P.
  Proof.
    intros.
    unfold Hoare_, Hoare. intros. contradiction.
  Qed.

  Definition maybe_lt0 (sbts : list singleBoundTerm) (fst : fstate) : Prop :=
    AnyOf (List.map
             (fun sbt =>
                (lb sbt fst <  0)%R /\
                (premise sbt fst)) sbts).

  Definition maybe_ge0 (sbts : list singleBoundTerm) (fst : fstate) : Prop :=
    AnyOf (List.map
             (fun sbt =>
                (ub sbt fst >=  0)%R /\
                (premise sbt fst)) sbts).

  Lemma or_distrib_imp :
    forall A B C : Prop,
      (A \/ B -> C) <->
      (A -> C) /\ (B -> C).
  Proof.
    tauto.
  Qed.

  Lemma and_distrib_or :
    forall A B C : Prop,
      A /\ (B \/ C) <->
      (A /\ B) \/ (A /\ C).
  Proof.
    tauto.
  Qed.

  Lemma float_lt_ge_trichotomy :
    forall f f', (float_lt f f' \/ float_ge f f').
  Proof.
    intros. unfold float_lt, float_ge.
    lra.
  Qed.

  Lemma float_lt_ge_trichotomy_contra :
    forall f f', float_lt f f' /\ float_ge f f' -> False.
  Proof.
    intros. unfold float_lt, float_ge in H. lra.
  Qed.

  Lemma Hoare__bound_ite :
    forall ex (P Q1 Q2 : _ -> Prop) c1 c2,
      Hoare_ Q1 c1 P ->
      Hoare_ Q2 c2 P ->
      Hoare_ (fun fst =>
                exists res, fexprD ex fst = Some res /\
                       let bs := bound_fexpr ex in
                       (maybe_lt0 bs fst -> Q1 fst) /\
                       (maybe_ge0 bs fst -> Q2 fst) /\
                       (AnyOf (List.map
                                 (fun sbt => let '(prem, _) := denote_singleBoundTermNew fst sbt in prem)
                                 bs)))%type
             (FIte ex c1 c2)
             P.
Proof.
  intros.
  generalize (bound_fexpr_sound ex (bound_fexpr ex) eq_refl).
  induction 1.
  { simpl. eapply Hoare__conseq.
    3: eapply Hoare__False.
    - simpl. intros. fwd. auto.
    - exact (fun _ x => x). }
  { simpl.
    eapply Hoare__conseq.
    2: exact (fun _ x => x).
    unfold maybe_lt0. unfold maybe_ge0.
    simpl. intros.
    repeat setoid_rewrite or_distrib_imp in H3.
    repeat setoid_rewrite and_distrib_or in H3.
    eapply H3.
    eapply Hoare__conseq.
    2: exact (fun _ x => x).
    2: eapply Hoare__or.
    3: eapply IHForall.
    simpl. intros. fwd.
    destruct H3.
    { fwd.
      left.
      exact (conj (Logic.ex_intro (fun x0 => eq (fexprD ex st) (Some x0)) _ H3) (conj H6 (conj H8 (conj H7 (conj H4 H5))))). }
    { right.
      fwd.
      unfold maybe_lt0, maybe_ge0.
      eexists. split; eauto. }
    clear H2 IHForall.
    do 2 red. intros.
    fwd.
    simpl in H1.
    do 2 red in H, H0.
    specialize (H1 _ _ H2 H3). fwd.
    assert (x1 = x0).
    { rewrite H1 in H2. inversion H2; auto. }
    subst.
    destruct (float_lt_ge_trichotomy x0 fzero).
    { pose proof H11 as H11'.
      unfold float_lt in H11. simpl in H11.
      unfold F2OR in H8. consider x0; intros; try congruence.
      { simpl in H12. lra. }
      { inversion H11.
        assert (x2 < 0)%R.
        { rewrite <- H14 in H9.
          simpl in H12.
          lra. }
        assert (lb x s < 0)%R by lra.
        fwd.
        specialize (H _ H6). fwd.
        split.
        { eexists. eapply FEIteT; eauto. }
        { intros. inversion H17; subst; clear H17; auto.
          rewrite H2 in H22. inversion H22; subst.
          generalize (float_lt_ge_trichotomy_contra _ _ (conj H11' H24)).
          intro; contradiction. } } }
    { pose proof H11 as H11'.
      unfold float_ge in H11. simpl in H11.
      unfold F2OR in H8. consider x0; intros; try congruence.
      { inversion H11. subst.
        apply Rle_ge in H10.
        fwd.
        specialize (H0 _ H7). fwd.
        split.
        { eexists. eapply FEIteF; eauto. }
        { intros. inversion H13; subst; clear H13; auto.
          rewrite H2 in H18. inversion H18; subst.
          generalize (float_lt_ge_trichotomy_contra _ _ (conj H20 H11')).
          intros; contradiction. } }
      { inversion H11.
        assert (x2 >= 0)%R.
        { simpl in H12.
          rewrite H14 in H12.
          assumption. }
        assert (ub x s >= 0)%R by lra.
        fwd.
        specialize (H0 _ H7). fwd.
        split.
        { eexists. eapply FEIteF; eauto. }
        { intros.
          inversion H17; subst; clear H17; auto.
          rewrite H2 in H22. inversion H22; subst.
          generalize (float_lt_ge_trichotomy_contra _ _ (conj H24 H11')).
          intros; contradiction. } } } }
Qed.

  (* Weakest-precondition calcluation function for fcmd language *)
  Fixpoint fwp (c : fcmd)
           (P : fstate  -> Prop) : fstate -> Prop :=
    match c with
    | FSkip => P
    | FSeq c1 c2 => fwp c1 (fwp c2 P)
    | FAsn v e => (fun fst  =>
                    exists res, fexprD e fst = Some res /\
                           AnyOf
                             (map
                                (fun sbt : singleBoundTerm =>
                                   let '(pred, bound) := bounds_to_formula sbt fst in
                                   pred /\
                                   (forall (val : float) (r : R),
                                       F2OR val = Some r ->
                                       bound r -> P (fstate_set fst v val)))
                                (bound_fexpr e)))
    | FFail => fun fst => False
    | FIte e c1 c2 => (fun fst =>
                        exists res, fexprD e fst = Some res /\
                               (let bs := bound_fexpr e in
                                (maybe_lt0 bs fst -> fwp c1 P fst) /\
                                (maybe_ge0 bs fst -> fwp c2 P fst) /\
                                AnyOf
                                  (map
                                     (fun sbt : singleBoundTerm =>
                                        let '(prem, _) := denote_singleBoundTermNew fst sbt in prem)
                                     bs)))
    end.
  
  Lemma fwp_correct :
    forall c P,
      Hoare_ (fwp c P)
             c
             P.
  Proof.
    intros c.
    induction c; intros; eauto using Hoare__False.
    { eapply Hoare__seq.
      Focus 2.
      eapply IHc2; eauto.
      simpl.
      eapply Hoare__conseq.
      3: eapply IHc1; eauto.
      2: exact (fun _ x => x).
      intros; eassumption.
    }
    { eapply Hoare__skip. }
    { eapply Hoare__bound_asn. }
    { eapply Hoare__bound_ite; eauto. }
  Qed.
