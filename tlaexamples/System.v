Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Classes.RelationClasses.
Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import TLA.ArithFacts.
Import LibNotations.

Open Scope HP_scope.
Open Scope string_scope.

Definition World (dvars : list Var)
           (world : list DiffEq) : Formula :=
  Continuous (("t"'::=--1)::world ++
                          (List.map
                             (fun x => x ' ::= 0) dvars))%list //\\
  "pc" = 0.

Definition Discr (cvars : list Var)
           (Prog : Formula) (d : R) : Formula :=
  Prog //\\ "t"! = d //\\ "pc" = 1 //\\ Unchanged cvars.


Definition Sys (dvars cvars : list Var)
           (Init Prog: Formula) (world : list DiffEq)
           (d : R) : Formula :=
  ("t" <= d //\\ Init) //\\
     [](((     World dvars world
          \\// Discr cvars Prog d)
          \\// Unchanged (dvars++cvars++"t"::"pc"::nil)%list)
          //\\ "t" >= 0).

Definition BoundSys (dvars cvars : list Var)
           (Init Prog: Formula) (world : list DiffEq)
           (d : R) : Formula :=
  ("t" <= d //\\ Init) //\\
     [](((     World dvars world
          \\// Discr cvars Prog d)
          \\// Unchanged (dvars++cvars++"t"::"pc"::nil)%list)
          //\\ 0 <= "t" <= d).

Ltac tlaRevert := first [ apply landAdj | apply lrevert ].

Lemma discr_indX : forall P A IndInv,
    is_st_formula IndInv ->
    P |-- [] A ->
    P |-- IndInv ->
    A //\\ IndInv |-- next IndInv ->
    P |-- []IndInv.
Proof.
  intros.
  intro. simpl; intros.
  specialize (H0 _ H3).
  induction n.
  { simpl. intros; eapply H1. auto. }
  { simpl. rewrite Stream.nth_suf_tl.
    apply next_formula_tl; auto.
    apply H2; auto.
    split; auto. }
Qed.

(*
Lemma discr_ind' : forall P A IndInv N,
    is_st_formula IndInv ->
    P |-- [] A ->
    P |-- IndInv ->
    P |-- [] N ->
    A //\\ IndInv //\\ N |-- next IndInv ->
    P |-- []IndInv.
Proof.
(*
  intros. rewrite H0; clear H0.
  intro. simpl; intros.
  induction n.
  { simpl. tauto. }
  { simpl. rewrite Stream.nth_suf_tl.
    apply next_formula_tl; auto.
    apply H1; auto.
    split; auto. destruct H2. apply H3. }
Qed.
*)
Admitted.
*)


Lemma Sys_bound_t : forall P dvars cvars Init Prog w d,
    P |-- Sys dvars cvars Init Prog w d -->> []0 <= "t" <= d.
Proof.
  intros.

Admitted.

Lemma Sys_BoundSys : forall P dvars cvars Init Prog w d,
    P |-- Sys dvars cvars Init Prog w d -->>
          BoundSys dvars cvars Init Prog w d.
Proof.
  unfold Sys, BoundSys; intros.
  apply limplAdj. tlaSplit; try tlaAssume.
  repeat apply landAdj.
  apply imp_strengthen with (F2:=[]"t"<=d).
  { eapply imp_trans. eapply Sys_bound_t.
    apply always_imp. tlaIntuition. }
  { repeat rewrite curry.
    tlaIntro. tlaIntro. apply forget_prem.
    repeat tlaIntro.
    rewrite Always_and.
    apply lrevert. apply always_imp.
    tlaIntro. solve_linear. }
Qed.

Definition InvariantUnder (vars : list Var) (F : Formula) : Prop :=
  |-- F //\\ Unchanged vars -->> next F.

Lemma BoundSys_def : forall dvars cvars Init Prog w d,
    BoundSys dvars cvars Init Prog w d -|-
    [](0 <= "t" <= d) //\\ Sys dvars cvars Init Prog w d.
Proof.
  intros. unfold BoundSys, Sys.
  symmetry.
  rewrite landC.
  rewrite landA. rewrite Always_and.
  apply land_cancel.
  apply forget_prem.
  apply ltrue_liff.
  repeat rewrite <- Always_and.
  unfold lequiv. split; try charge_tauto.
  repeat tlaSplit; try charge_tauto.
  solve_linear.
Qed.

Definition all_in {T} (l1 l2 : list T) :=
  forall x, List.In x l1 -> List.In x l2.

Theorem all_in_dec_ok : forall (l1 l2 : list Var),
  List.forallb
    (fun x => if List.in_dec String.string_dec x l2
              then true else false) l1 = true ->
  all_in l1 l2.
Proof.
  red. intros.
  rewrite List.forallb_forall in H.
  apply H in H0.
  destruct (List.in_dec String.string_dec x l2);
    auto; discriminate.
Qed.

Instance Reflexive_all_in {T} : Reflexive (@all_in T).
Proof. red; red; tauto. Qed.

Instance Transitive_all_in {T} : Transitive (@all_in T).
Proof. unfold all_in; red; intros. eauto. Qed.

Lemma World_weaken : forall dvars dvars' w w',
    all_in dvars dvars' ->
    all_in w w' ->
    World dvars' w' |-- World dvars w.
Proof.
Admitted.

Lemma Discr_weaken : forall cvars cvars' P P' d d',
    all_in cvars cvars' ->
    |-- "pc" = 1 -->> P' -->> P ->
    (d >= d')%R ->
    Discr cvars' P' d' |-- Discr cvars P d.
Proof.
  unfold Discr. intros.
Abort.

Theorem Sys_weaken : forall dvars dvars' cvars cvars'
                            I I' P P' w w' d d',
  all_in dvars dvars' ->
  all_in cvars cvars' ->
  (|-- I' -->> I) ->
  (|-- "pc" = 1 -->> P' -->> P) ->
  all_in w w' ->
  (d >= d')%R -> (** This weakening is non-trivial for discrete formula **)
  (Sys dvars' cvars' I' P' w' d' |-- Sys dvars cvars I P w d).
Proof.
  do 12 intro.
  intros Hdvars Hcvars HI HP Hw Hd.
  unfold Sys.
  apply lrevert.
  rewrite (rw_impl HI); clear HI.
  tlaIntro.
  repeat tlaSplit; try tlaAssume.
  { do 2 apply landL1. clear - Hd. solve_linear. }
  { tlaRevert.
    apply always_imp. tlaIntro.
    repeat tlaSplit; try tlaAssume.
    rewrite landC. tlaRevert. apply forget_prem.
    tlaIntro.
    erewrite World_weaken by eauto.
    admit. }
Qed.

Theorem sys_by_induction :
  forall P A dvars cvars Init Prog Inv IndInv w (d:R),
  is_st_formula IndInv ->
  (P |-- Init -->> IndInv) ->
  (P |-- [] A) ->
  (A |-- (IndInv //\\ 0 <= "t" <= d) -->> Inv) ->
  InvariantUnder (dvars ++ cvars ++ "t" :: "pc" :: nil)%list IndInv ->
  (A |-- (IndInv //\\ World dvars w) -->> next IndInv) ->
  (A |-- (IndInv //\\ 0 <= "t" <= d //\\ 0 <= "t"! <= d //\\ "pc" = 1
          //\\ Discr cvars Prog d) -->> next IndInv) ->
  (P |-- Sys dvars cvars Init Prog w d -->> [] Inv).
Proof.
  Opaque Continuous.
  intros P A dvars cvars Init Prog Inv IndInv w d
         Hst Hinit Ha Hinv InvUnder Hw Hdiscr.
  rewrite (rw_impl (Sys_BoundSys P _ _ _ _ _ _)).
  rewrite BoundSys_def. rewrite uncurry.
  tlaIntro.
  apply imp_trans with (F2:=[]IndInv).
  - apply imp_trans with (F2:=Sys dvars cvars IndInv Prog w d).
    + unfold Sys. tlaRevert.
      rewrite (rw_impl Hinit); clear Hinit.
      do 2 tlaIntro; tlaAssume.
    + unfold Sys. tlaIntro.
      eapply discr_indX
        with (A:= A//\\0<= "t" <= d //\\ 0 <= "t" ! <= d //\\
                 (((World dvars w \\// Discr cvars Prog d) \\//
                  Unchanged (dvars ++ cvars ++ ["t", "pc"])) //\\ "t" >= 0)).
      * assumption.
      * rewrite Ha. rewrite Always_and.
        rewrite <- Always_and.
        rewrite (always_st (0 <= _ <= _)) by (compute; tauto).
        simpl next.
        repeat rewrite <- Always_and.
        repeat tlaSplit; try tlaAssume.
      * tlaAssume.
      * repeat rewrite (landC (_ \\// _) _).
        repeat rewrite land_lor_distr.
        repeat rewrite (landC (_ \\// _) _).
        repeat rewrite land_lor_distr. tlaRevert.
        apply or_left; [ apply or_left | ].
        { tlaIntro. rewrite Hw. tlaIntuition. }
        { rewrite Hdiscr. tlaIntuition. }
        { apply forget_prem. red in InvUnder. rewrite InvUnder.
          tlaIntuition. }
  - tlaIntuition.
Qed.