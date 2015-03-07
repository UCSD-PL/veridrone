Require Import Coq.Reals.Rdefinitions.
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


Lemma always_tauto : forall G P, |-- P -> G |-- [] P.
Proof. tlaIntuition. Qed.

Lemma land_lor_distr : forall P Q R,
    P //\\ (Q \\// R) -|- (P //\\ Q) \\// (P //\\ R).
Proof. intros. red; breakAbstraction. intuition. Qed.

Lemma next_inv : forall N I,
  is_st_formula I ->
  (|-- [](N //\\ I) -->> [](N //\\ I //\\ next I)).
Proof.
  intros. breakAbstraction. intuition.
  - apply H1.
  - apply H1.
  - apply next_formula_tl; auto.
    rewrite <- nth_suf_Sn.
    apply H1.
Qed.

Lemma next_inv' : forall G P Q Z,
  is_st_formula Q ->
  (|-- P -->> Q) ->
  (|-- P //\\ next Q -->> Z) ->
  (G |-- []P -->> []Z).
Proof.
  tlaIntuition.
  - apply H1; auto.
    split; auto.
    apply next_formula_tl; auto.
    rewrite <- nth_suf_Sn. auto.
Qed.



Lemma Always_and : forall P Q,
    []P //\\ []Q -|- [](P //\\ Q).
Proof.
  intros. split.
  { breakAbstraction. intros. intuition. }
  { breakAbstraction; split; intros; edestruct H; eauto. }
Qed.

Lemma Always_or : forall P Q,
    []P \\// []Q |-- [](P \\// Q).
Proof. tlaIntuition. Qed.

Lemma Sys_bound_t : forall P dvars cvars Init Prog w d,
    P |-- Sys dvars cvars Init Prog w d -->> []0 <= "t" <= d.
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
    BoundSys dvars cvars Init Prog w d -|- [](0 <= "t" <= d) //\\ Sys dvars cvars Init Prog w d.
Proof. Admitted.

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

Require Import RelationClasses.
Instance Reflexive_all_in {T} : Reflexive (@all_in T).
Proof. red; red; tauto. Qed.



Theorem Sys_weaken : forall dvars dvars' cvars cvars'
                            I I' P P' w w' d d',
  all_in dvars dvars' ->
  all_in cvars cvars' ->
  (|-- I' -->> I) ->
  (|-- "pc" = 1 -->> P' -->> P) ->
  all_in w w' ->
  (d >= d')%R ->
  (Sys dvars' cvars' I' P' w' d' |-- Sys dvars cvars I P w d).
Proof.
  do 12 intro.
  intros Hdvars Hcvars HI HP Hw Hd.
Admitted.

Ltac tlaRevert := first [ apply landAdj | apply lrevert ].

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

(*
Lemma discr_ind' : forall P A Init Inv IndInv N,
    is_st_formula I ->
    (P |-- [] A) ->
    (P |-- Init -->> IndInv) ->
    P |-- IndInv -->> Inv ->
    (A |-- IndInv //\\ N -->> next IndInv) ->
    (P |-- (Init //\\ []N) -->> []Inv).
Proof.
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

Lemma always_st : forall Q,
    is_st_formula Q ->
    [] Q -|- [] (Q //\\ next Q).
Proof. Admitted.


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
      eapply discr_ind'
        with (A:= A//\\0<= "t" <= d //\\ 0 <= "t" ! <= d)
             (N:=(((World dvars w \\// Discr cvars Prog d) \\//
                                                           Unchanged (dvars ++ cvars ++ ["t", "pc"])) //\\ 
                                                                                                      "t" >= 0)).
      * assumption.
      * rewrite Ha. rewrite Always_and.
        rewrite <- Always_and.
        rewrite (always_st (0 <= _ <= _)) by (compute; tauto).
        simpl next.
        repeat rewrite <- Always_and.
        repeat tlaSplit; try tlaAssume.
      * tlaAssume.
      * tlaAssume.
      * rewrite (landC (_ \\// _) _).
        repeat rewrite land_lor_distr. tlaRevert.
        apply or_left; [ apply or_left | ].
        { tlaIntro. rewrite Hw. tlaIntuition. }
        { rewrite Hdiscr. tlaIntuition. }
        { apply forget_prem. red in InvUnder. rewrite InvUnder.
          tlaIntuition. }
  - tlaIntuition.
Qed.