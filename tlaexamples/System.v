Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import TLA.ArithFacts.
Require Import TLA.Automation.
Require Import Coq.Lists.ListSet.

Open Scope HP_scope.
Open Scope string_scope.

(* Convenience functions to say that all variables in a list
   have derivative 0. *)
Definition AllConstant (vars : list Var) : Evolution :=
  fun st' => List.fold_right
               (fun x a => st' x = 0 //\\ a)
               TRUE vars.

(* Adds time derivative to an Evolution. *)
Definition mkEvolution (world : Evolution) : Evolution :=
  fun st' => st' "t" = --1 //\\  world st'.

Definition World (world : Evolution) : Formula :=
  Continuous (mkEvolution world).

Definition Discr (Prog : Formula) (d : R) : Formula :=
  Prog //\\ "t"! <= d.

Definition Next (Prog: Formula) (world : Evolution)
           (unch:list Term) (d : R) :=
  let w := World world in
  let d := Discr Prog d in
  let steps := w \\// d
  in      steps
     \\// (Enabled d -->> lfalse)
(*     \\// (Enabled w -->> lfalse) *)
     \\// UnchangedT (("t":Term)::unch)%list.

Definition Next_or_stuck (Prog: Formula) (world : Evolution)
           (unch:list Term) (d : R) :=
  let w := World world in
  let d := Discr Prog d in
  let steps := w \\// d
  in      steps
     \\// UnchangedT (("t":Term)::unch)%list.

Definition sysD (Init Prog: Formula) (world : Evolution)
           (unch : list Term) (d : R) : Formula :=
  ("t" <= d //\\ Init) //\\
     [](Next Prog world unch d //\\ 0 <= "t").

Definition sysD_or_stuck (Init Prog: Formula) (world : Evolution)
           (unch : list Term) (d : R) : Formula :=
  ("t" <= d //\\ Init) //\\
     [](Next_or_stuck Prog world unch d //\\ 0 <= "t").

Record SysRec
: Type := Sys
{ Init : Formula
; Prog : Formula
; world : Evolution
; unch : list Term
; maxTime : R }.

Definition SysD (s : SysRec)
: Formula :=
  sysD s.(Init) s.(Prog) s.(world) s.(unch) s.(maxTime).

Definition SysD_or_stuck (s : SysRec)
: Formula :=
  sysD_or_stuck s.(Init) s.(Prog) s.(world) s.(unch) s.(maxTime).

Definition SysCompose (a b : SysRec) : SysRec :=
{| Init  := a.(Init) //\\ b.(Init)
 ; Prog  := a.(Prog) //\\ b.(Prog)
 ; world := fun st' => a.(world) st' //\\ b.(world) st'
 ; unch := a.(unch) ++ b.(unch)
 ; maxTime := Rmin a.(maxTime) b.(maxTime)
 |}.

Definition SysRename (m : list (Var * Term)) (s : SysRec)
  : SysRec :=
  {| Init := Rename m s.(Init)
   ; Prog := Rename m s.(Prog)
   ; world := fun st' => Rename m (s.(world) st')
   ; unch := List.map (rename_term m) s.(unch)
   ; maxTime := s.(maxTime)
  |}.

Definition SysSafe (a : SysRec) : Formula :=
  SysD a -->> SysD_or_stuck a.

Definition SysRec_equiv (a b : SysRec) : Prop :=
  a.(unch) = b.(unch) /\
  (a.(Init) -|- b.(Init)) /\
  (a.(Prog) -|- b.(Prog)) /\
  (forall st', (a.(world) st' -|- b.(world) st')) /\
  a.(maxTime) = b.(maxTime).

Lemma Proper_Enabled :
  Proper (lequiv ==> lequiv) Enabled.
Proof.
  red. red. unfold lequiv, lentails. simpl.
  unfold tlaEntails. simpl. intros. split.
  { intros. destruct H0. exists x0. intuition. }
  { intros. destruct H0. exists x0. intuition. }
Qed.

Lemma Proper_Always :
  Proper (lequiv ==> lequiv) Always.
Proof.
  red. red. unfold lequiv, lentails. simpl.
  intuition. restoreAbstraction. tlaRevert. apply always_imp.
  charge_tauto.
  restoreAbstraction. tlaRevert.
  apply always_imp. charge_tauto.
Qed.

Existing Instance Proper_Always.

Existing Instance Proper_Enabled.

 Lemma worldImp : forall x y x0 x1, (forall st' : state, world x st' -|- world y st') -> (is_solution x1 (mkEvolution (world x)) x0 <-> is_solution x1 (mkEvolution (world y)) x0).
      intros.
      unfold mkEvolution in *.
      split.
      {
        intros.
        unfold is_solution,solves_diffeqs in *.
        destruct H0.
        exists x2.
        intros.
        specialize (H0 z H1).
        simpl in *.
        decompose [and] H0.
        split.
        { intuition. }
        {  
          specialize (H (fun x3 : Var =>
             Ranalysis1.derive (fun t : R => x1 t x3) (x2 x3) z)).
          destruct H.
          simpl in *.
          unfold tlaEntails in *.
          specialize (H (Stream.forever (x1 z)) H3).
          intuition.
        }
      }
      {
        intros.
        unfold is_solution,solves_diffeqs in *.
        destruct H0.
        exists x2.
        intros.
        specialize (H0 z H1).
        simpl in *.
        decompose [and] H0.
        split.
        { intuition. }
        {  
          specialize (H (fun x3 : Var =>
             Ranalysis1.derive (fun t : R => x1 t x3) (x2 x3) z)).
          destruct H.
          simpl in *.
          unfold tlaEntails in *.
          specialize (H4 (Stream.forever (x1 z)) H3).
          intuition.
        }
      }
    Qed.
 
   Lemma simplImp : forall x y (tr:  Stream.stream (String.string -> R)) n, (Prog x -|- Prog y) -> (maxTime x = maxTime y) ->
                                                                                         ( (exists tr' : Stream.stream state,
                                                                                               eval_formula (Prog y) (Stream.Cons (Stream.hd (Stream.nth_suf n tr)) tr') /\ (Stream.hd tr' "t" <= maxTime y)%R) <-> 
                                                                                           (exists tr' : Stream.stream state,
                                                                                               eval_formula (Prog x) (Stream.Cons (Stream.hd (Stream.nth_suf n tr)) tr') /\ (Stream.hd tr' "t" <= maxTime x)%R)).
                Proof.
                  intros.
                  destruct H.
                  simpl in H,H1.
                  unfold tlaEntails in H,H1.
                  split.
                  {
                    intros.
                    destruct H2.
                    exists x0.
                    decompose [and] H2.
                    specialize (H1 (Stream.Cons (Stream.hd (Stream.nth_suf n tr)) x0) H3).
                    split.
                    {
                      intuition.
                    }
                    {
                      rewrite H0.
                      intuition.
                    }
                  }
                  {
                    intros.
                    {
                      destruct H2.
                      {
                        exists x0.
                        decompose [and] H2.
                        specialize (H (Stream.Cons (Stream.hd (Stream.nth_suf n tr)) x0) H3).
                        split.
                        {
                          intuition.
                        }
                        {
                          rewrite <-H0.
                          intuition.
                        }
                      }
                    }
                  }
                Qed.
    Lemma assist2 : forall x y tr, 
        (unch x = unch y /\
         (Init x -|- Init y) /\
         (Prog x -|- Prog y) /\
         (forall st' : state, world x st' -|- world y st') /\
         maxTime x = maxTime y) -> (
(((Stream.hd tr "t" <= maxTime x)%R /\ eval_formula (Init x) tr) /\
       (forall n : nat,
        (((exists (x0 : R) (x1 : R -> state),
             (x0 > 0)%R /\
             is_solution x1 (mkEvolution (world x)) x0 /\
             x1 0%R = Stream.hd (Stream.nth_suf n tr) /\
             x1 x0 = Stream.hd (Stream.tl (Stream.nth_suf n tr))) \/
          eval_formula (Prog x) (Stream.nth_suf n tr) /\
          (Stream.hd (Stream.tl (Stream.nth_suf n tr)) "t" <= maxTime x)%R) \/
         ((exists tr' : Stream.stream state,
             eval_formula (Prog x)
               (Stream.Cons (Stream.hd (Stream.nth_suf n tr)) tr') /\
             (Stream.hd tr' "t" <= maxTime x)%R) -> False) \/
         Stream.hd (Stream.tl (Stream.nth_suf n tr)) "t" =
         Stream.hd (Stream.nth_suf n tr) "t" /\
         eval_formula (UnchangedT (unch x)) (Stream.nth_suf n tr)) /\
        (0 <= Stream.hd (Stream.nth_suf n tr) "t")%R)) ->
          
          ((Stream.hd tr "t" <= maxTime y)%R /\ eval_formula (Init y) tr) /\
       (forall n : nat,
        (((exists (x0 : R) (x1 : R -> state),
             (x0 > 0)%R /\
             is_solution x1 (mkEvolution (world y)) x0 /\
             x1 0%R = Stream.hd (Stream.nth_suf n tr) /\
             x1 x0 = Stream.hd (Stream.tl (Stream.nth_suf n tr))) \/
          eval_formula (Prog y) (Stream.nth_suf n tr) /\
          (Stream.hd (Stream.tl (Stream.nth_suf n tr)) "t" <= maxTime y)%R) \/
         ((exists tr' : Stream.stream state,
             eval_formula (Prog y)
               (Stream.Cons (Stream.hd (Stream.nth_suf n tr)) tr') /\
             (Stream.hd tr' "t" <= maxTime y)%R) -> False) \/
         Stream.hd (Stream.tl (Stream.nth_suf n tr)) "t" =
         Stream.hd (Stream.nth_suf n tr) "t" /\
         eval_formula (UnchangedT (unch y)) (Stream.nth_suf n tr)) /\
        (0 <= Stream.hd (Stream.nth_suf n tr) "t")%R))   .
    Proof.
      intros.
      decompose [and] H.
      decompose [and] H0.
      split.
      {
        split.
        rewrite <- H6.
        intuition.
        destruct H3.
        simpl in *.
        unfold tlaEntails in *.
        specialize (H3 tr H9).
        intuition.
      }
      {
        intros.
        split.
        {
          specialize (H7 n).
          decompose [and] H7.
          destruct H5.
          {
            constructor 1.
            destruct H5.
            {
              constructor 1.
              destruct H5.
              destruct H5.
              exists x0. 
              exists x1.
              decompose [and] H5.
              split.
              {
                intuition.
              }
              {
                split.
                {
                  pose proof worldImp.
                  specialize (H14 x y x0 x1 H4).
                  destruct H14.
                  specialize (H14 H13).
                  intuition.
                }
                {
                  split.
                  {
                    intuition.
                  }
                  {
                    intuition.
                  }
                }
              }
            }
            {
              constructor 2.
              decompose [and] H5.
              split.
              {
                destruct H2.
                simpl in H2,H13.
                unfold tlaEntails in H2,H3.
                specialize (H2 (Stream.nth_suf n tr) H11).
                intuition.
              }
              {
                rewrite <- H6. 
                intuition.
              }
            }
          }
          {
            constructor 2.
            destruct H5.
            {
              constructor 1.
              {
               
                intros.
                Lemma imp2 : forall x y,( x <-> y) -> (y -> False) -> (x -> False).
                  intuition.
                Qed.
                pose proof imp2.
                pose proof simplImp.
                specialize (H13 x y tr n H2 H6).
                SearchAbout ((_ <-> _) -> (_<->_)).
                
                specialize (H12  
                              (exists tr' : Stream.stream state,   eval_formula (Prog y) (Stream.Cons (Stream.hd (Stream.nth_suf n tr)) tr') /\ (Stream.hd tr' "t" <= maxTime y)%R)  (exists tr' : Stream.stream state, eval_formula (Prog x) (Stream.Cons (Stream.hd (Stream.nth_suf n tr)) tr') /\ (Stream.hd tr' "t" <= maxTime x)%R) H13 H5 H11).
                intuition.
              }
            }
            {
              constructor 2.
              rewrite <- H1.
              intuition.
            }
          }
        }
        {
          specialize (H7 n).
          decompose [and] H7.
          intuition.
        }
      }
    Qed.
     Lemma imp : forall x y,( x <-> y) -> (x -> False) -> (y -> False).
                  intuition.
                Qed.
              
    Lemma assist : forall x y tr, 
        (unch x = unch y /\
         (Init x -|- Init y) /\
         (Prog x -|- Prog y) /\
         (forall st' : state, world x st' -|- world y st') /\
         maxTime x = maxTime y) -> (((Stream.hd tr "t" <= maxTime y)%R /\ eval_formula (Init y) tr) /\
       (forall n : nat,
        (((exists (x0 : R) (x1 : R -> state),
             (x0 > 0)%R /\
             is_solution x1 (mkEvolution (world y)) x0 /\
             x1 0%R = Stream.hd (Stream.nth_suf n tr) /\
             x1 x0 = Stream.hd (Stream.tl (Stream.nth_suf n tr))) \/
          eval_formula (Prog y) (Stream.nth_suf n tr) /\
          (Stream.hd (Stream.tl (Stream.nth_suf n tr)) "t" <= maxTime y)%R) \/
         ((exists tr' : Stream.stream state,
             eval_formula (Prog y)
               (Stream.Cons (Stream.hd (Stream.nth_suf n tr)) tr') /\
             (Stream.hd tr' "t" <= maxTime y)%R) -> False) \/
         Stream.hd (Stream.tl (Stream.nth_suf n tr)) "t" =
         Stream.hd (Stream.nth_suf n tr) "t" /\
         eval_formula (UnchangedT (unch y)) (Stream.nth_suf n tr)) /\
        (0 <= Stream.hd (Stream.nth_suf n tr) "t")%R) -> ((Stream.hd tr "t" <= maxTime x)%R /\ eval_formula (Init x) tr) /\
       (forall n : nat,
        (((exists (x0 : R) (x1 : R -> state),
             (x0 > 0)%R /\
             is_solution x1 (mkEvolution (world x)) x0 /\
             x1 0%R = Stream.hd (Stream.nth_suf n tr) /\
             x1 x0 = Stream.hd (Stream.tl (Stream.nth_suf n tr))) \/
          eval_formula (Prog x) (Stream.nth_suf n tr) /\
          (Stream.hd (Stream.tl (Stream.nth_suf n tr)) "t" <= maxTime x)%R) \/
         ((exists tr' : Stream.stream state,
             eval_formula (Prog x)
               (Stream.Cons (Stream.hd (Stream.nth_suf n tr)) tr') /\
             (Stream.hd tr' "t" <= maxTime x)%R) -> False) \/
         Stream.hd (Stream.tl (Stream.nth_suf n tr)) "t" =
         Stream.hd (Stream.nth_suf n tr) "t" /\
         eval_formula (UnchangedT (unch x)) (Stream.nth_suf n tr)) /\
        (0 <= Stream.hd (Stream.nth_suf n tr) "t")%R)) .
    Proof.
      intros.
      decompose [and] H.
      decompose [and] H0.
      split.
      {
        split.
        rewrite H6.
        intuition.
        destruct H3.
        simpl in *.
        unfold tlaEntails in *.
        specialize (H5 tr H9).
        intuition.
      }
      {
        intros.
        split.
        {
          specialize (H7 n).
          decompose [and] H7.
          destruct H5.
          {
            constructor 1.
            destruct H5.
            {
              constructor 1.
              destruct H5.
              destruct H5.
              exists x0. 
              exists x1.
              decompose [and] H5.
              split.
              {
                intuition.
              }
              {
                split.
                {
                  pose proof worldImp.
                  specialize (H14 x y x0 x1 H4).
                  destruct H14.
                  specialize (H16 H13).
                  intuition.
                }
                {
                  split.
                  {
                    intuition.
                  }
                  {
                    intuition.
                  }
                }
              }
            }
            {
              constructor 2.
              decompose [and] H5.
              split.
              {
                destruct H2.
                simpl in H2,H13.
                unfold tlaEntails in H2,H3.
                specialize (H13 (Stream.nth_suf n tr) H11).
                intuition.
              }
              {
                rewrite H6. 
                intuition.
              }
            }
          }
          {
            constructor 2.
            destruct H5.
            {
              constructor 1.
              {
               
                intros.
                pose proof imp.
                pose proof simplImp.
                specialize (H13 x y tr n H2 H6).
                SearchAbout ((_ <-> _) -> (_<->_)).
                specialize (H12  
                              (exists tr' : Stream.stream state,   eval_formula (Prog y) (Stream.Cons (Stream.hd (Stream.nth_suf n tr)) tr') /\ (Stream.hd tr' "t" <= maxTime y)%R)  (exists tr' : Stream.stream state, eval_formula (Prog x) (Stream.Cons (Stream.hd (Stream.nth_suf n tr)) tr') /\ (Stream.hd tr' "t" <= maxTime x)%R) H13 H5 H11).
                intuition.
              }
            }
            {
              constructor 2.
              rewrite H1.
              intuition.
            }
          }
        }
        {
          specialize (H7 n).
          decompose [and] H7.
          intuition.
        }
      }
    Qed.


Lemma Proper_SysSafe :
  Proper (SysRec_equiv ==> lequiv) SysSafe.
Proof.
  red. red. unfold SysSafe. intros. red in H.
  unfold SysD, SysD_or_stuck, sysD, sysD_or_stuck, Next,
  Next_or_stuck, World, Continuous.
  decompose [and] H. destruct H1. destruct H2. 
  
  (* 
  unfold Prog in *.
  simpl in H1.
  inversion H1.
  simpl in H0,H2.
  unfold tlaEntails in H0,H2.*)
  
  split.
  {
    breakAbstraction.
    intros. 
    intros.
    intros.
    pose proof assist.
    specialize (H9 x y tr H H8).
    specialize (H7 H9).
    revert H7.      
    intros.
    decompose [and] H7.
    {
      split.
      {
        intuition.
      }
      {
        intros.
        specialize (H11 n).
        decompose [and] H11.
        split.
        {
          destruct H10.
          {
            constructor 1.
            destruct H10.
            {
              constructor 1.
              destruct H10.
              destruct H10.
              exists x0.
              exists x1.
              decompose [and] H10. 
              split.
              {
                intuition.
              }
              {
                split.
                {
                  pose proof worldImp.
                  specialize (H18 x y x0 x1 H3).
                  destruct H18.
                  specialize (H18 H17).
                  intuition.
                }
                {
                  split.
                  {
                    intuition.
                  }
                  {
                    intuition.
                  }
                }
              }
            }
            {
              constructor 2.
              rewrite <- H5.
              intuition.
            }
          }
          {
            constructor 2.
            {
              rewrite <- H0.
              intuition.
            }
          }
        }
        {
          intuition.
        }
      }
    }
  }
  {
    breakAbstraction.
    intros.
    pose proof assist2.
    specialize (H9 x y tr H H8).
    specialize (H7 H9).
    revert H7.      
    intros.
    decompose [and] H7.
    {
      split.
      {
        intuition.
      }
      {
        intros.
        specialize (H11 n).
        decompose [and] H11.
        split.
        {
          destruct H10.
          {
            constructor 1.
            destruct H10.
            {
              constructor 1.
              destruct H10.
              destruct H10.
              exists x0.
              exists x1.
              decompose [and] H10. 
              split.
              {
                intuition.
              }
              {
                split.
                {
                  pose proof worldImp.
                  specialize (H18 x y x0 x1 H3).
                  destruct H18.
                  specialize (H20 H17).
                  intuition.
                }
                {
                  split.
                  {
                    intuition.
                  }
                  {
                    intuition.
                  }
                }
              }
            }
            {
              constructor 2.
              rewrite  H5.
              intuition.
            }
          }
          {
            constructor 2.
            {
              rewrite H0.
              intuition.
            }
          }
        }
        {
          intuition.
        }
      }
    }
  }
  Qed.

Existing Instance Proper_Safe.

(*Ltac tlaRevert := first [ apply landAdj | apply lrevert ]. *)

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

Lemma Always_now : forall P I,
  P |-- []I ->
  P |-- I.
Proof.
  breakAbstraction.
  intros P I H tr HP.
  apply (H tr HP 0).
Qed.

Require Import ChargeTactics.Lemmas.

Ltac decompose_hyps :=
  repeat rewrite land_lor_distr_R;
  repeat rewrite land_lor_distr_L;
  repeat apply lorL.

Definition TimeBound d : Formula := 0 <= "t" <= d.

Lemma mkEvolution_st_formula :
  forall w,
    (forall st : state, is_st_formula (w st)) ->
    forall st : state, is_st_formula (mkEvolution w st).
Proof.
  simpl. intros. intuition.
Qed.

Lemma Sys_bound_t : forall P (a : SysRec),
    (forall st, is_st_formula (a.(world) st)) ->
    forall Hsafe : P |-- SysSafe a,
    P |-- SysD a ->
    P |-- []TimeBound a.(maxTime).
Proof.
  intros.
  unfold SysSafe in *.
  assert (P |-- SysD_or_stuck a).
  { charge_apply Hsafe. charge_split. reflexivity. assumption. }
  clear - H1 H. rename H1 into H0.
  unfold SysD in *.
  rewrite <- Always_and with (P:=0 <= "t") (Q:="t" <= a.(maxTime)).
  tlaSplit.
  - rewrite H0. unfold SysD_or_stuck, sysD_or_stuck, sysD.
    rewrite <- Always_and. tlaAssume.
  - apply discr_indX
    with (A:=Next_or_stuck a.(Prog) a.(world)
                  a.(unch) a.(maxTime)).
    + tlaIntuition.
    + rewrite H0.
      unfold SysD_or_stuck,sysD_or_stuck,Next_or_stuck,sysD,Next.
      rewrite <- Always_and. tlaAssume.
    + rewrite H0. unfold sysD. tlaAssume.
    + unfold Next_or_stuck. decompose_hyps.
      * pose proof (mkEvolution_st_formula a.(world)).
        specialize (H1 H). clear H.
        eapply diff_ind with (Hyps:=TRUE);
        try solve [tlaIntuition].
        { unfold World. tlaAssume. }
        { apply H1. }
        { solve_linear. }
      * solve_linear.
      * solve_linear.
Qed.

Definition InvariantUnder (unch : list Term)
           (F : Formula) : Prop :=
  F //\\ UnchangedT unch |-- next F.

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

Lemma VarsAgree_val : forall x xs s,
  List.In x xs ->
  VarsAgree xs s |-- x = (s x).
Proof.
  induction xs.
  - tlaIntuition.
  - intros. simpl in H. destruct H.
    + subst a. charge_assumption.
    + rewrite <- IHxs.
      * charge_assumption.
      * auto.
Qed.

Lemma VarsAgree_weaken : forall xs xs' s,
  all_in xs xs' ->
  VarsAgree xs' s |-- VarsAgree xs s.
Proof.
  induction xs.
  - tlaIntuition.
  - intros. simpl VarsAgree. restoreAbstraction.
    rewrite <- VarsAgree_val with (x:=a) (xs:=xs').
    + charge_split.
      * charge_tauto.
      * rewrite IHxs; try charge_tauto.
        unfold all_in in *. intuition.
    + intuition.
Qed.

Lemma VarsAgree_app : forall xs1 xs2 s,
  VarsAgree (xs1 ++ xs2) s -|-
  VarsAgree xs1 s //\\ VarsAgree xs2 s.
Proof.
  induction xs1; intros.
  - tlaIntuition. split; charge_tauto.
  - simpl VarsAgree. restoreAbstraction.
    rewrite IHxs1. split; charge_tauto.
Qed.

Lemma AVarsAgree_val : forall x xs s,
  List.In x xs ->
  AVarsAgree xs s |-- x! = (s x).
Proof.
  induction xs.
  - tlaIntuition.
  - intros. simpl in H. destruct H.
    + subst a. charge_assumption.
    + rewrite <- IHxs.
      * charge_assumption.
      * auto.
Qed.

Lemma AVarsAgree_weaken : forall xs xs' s,
  all_in xs xs' ->
  AVarsAgree xs' s |-- AVarsAgree xs s.
Proof.
  induction xs.
  - tlaIntuition.
  - intros. simpl AVarsAgree. restoreAbstraction.
    rewrite <- AVarsAgree_val with (x:=a) (xs:=xs').
    + charge_split.
      * charge_tauto.
      * rewrite IHxs; try charge_tauto.
        unfold all_in in *. intuition.
    + intuition.
Qed.

Lemma AVarsAgree_app : forall xs1 xs2 s,
  AVarsAgree (xs1 ++ xs2) s -|-
  AVarsAgree xs1 s //\\ AVarsAgree xs2 s.
Proof.
  induction xs1; intros.
  - tlaIntuition. split; charge_tauto.
  - simpl AVarsAgree. restoreAbstraction.
    rewrite IHxs1. split; charge_tauto.
Qed.

Lemma exists_entails : forall T F1 F2,
  (forall x, F1 x |-- F2 x) ->
  Exists x : T, F1 x |-- Exists x : T, F2 x.
Proof.
  tlaIntuition.  destruct H0.
  exists x. intuition.
Qed.

Lemma all_in_map : forall A B (l l':list A) (f:A->B),
  all_in l l' ->
  all_in (List.map f l) (List.map f l').
Proof.
  unfold all_in; simpl; intros.
  apply List.in_map_iff.
  apply List.in_map_iff in H0. destruct H0.
  exists x0. intuition.
Qed.

Lemma World_weaken : forall w w',
    (forall st', w' st' |-- w st') ->
    World w' |-- World w.
Proof.
  intros.
  unfold World,Continuous.
  Print World.
  Print Continuous.
  Print is_solution.
  Print solves_diffeqs.
  repeat (apply exists_entails; intros).
  repeat charge_split; try solve [tlaAssume].
  breakAbstraction; unfold is_solution; intros;
    intuition.
    match goal with
    | [ H : context[solves_diffeqs] |- _ ]
        => let pf := fresh "pf" in
           let Hcont := fresh "Hcont" in
           destruct H as [pf Hcont]; exists pf
    end.
    unfold solves_diffeqs in *; intros.
    specialize (Hcont z H0).
    unfold mkEvolution in *.
    simpl in *.
    decompose [and] Hcont.
    split.
    { intuition. }
    { specialize (H (fun x1 : Var =>
             Ranalysis1.derive (fun t : R => x0 t x1) (pf x1) z) (Stream.forever (x0 z))).
      intuition.
    }
    Qed.
(*
    erewrite Hcont; eauto.
    simpl in *; intuition. right.
    apply List.in_or_app.
    match goal with
    | [ H : _ |- _ ]
      => apply List.in_app_or in H
    end; intuition. right.
    apply List.in_map_iff.
    match goal with
    | [ H : _ |- _ ]
      => let x := fresh "x" in
         apply List.in_map_iff in H;
           destruct H as [x ?]; exists x
    end; intuition.
  - fold VarsAgree. simpl VarsAgree.
    repeat rewrite List.map_app with (f:=get_var).
    repeat rewrite VarsAgree_app. charge_split.
    + erewrite VarsAgree_weaken with (xs:=List.map get_var w).
      * tlaIntuition.
      * apply all_in_map; auto.
    + erewrite VarsAgree_weaken with
      (xs:=List.map get_var
                    (List.map (fun x1 : Var => x1 '  ::= 0)
                              dvars0))
        (xs':=List.map get_var
                       (List.map (fun x1 : Var => x1 '  ::= 0)
                                 dvars')).
      * tlaIntuition.
      * repeat apply all_in_map; auto.
  - fold AVarsAgree. simpl AVarsAgree.
    repeat rewrite List.map_app with (f:=get_var).
    repeat rewrite AVarsAgree_app. charge_split.
    + erewrite AVarsAgree_weaken with (xs:=List.map get_var w).
      * tlaIntuition.
      * apply all_in_map; auto.
    + erewrite AVarsAgree_weaken with
      (xs:=List.map get_var
                    (List.map (fun x1 : Var => x1 '  ::= 0)
                              dvars0))
        (xs':=List.map get_var
                       (List.map (fun x1 : Var => x1 '  ::= 0)
                                 dvars')).
      * tlaIntuition.
      * repeat apply all_in_map; auto.
*)
Qed.

Lemma Unchanged_In : forall ls l,
    List.In l ls ->
    Unchanged ls |-- l! = l.
Proof.
  induction ls; simpl.
  { inversion 1. }
  { intros. destruct H; restoreAbstraction.
    { subst. charge_tauto. }
    { rewrite IHls; eauto. charge_tauto. } }
Qed.

Lemma UnchangedT_In : forall ls l,
    List.In l ls ->
    UnchangedT ls |-- next_term l = l.
Proof.
  induction ls; simpl.
  { inversion 1. }
  { intros. destruct H; restoreAbstraction.
    { subst. charge_tauto. }
    { rewrite IHls; eauto. charge_tauto. } }
Qed.

Lemma Unchanged_weaken : forall vars' vars,
    all_in vars' vars ->
    Unchanged vars |-- Unchanged vars'.
Proof.
  induction vars'.
  { intros. tlaIntuition. }
  { intros. red in H.
    simpl. restoreAbstraction.
    tlaSplit.
    { apply Unchanged_In. apply H. left. reflexivity. }
    { eapply IHvars'. red. intros. eapply H. right. assumption. } }
Qed.

Lemma UnchangedT_weaken : forall unch' unch,
    all_in unch' unch ->
    UnchangedT unch |-- UnchangedT unch'.
Proof.
  induction unch'.
  { intros. tlaIntuition. }
  { intros. red in H.
    simpl. restoreAbstraction.
    tlaSplit.
    { apply UnchangedT_In. apply H. left. reflexivity. }
    { eapply IHunch'. red. intros. eapply H. right. assumption. } }
Qed.

Lemma Discr_weaken : forall P P' d d',
    P' |-- P ->
    (d >= d')%R ->
    Discr P' d' |-- Discr P d.
Proof.
  unfold Discr. intros. rewrite H. solve_linear.
Qed.

Theorem Sys_weaken : forall I I' P P' w w' unch unch' d d',
  forall Hsafe : |-- SysSafe (Sys I' P' w' unch' d'),
  I' |-- I ->
  P' |-- P ->
  (forall st', w' st' |-- w st') ->
  all_in unch unch' ->
  (d >= d')%R ->
  SysD (Sys I' P' w' unch' d') |--
  SysD (Sys I P w unch d).
Proof.
  do 11 intro.
  intros HI HP Hw Hunch Hd.
  unfold SysSafe in Hsafe. apply landAdj in Hsafe.
  rewrite landtrueL in Hsafe.
  rewrite Hsafe.
  unfold SysD, sysD, Init, Next, SysD_or_stuck,
  sysD_or_stuck, Next_or_stuck;
    simpl.
  restoreAbstraction.
  apply lrevert.
  rewrite HI; clear HI.
  tlaIntro.
  repeat tlaSplit; try tlaAssume.
  { do 2 apply landL1. clear - Hd. solve_linear. }
  { tlaRevert.
    apply always_imp. tlaIntro.
    repeat tlaSplit; try tlaAssume.
    rewrite landC. tlaRevert. apply forget_prem.
    tlaIntro. unfold Next.
    erewrite Discr_weaken at 1 by eauto.
    erewrite World_weaken at 1 by eauto.
    erewrite UnchangedT_weaken at 1 by eauto.
    decompose_hyps; charge_tauto. }
Qed.

Ltac sys_apply_with_weaken H :=
  eapply imp_trans; [ | apply H ];
  eapply Sys_weaken;
  try solve [ apply all_in_dec_ok ; reflexivity
            | apply imp_id
            | reflexivity ].

Theorem Sys_by_induction :
  forall P A Init Prog Inv IndInv w unch (d:R),
  is_st_formula IndInv ->
  P |-- SysD (Sys Init Prog w unch d) ->
  (forall st', is_st_formula (w st')) ->
  forall Hsafe : P |-- SysSafe (Sys Init Prog w unch d),
  P //\\ Init |-- IndInv ->
  P |-- [] A ->
  A //\\ IndInv //\\ TimeBound d |-- Inv ->
  InvariantUnder (("t":Term)::unch)%list IndInv ->
  A //\\ IndInv //\\ TimeBound d //\\ next (TimeBound d)
    //\\ World w |-- next IndInv ->
  A //\\ IndInv //\\ TimeBound d //\\ next (TimeBound d)
          //\\ Discr Prog d |-- next IndInv ->
  P |-- [] Inv.
Proof.
  intros P A Init Prog Inv IndInv w unch d
         Hst Hsys Hstw Hsafe Hinit Ha Hinv InvUnder Hw Hdiscr.
  tlaAssert ([]TimeBound d).
  - change d with (maxTime {|
               Init := Init;
               Prog := Prog;
               world := w;
               unch := unch;
               maxTime := d |}).
    eapply Sys_bound_t;
      [ assumption | assumption | rewrite Hsys; tlaAssume ].
  - tlaIntro. tlaAssert ([]IndInv).
    + tlaAssert ([]A); [rewrite Ha; tlaAssume | tlaIntro ].
      tlaAssert (SysD_or_stuck (Sys Init Prog w unch d));
        [ | tlaIntro ].
      { unfold SysSafe in Hsafe. charge_apply Hsafe.
        charge_split; try charge_tauto. }
      apply discr_indX with
      (A:=Next_or_stuck Prog w unch d //\\
               TimeBound d //\\ next (TimeBound d) //\\ A).
        { assumption. }
        { unfold SysD_or_stuck, sysD_or_stuck, Next_or_stuck. simpl.
          restoreAbstraction.
          repeat rewrite <- Always_and.
          repeat tlaSplit.
          - tlaAssume.
          - tlaAssume.
          - rewrite always_st with (Q:=TimeBound d);
            (unfold TimeBound; simpl next;
            repeat rewrite <- Always_and; charge_tauto)
            || tlaIntuition.
          - rewrite always_st with (Q:=TimeBound d);
            (unfold TimeBound; simpl next;
            repeat rewrite <- Always_and; charge_tauto)
            || tlaIntuition.
          - tlaAssume. }
        { rewrite <- Hinit. unfold SysD. charge_tauto. }
        { unfold Next_or_stuck. decompose_hyps.
          - rewrite <- Hw. charge_tauto.
          - rewrite <- Hdiscr. charge_tauto.
          - unfold InvariantUnder in *. rewrite <- InvUnder.
            charge_tauto. }
    + rewrite Ha. tlaRevert. tlaRevert.
      repeat rewrite <- uncurry. repeat rewrite Always_and.
      apply always_imp. charge_intros. rewrite <- Hinv.
      charge_tauto.
Qed.

(** TODO: move this **)
Lemma charge_and_use : forall P Q C,
    C |-- P ->
    C //\\ P |-- Q ->
    C |-- P //\\ Q.
Proof.
  intros. charge_tauto.
Qed.

(*
Section ComposeDiscrete.

  Variable Is : Formula.
  Variable Ic : Formula.
  Variable dvars : list Var.
  Variable cvars : list Var.
  Variable w : list DiffEq.
  Variable WC : Formula.
  Variable d : R.
  Variable S : Formula.
  Variable C : Formula.
  Variable P : Formula.
  Variable E : Formula.

  Theorem compose_discrete :
        |-- SysD (Sys dvars cvars Is S w WC d) -->> []E ->
    []E |-- SysD (Sys dvars cvars Ic C w WC d) -->> []P ->
    |-- SysD (Sys dvars cvars (Is //\\ Ic) (S //\\ C) w WC d) -->>
        [](P //\\ E).
  Proof.
    intros.
    rewrite <- Always_and.
    tlaIntro. rewrite (landC ([]P) ([]E)). apply charge_and_use.
    { charge_apply H.
      eapply Sys_weaken; try reflexivity.
      charge_tauto. charge_tauto. }
    { charge_apply H0. charge_split; try charge_tauto.
      erewrite Sys_weaken;
        try first [ charge_assumption |
                    reflexivity |
                    charge_tauto ]. }
  Qed.

End ComposeDiscrete.
*)

(*
Section ComposeWorld.

  Variable Iw : Formula.
  Variable Id : Formula.
  Variable dvars : list Var.
  Variable cvars : list Var.
  Variable w : list DiffEq.
  Variable WC : Formula.
  Variable d : R.
  Variable D : Formula.
  Variable P : Formula.
  Variable E : Formula.


  Theorem compose_world :
        |-- SysD (Sys dvars cvars Iw ltrue w WC d) -->> []E ->
    []E |-- SysD (Sys dvars cvars Id D w ltrue d) -->> []P ->
    |-- SysD (Sys dvars cvars (Iw //\\ Id) D w WC d) -->>
        [](P //\\ E).
  Proof.
    intros.
    rewrite <- Always_and.
    tlaIntro. rewrite (landC ([]P) ([]E)). apply charge_and_use.
    { charge_apply H.
      eapply Sys_weaken; try reflexivity.
      charge_tauto. charge_tauto. }
    { charge_apply H0. charge_split; try charge_tauto.
      erewrite Sys_weaken;
        try first [ charge_assumption |
                    reflexivity |
                    charge_tauto ]. }
  Qed.

End ComposeWorld.
*)

Theorem Enabled_and (A B : Formula) :
  Enabled (A //\\ B) |-- Enabled A //\\ Enabled B.
Proof.
  breakAbstraction. intros. split; destruct H;
  exists x; tauto.
Qed.

Theorem Enabled_imp (A B : Formula) :
  A |-- B ->
  Enabled A |-- Enabled B.
Proof.
  breakAbstraction. intros. destruct H0.
  eauto.
Qed.

Theorem ComposeRefine (a b : SysRec) :
  forall Hsafe : |-- SysSafe (SysCompose a b),
  SysD (SysCompose a b) |-- SysD a.
Proof.
  intro.
  unfold SysSafe in Hsafe. apply landAdj in Hsafe.
  rewrite landtrueL in Hsafe. rewrite Hsafe.
  unfold SysCompose, SysD_or_stuck, SysD, sysD_or_stuck,
  sysD, Next_or_stuck, Next.
  simpl. restoreAbstraction.
  repeat rewrite <- Always_and.
  repeat charge_split; try charge_tauto.
  { tlaAssert (Rmin (maxTime a) (maxTime b) <= maxTime a);
    [ solve_linear; apply Rmin_l | tlaIntro ].
    - solve_linear. }
  { tlaRevert. apply forget_prem.
    charge_intros.
    rewrite Always_and.
    tlaRevert. apply always_imp.
    charge_intros. decompose_hyps.
    - apply lorR1. apply lorR1.
      rewrite World_weaken.
      + charge_tauto.
      + intros. charge_tauto.
    - apply lorR1. apply lorR2.
      unfold Discr. repeat charge_split; try charge_tauto.
      + tlaAssert (Rmin (maxTime a) (maxTime b) <= maxTime a);
        [ solve_linear; apply Rmin_l | tlaIntro ].
        solve_linear.
    - apply lorR2. apply lorR2.
      charge_split; try charge_tauto.
      rewrite UnchangedT_weaken.
      + charge_tauto.
      + unfold all_in. intros. apply List.in_or_app.
        tauto. }
Qed.

Theorem ComposeComm (a b : SysRec) :
  SysD (SysCompose a b) |-- SysD (SysCompose b a).
Proof.
  intros. unfold SysCompose, SysD, sysD, Next.
  simpl. restoreAbstraction.
  repeat rewrite <- Always_and.
  repeat charge_split; try charge_tauto.
  { solve_linear. rewrite Rmin_comm. auto. }
  { tlaRevert. apply forget_prem.
    charge_intros.
    rewrite Always_and.
    tlaRevert. apply always_imp.
    charge_intros. decompose_hyps.
    - apply lorR1. apply lorR1.
      rewrite World_weaken.
      + charge_tauto.
      + tlaIntuition.
    - apply lorR1. apply lorR2.
      unfold Discr. repeat charge_split; try charge_tauto.
      + solve_linear. rewrite Rmin_comm. auto.
    - apply lorR2. apply lorR1. charge_intros. unfold Discr.
      charge_use. tlaRevert. apply forget_prem. charge_intros.
      apply Enabled_imp. rewrite Rmin_comm.
      repeat charge_split; try charge_tauto.
    - apply lorR2. apply lorR2.
      charge_split; try charge_assumption.
      rewrite UnchangedT_weaken; [ charge_assumption | ].
      unfold all_in. intros. apply List.in_or_app.
      apply List.in_app_or in H. intuition. }
Qed.

Axiom Proper_SysCompose : Proper (SysRec_equiv ==> SysRec_equiv ==> SysRec_equiv) SysCompose.
Existing Instance Proper_SysCompose.

Axiom SysCompose_Comm : forall a b, SysRec_equiv (SysCompose a b) (SysCompose b a).

Theorem Compose (a b : SysRec) P Q G :
  forall Hsafe : |-- SysSafe (SysCompose a b),
  G |-- SysD a -->> [] P ->
  G //\\ [] P |-- SysD b -->> [] Q ->
  G |-- SysD (SysCompose a b) -->> [](P //\\ Q).
Proof.
  intros Hsafe Ha Hb.
  rewrite <- Always_and.
  tlaIntro. tlaAssert ([]P).
  - charge_apply Ha. rewrite ComposeRefine.
    charge_tauto. auto.
  - tlaAssert (SysD b).
    + rewrite ComposeComm; rewrite ComposeRefine.
      charge_tauto. rewrite SysCompose_Comm. assumption.
    + charge_tauto.
Qed.

Lemma always_impl_distr : forall Q R,
    [] (Q -->> R) |-- [] Q -->> [] R.
Proof.
  intros.
  charge_intro.
  rewrite Always_and.
  tlaRevert.
  eapply always_imp.
  charge_tauto.
Qed.

Ltac charge_exfalso :=
  etransitivity; [ | eapply lfalseL ].

Theorem SysSafe_rule
: forall P S
    (Hprog : P |-- [] Enabled (Discr S.(Prog) S.(maxTime)))
(*    (Hcont : P |-- [] (Enabled (World S.(dvars) S.(world) //\\ S.(WConstraint)))) *),
    P |-- SysSafe S.
Proof.
  unfold SysSafe.
  intros.
  unfold SysD, SysD_or_stuck, sysD, sysD_or_stuck.
  charge_intro.
  charge_split.
  - charge_tauto.
  - rewrite <- landA. tlaRevert.
    tlaAssert (P); [ charge_assumption | rewrite Hprog at 2 ].
(*    tlaAssert (P); [ charge_assumption | rewrite Hcont at 2 ]. *)
    repeat rewrite <- always_impl_distr.
    apply always_tauto.
    unfold Next, Next_or_stuck.
    charge_intros. charge_split; [ | charge_tauto ].
    decompose_hyps; try charge_tauto.
    { charge_exfalso. charge_tauto. }
Qed.

Theorem SysRename_sound : forall s m,
  List.Forall (fun p => eq (is_st_term (snd p)) true) m ->
  Rename m (Enabled s.(Prog)) -|- Enabled (Rename m s.(Prog)) ->
  Rename m (SysD s) -|- SysD (SysRename m s).
Proof.
  intros. destruct s. unfold SysD, sysD, Next, World. simpl.
  restoreAbstraction. Rename_rewrite; auto.
  split.
  - repeat charge_split.
    + admit. (* This is not true. *)
    + charge_tauto.
    + tlaRevert. apply forget_prem.
      apply always_imp. charge_intros.
      decompose_hyps.
      * 
      repeat charge_split.
      * 