Require Import RelationClasses.
Require Import TLA.Syntax.
Require Import TLA.Semantics.

(** NOTE: Avoid using this **)
Ltac breakAbstraction :=
  simpl in *; unfold tlaEntails in *; simpl in *.

Ltac restoreAbstraction :=
  change And    with (@land Formula _) in *;
  change Imp    with (@limpl Formula _) in *;
  change Or     with (@lor Formula _) in *;
  change TRUE   with (@ltrue Formula _) in *;
  change FALSE  with (@lfalse Formula _) in *;
  change Syntax.Forall with (@lforall Formula _) in *;
  change Syntax.Exists with (@lexists Formula _) in *.

Lemma tlaRefl
: forall G l o,
    match o with
    | Ge | Le | Eq => true
    | _ => false
    end = true ->
    G |-- Comp l l o.
Proof.
  breakAbstraction. intros. unfold eval_comp; simpl;
  destruct o; try congruence; simpl.
  apply RIneq.Req_ge. reflexivity.
  apply RIneq.Req_le. reflexivity.
Qed.

Ltac tlaRefl :=
  apply tlaRefl; reflexivity.

Ltac tlaSplit := apply landR.

Ltac tlaAssume :=
  match goal with
  | |- ?X |-- ?Y =>
    solve [ reflexivity
          | apply landL1 ; tlaAssume
          | apply landL2 ; tlaAssume ]
  end.

Fixpoint conj (ls : list Formula) : Formula :=
  match ls with
  | nil => ltrue
  | l :: nil => l
  | l :: ls => l //\\ conj ls
  end%list.

Lemma conj_app : forall b a,
    conj (a ++ b) -|- conj a //\\ conj b.
Proof.
  induction a; simpl; restoreAbstraction.
  { intros. rewrite landtrueL. reflexivity. }
  { intros.
    destruct a0.
    { simpl in *. restoreAbstraction.
      rewrite landtrueL in IHa.
      destruct b. simpl; restoreAbstraction.
      rewrite landtrueR. reflexivity. reflexivity. }
    { simpl in *; restoreAbstraction.
      rewrite landA.
      rewrite IHa. reflexivity. } }
Qed.

Fixpoint tlaSimplify (Hyps : list Formula) (f : Formula) : list Formula :=
  match f with
  | TRUE => nil
  | And P Q => tlaSimplify Hyps P ++ tlaSimplify Hyps Q
  | Or P Q =>
    match tlaSimplify Hyps P with
    | nil => nil
    | P' => match tlaSimplify Hyps Q with
            | nil => nil
            | Q' => (conj P' \\// conj Q') :: nil
            end
    end
  | Imp P Q =>
    match tlaSimplify (P :: Hyps) Q with
    | nil => nil
    | Q' => (P -->> conj Q') :: nil
    end
  | _ => f :: nil
  end%list.

Lemma tlaSimplify_sound' : forall G Hs,
    match tlaSimplify Hs G with
    | nil => True
    | G' => conj Hs |-- conj G'
    end ->
    conj Hs |-- G.
Proof.
  Transparent lentails lor land.
  induction G; try solve [ simpl; auto ].
  { simpl. breakAbstraction. trivial. }
  { Opaque lentails.
    simpl. intros.
    specialize (IHG1 Hs).
    specialize (IHG2 Hs).
    destruct (tlaSimplify Hs G1);
      destruct (tlaSimplify Hs G2); simpl in *;
      restoreAbstraction.
    { apply landR; eauto. }
    { apply landR; eauto. }
    { destruct l.
      apply landR; eauto.
      apply landR; eauto.
      eapply IHG1.
      rewrite H. rewrite List.app_nil_r. reflexivity. }
    { apply landR.
      { apply IHG1.
        rewrite H.
        admit. }
      { admit. } } }
  { simpl in *; restoreAbstraction.
    admit. }
  { simpl in *; restoreAbstraction; intros.
    specialize (IHG2 (G1 :: Hs)%list).
    destruct (tlaSimplify (G1 :: Hs) G2).
    { apply IHG2 in H.
      apply limplAdj. rewrite <- H.
      simpl.
      destruct Hs; simpl; restoreAbstraction.
      tlaAssume.
      tlaSplit; try tlaAssume. }
    { admit. } }
Qed.

Theorem tlaSimplify_sound : forall G H,
    match tlaSimplify (H :: nil) G with
    | nil => True
    | G' => H |-- conj G'
    end ->
    H |-- G.
Proof.
  intros. eapply (tlaSimplify_sound' G (H :: nil) H0).
Qed.