Require Import Coq.Classes.RelationClasses.
Require Import ChargeTactics.Tactics.
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
  change Syntax.Exists with (@lexists Formula _) in *;
  change tlaEntails with (@lentails Formula _) in *;
  fold eval_formula.

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

Ltac tlaIntro := charge_intro.

Ltac tlaIntuition :=
  breakAbstraction ; intuition ; restoreAbstraction.

Ltac tlaAssert H :=
  apply Lemmas.lcut with (R:=H).

Ltac tlaRevert := first [ apply landAdj | apply Lemmas.lrevert ].

(** Rewriting **)
Section RW_Impl.
  Variable P : Formula.
  Definition RW_Impl (A B : Formula) : Prop :=
    P |-- A -->> B.

  Global Instance Reflexive_RW_Impl : Reflexive RW_Impl.
  Proof.
    red; red. intros. apply limplAdj. tlaAssume.
  Qed.

  Global Instance Transitive_RW_Impl : Transitive RW_Impl.
  Proof.
    red; red. intros. apply limplAdj.
    eapply Lemmas.lcut. instantiate (1 := y).
    apply landAdj. apply H.
    apply landL1. apply H0.
  Qed.

  Require Import Setoid.

  Global Add Parametric Relation : Formula RW_Impl
   reflexivity proved by Reflexive_RW_Impl
   transitivity proved by Transitive_RW_Impl
   as RW_Impl_rel.

  Global Add Parametric Morphism : (@land Formula _) with
    signature (RW_Impl ==> RW_Impl ==> RW_Impl)
    as RW_Impl_and_mor.
  Proof.
    unfold RW_Impl. simpl.
    breakAbstraction. simpl. intuition.
  Qed.

  Global Add Parametric Morphism : (@land Formula _) with
    signature (RW_Impl --> RW_Impl --> Basics.flip RW_Impl)
    as RW_Impl_and_flip_mor.
  Proof.
    unfold RW_Impl. simpl.
    breakAbstraction. simpl. intuition.
  Qed.

  Global Add Parametric Morphism : (@lor Formula _) with
    signature (RW_Impl ==> RW_Impl ==> RW_Impl)
    as RW_Impl_or_mor.
  Proof.
    unfold RW_Impl. simpl.
    breakAbstraction. simpl. intuition.
  Qed.

  Global Add Parametric Morphism : (@lor Formula _) with
    signature (RW_Impl --> RW_Impl --> Basics.flip RW_Impl)
    as RW_Impl_or_flip_mor.
  Proof.
    unfold RW_Impl. simpl.
    breakAbstraction. simpl. intuition.
  Qed.

  Global Add Parametric Morphism : (@limpl Formula _) with
    signature (RW_Impl --> RW_Impl ==> RW_Impl)
    as RW_Impl_impl_mor.
  Proof.
    unfold RW_Impl. simpl.
    breakAbstraction. simpl. intuition.
  Qed.

  Global Add Parametric Morphism : (@limpl Formula _) with
    signature (RW_Impl ==> RW_Impl --> Basics.flip RW_Impl)
    as RW_Impl_impl_flip_mor.
  Proof.
    unfold RW_Impl. simpl.
    breakAbstraction. simpl. intuition.
  Qed.

  Global Add Parametric Morphism : (@lentails Formula _ P) with
    signature (RW_Impl ==> Basics.impl)
    as RW_Impl_entails_mor.
  Proof.
    unfold RW_Impl, Basics.impl. simpl.
    breakAbstraction. simpl. intuition.
  Qed.

  Global Add Parametric Morphism : (@lentails Formula _ P) with
    signature (RW_Impl --> Basics.flip Basics.impl)
    as RW_Impl_flip_entails_mor.
  Proof.
    unfold RW_Impl, Basics.impl. simpl.
    breakAbstraction. simpl. intuition.
  Qed.

  Definition rw_impl {A B : Formula} (H : P |-- A -->> B) : RW_Impl A B := H.

End RW_Impl.

Class SimpleEntail (A B : Formula) : Prop :=
  slentails : lentails A B.

Hint Extern 1 (SimpleEntail _ _) => match goal with
                                    | |- ?X => idtac X; red; charge_tauto
                                    end : typeclass_instances.

Global Instance subrelation_RW_Impl P Q (H : SimpleEntail Q P)
: subrelation (RW_Impl P) (RW_Impl Q).
Proof. do 4 red. unfold RW_Impl; intros.
       red in H. rewrite H. assumption.
Qed.

Global Add Parametric Morphism P Q (H : SimpleEntail P Q)
: (@lentails Formula _ P) with
  signature (RW_Impl Q --> Basics.flip Basics.impl)
  as RW_Impl_weaken_flip_entails_mor.
Proof.
  unfold RW_Impl, Basics.impl. intros.
  red in H. charge_tauto.
Qed.

Global Add Parametric Morphism P Q (H : SimpleEntail P Q)
: (@lentails Formula _ P) with
  signature (RW_Impl Q ==> Basics.impl)
  as RW_Impl_weaken_entails_mor.
Proof.
  unfold RW_Impl, Basics.impl. intros.
  red in H. charge_tauto.
Qed.

Arguments rw_impl {P A B} _ _ _ _.

Export ChargeTactics.Tactics.