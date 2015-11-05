Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Charge.Logics.ILogic.
Require Import ChargeTactics.Tactics.

Section named.
  Context {L : Type}
          {ILO : ILogicOps L}
          {IL : ILogic L}.

  Fixpoint lentNamed (ls : list (string * L)%type) (G : L) : Prop :=
    match ls with
    | nil => |-- G
    | (_,p) :: ls => lentNamed ls (p -->> G)
    end.

  Instance Proper_lentNamed_lentails
  : Proper (eq ==> lentails ==> Basics.impl) lentNamed.
  Proof.
    red. red. intros; subst. induction y; do 2 red.
    { simpl. intros. etransitivity. eassumption. eauto. }
    { simpl. intros. destruct a.
      revert H0. eapply IHy.
      rewrite H. reflexivity. }
  Qed.

  Import ListNotations.

  Fixpoint remove (n : string) (ls : list (string * L)) : list (string * L) :=
    match ls with
    | nil => nil
    | (n',X) :: ls =>
      if String.string_dec n n' then remove n ls else (n',X) :: remove n ls
    end.

  Lemma clearNamed (n : string) ls
  : forall goal,
    lentNamed (remove n ls) goal ->
    lentNamed ls goal.
  Proof.
    induction ls; simpl; auto.
    destruct a.
    destruct (string_dec n s).
    { subst. intros. eapply Proper_lentNamed_lentails.
      reflexivity. 2: eauto.
      charge_intro.
      charge_assumption. }
    { simpl. intros. eapply Proper_lentNamed_lentails. reflexivity.
      2: eapply IHls; eauto. reflexivity. }
  Qed.

  Lemma introNamed (n : string) ls P Q :
    lentNamed ((n,P) :: ls) Q ->
    lentNamed ls (P -->> Q).
  Proof. simpl. auto. Qed.

  Fixpoint find (n : string) (ls : list (string * L))
  : option (L * (list (string * L) -> list (string * L)))  :=
    match ls with
    | nil => None
    | (n',X) :: ls => if String.string_dec n n'
                      then Some (X, fun x => x ++ ls)
                      else match find n ls with
                           | None => None
                           | Some (x,ls) => Some (x, fun x => (n',X) :: ls x)
                           end
    end.

  Lemma destructNamed (n : string) n1 n2 ls P Q R rst :
    find n ls = Some (P //\\ Q, rst) ->
    lentNamed (rst [(n1,P);(n2,Q)]) R ->
    lentNamed ls R.
  Proof.
  Admitted.

  Lemma applyNamed (n : string) ls P Q Z:
    find n ls = Some (Q -->> P, Z) ->
    lentNamed ls Q ->
    lentNamed ls P.
  Proof. Admitted.

  Goal lentNamed nil ((ltrue //\\ lfalse) -->> (ltrue -->> lfalse) -->> lfalse).
    apply (introNamed "H").
    apply (introNamed "H0").
    eapply (@applyNamed "H0"); [ reflexivity | ].
    eapply (@destructNamed "H" "H'" "H''"); [ reflexivity | cbv iota beta delta [ app ] ].
  Admitted.

End named.