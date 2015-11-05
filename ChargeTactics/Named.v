Require Import Charge.Logics.ILogic.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Section named.
  Context {L : Type} {ILO : ILogicOps L}.

  Fixpoint lent_named (ls : list (string * L)%type) acc (G : L) : Prop :=
    match ls with
    | nil => acc |-- G
    | (_,p) :: ls => lent_named ls (acc //\\ p) G
    end.

  Definition lentNamed ls goal := lent_named ls ltrue goal.
  Import ListNotations.

  Fixpoint remove (n : string) (ls : list (string * L)) : list (string * L) :=
    match ls with
    | nil => nil
    | (n',X) :: ls =>
      if String.string_dec n n' then remove n ls else (n',X) :: remove n ls
    end.

  Lemma clearNamed (n : string) ls goal :
    lentNamed (remove n ls) goal ->
    lentNamed ls goal.
  Proof.
  Admitted.

  Lemma introNamed (n : string) ls P Q :
    lentNamed ((n,P) :: ls) Q ->
    lentNamed ls (P -->> Q).
  Proof.
    unfold lentNamed. simpl.
  Admitted.

  Fixpoint find (n : string) (ls : list (string * L)) : option L :=
    match ls with
    | nil => None
    | (n',X) :: ls => if String.string_dec n n' then Some X else find n ls
    end.

  Lemma destructNamed (n : string) n1 n2 ls P Q R :
    find n ls = Some (P //\\ Q) ->
    lentNamed ((n1,P)::(n2,Q)::ls) R ->
    lentNamed ls R.
  Proof. Admitted.
    

  Lemma applyNamed (n : string) ls P Q :
    find n ls = Some (Q -->> P) ->
    lentNamed ls Q ->
    lentNamed ls P.
  Proof. Admitted.

  Goal lentNamed nil ((ltrue //\\ lfalse) -->> (ltrue -->> lfalse) -->> lfalse).
    apply (introNamed "H").
    apply (introNamed "H0").
    eapply (@applyNamed "H0"); [ reflexivity | ].
    eapply (@destructNamed "H" "H'" "H''"); [ reflexivity | ].
  Admitted.

End named.
