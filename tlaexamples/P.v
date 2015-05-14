Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Import LibNotations.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import ChargeTactics.Lemmas.

Open Scope string_scope.
Open Scope HP_scope.

Section P.

  Variable d : R.
  Hypothesis d_gt_0 : (d > 0)%R.

  Definition World : Formula :=
    Continuous (["x"' ::= "v", "v"' ::= 0, "t"' ::= --1]).

  Definition Ctrl : Formula :=
    "v"! = --"x"/d //\\ Unchanged (["x", "t"]).

  Definition Init : Formula :=
    "v" = --"x"/d.

  Definition Next : Formula :=
    (World \\// (Ctrl //\\ "t"! <= d)) //\\
    "t"! >= 0.

  Definition Spec : Formula :=
    Init //\\ []Next.

  Definition Abs (t : Term) (f : Term -> Formula) : Formula :=
    (t > 0 -->> f t) //\\ (t <= 0 -->> f (--t)).

  Definition Stable x : Formula :=
    Forall a : R,
      a > 0 -->>
      Exists b : R,
        b > 0 //\\
        (x < b -->> []Abs x (fun t => t < a)).

  Ltac decompose_hyps :=
    repeat rewrite land_lor_distr_R;
    repeat rewrite land_lor_distr_L;
    repeat apply lorL.

  Definition IndInv : Formula :=
    ("v" < 0 -->> --"v"*"t" <= "x") //\\
    ("v" >= 0 -->> "v"*"t" <= --"x").

  Lemma spec_indinv :
    |-- Spec -->> []IndInv.
  Proof.
    charge_intros.
    eapply BasicProofRules.discr_indX.
    + tlaIntuition.
    + unfold Spec. charge_tauto.
    + unfold Spec, IndInv, Init. admit.
    + unfold Next.
      decompose_hyps.
      * unfold World.
        eapply diff_ind with (Hyps:=ltrue).
        { tlaIntuition. }
        { tlaIntuition. }
        { charge_tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { repeat tlaSplit;
          try solve [solve_linear |
                     tlaIntro; eapply unchanged_continuous;
                     [ tlaAssume | solve_linear ] ]. }
      * simpl. restoreAbstraction. charge_split.
        { solve_linear. rewrite_next_st.
          clear - H1 H5 d_gt_0. 
          
  Lemma spec_stable :
    |-- Spec -->> Stable.
  Proof.
    unfold Stable. charge_intros.
    eapply lexistsR. instantiate (1:=x0).
    charge_split.
    - charge_tauto.
    - charge_intros.
      eapply BasicProofRules.discr_indX.
      + tlaIntuition.
      + unfold Spec. charge_tauto.
      + charge_tauto.
      + unfold Next. simpl BasicProofRules.next.
        decompose_hyps.
        * unfold World.


End P.

Close Scope string_scope.
Close Scope HP_scope.