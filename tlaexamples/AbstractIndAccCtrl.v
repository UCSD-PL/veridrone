Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import TLA.ArithFacts.
Require Import TLA.Substitution.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

Definition tdist (v:Term) (a:Term) (t:Term) : Term :=
  v*t + (/2)%R*a*t^^2.

Definition tdiff : Term :=
  "t"-"T".

Module Type InvParameters.

  Parameter d : R.
  Parameter Hd : (d > 0)%R.

  Parameter Inv : Formula.
  Hypothesis HInv_st : is_st_formula Inv.
  Hypothesis HInv_unch : forall (t:R),
    |- (Inv["H" + (tdist "V" "a" t)//"h"]["V" + "a"*t//"v"] /\
        Unchanged (["a", "H", "V", "T"]))
       --> (next Inv)
             [next_term ("H" + (tdist "V" "a" t))/!"h"]
             [next_term ("V" + "a"*t)/!"v"].

End InvParameters.

Module AbstractIndAccCtrl (Import Params : InvParameters).

  Definition Ctrl : Formula :=
    Inv -->
        Forall R
        (fun t =>
           0 <= t <= d -->
           (next Inv)["h" + (tdist "v" "a"! t)/!"h"]
                     ["v" + "a"!*t/!"v"]
                     ["h"/!"H"]
                     ["v"/!"V"]).

  Definition Evolve : Formula :=
    Continuous (["h"' ::= "v",
                 "v"' ::= "a",
                 "a"' ::= 0,
                 "t"' ::= 1,
                 "H"' ::= 0,
                 "T"' ::= 0,
                 "V"' ::= 0
               ]).

  Definition Read : Formula :=
    "T"! = "t" /\ "H"! = "h" /\ "V"! = "v".
 
  Definition Next : Formula :=
       (Evolve /\ "t"! <="T" + d)
    \/ (Ctrl /\ Read /\
        Unchanged (["h","v","t"])).

  Definition Ind_Inv : Formula :=
    "h" - "H" = tdist "V" "a" tdiff /\
    "v" - "V" = "a"*tdiff /\
    (Forall R
            (fun t =>
               0 <= t <= d -->
               Inv["H" + (tdist "V" "a" t)//"h"]
                  ["V" + "a"*t//"v"])) /\
    0 <= tdiff <= d.

  Definition Init : Formula := Ind_Inv.

  Lemma ind_inv_safe : |- Ind_Inv --> Inv.
  Proof.
    simpl; unfold eval_comp; simpl; intuition.
    specialize (H1 (hd tr "t" - hd tr "T"))%R. intuition.
    eapply subst_formula_eq with (x:="h"); eauto;
    [ | eapply subst_formula_eq with (x:="v"); eauto];
    solve_linear.
  Qed.

  Lemma safety :
    |- (Init /\ []Next) --> []Inv.
  Proof.
     apply imp_trans with (F2:=Ind_Inv /\ []Next).
    - apply and_right.
      + apply and_left1. apply imp_id.
      + apply and_left2. apply imp_id.
    - apply imp_trans with (F2:=[]Ind_Inv).
      + pose proof HInv_st.
        apply inv_discr_ind.
        simpl. intuition.
        repeat apply subst_st_formula;
          simpl; auto. unfold Next, Evolve.
        prove_inductive.
        * match goal with
            | [ |- context [Continuous ?deqs] ] =>
              match goal with 
                | [ |-( |- _ --> ?g)] => 
                  eapply diff_ind
                  with (cp:=deqs) (G:=unnext g)
                       (Hyps:="v"= "V"+ "a"*("t"-"T"))
              end
          end; try solve [simpl; intuition | solve_linear].
          match goal with
            | [ |- context [Continuous ?deqs1] ] =>
              match goal with 
                | [ |- (|- _ --> ?g1)] => 
                  eapply diff_ind
                  with (cp:=deqs1) (G:=unnext g1) (Hyps:=TRUE)
              end
          end; try solve [intuition | solve_linear].
        * apply forall_right; intro.
          match goal with
            | [ |- context [Continuous ?deqs] ] =>
              apply unchanged_continuous with (eqs:=deqs)
          end; try solve [solve_linear].

          repeat rewrite next_subst_formula; auto.
          simpl. intros. apply HInv_unch.
          intuition.
          apply H9; intuition.
          simpl. intuition.
          unfold eval_comp in *. simpl in *.
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H
                 end; solve_linear.
          unfold eval_comp in *. simpl in *.
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H
                 end; solve_linear.
          apply subst_st_formula;
            simpl; auto.
        * solve_linear;
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H
                 end; solve_linear.
        * solve_linear;
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H
                 end; solve_linear.
        * solve_linear.
          { repeat rewrite next_subst_formula; auto.
            - apply subst_term_formula_sub
              with (x:="V") (t1:="v").
              simpl; auto.

              rewrite subst_term_formula_comm;
                try solve [intro; discriminate |
                           reflexivity ].
              apply subst_term_formula_sub
              with (x:="V") (t1:="v"); auto.
              apply subst_term_formula_sub
              with (x:="H") (t1:="h"); auto.
              rewrite subst_term_formula_comm;
                try solve [intro; discriminate |
                           reflexivity].
              unfold tdist in *. simpl in *.
              assert (eval_formula Inv tr) by
                  (apply ind_inv_safe; simpl; auto).

              apply subst_eq_next with (x:="H") (t:="h");
                solve_linear.
              apply subst_eq_next with (x:="V") (t:="v");
                solve_linear.
              apply H16; auto.
            - repeat apply subst_st_formula;
              simpl; auto. }
      + apply always_imp. apply ind_inv_safe.
Qed.

End AbstractIndAccCtrl.