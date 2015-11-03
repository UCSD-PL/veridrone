Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Import LibNotations.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import TLA.ArithFacts.
Require Import TLA.Substitution.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

(*
   As with most systems, to prove an invariant
   of a hybrid system, you come up with a global
   inductive invariant of that system that implies
   the invariant you care about. To show that the
   inductive invariant is in fact inductive, you
   have to show that it is preserved by the discrete
   and the continuous transitions. The content of the
   inductive invariant varied from system (e.g. conditions
   on how close the system can be to the height upper
   bound), but the core structure always stayed the same.
   It was always a conjunction of the following:
     1) Physical variables (like h) differ from
        their corresponding discrete variable (like H)
        according to the solution to the system
        of differential equations.
     2) For the next d (delay) time units, the content
        part of the inductive invariant will hold if
        you substitute, for each physical variable,
        its value in terms of only discrete variables.
     3) The time t never differs from its discrete
        variable T by more than d.
   For every example, we would have to prove that
   this inductive invariant was preserved by the
   continuous transition and by the discrete
   transition(s). This involved several kinds of
   duplicated work:
     1) (1) holds on any discrete transition with
        a Read (where T! = t, H! = h, etc.)
     2) (1) holds on any continuous transition
        to which the solution corresponds
     3) If the content of the inductive invariant only
        depends on variables in the spec, then (2)
        holds on the continuous transition
     4) (3) holds on any system properly enforcing
        the delay
   Given this, it seemed silly to repeat the structure
   of the inductive invariant and repeat the proofs
   that should always be possible. Ideally, for each
   system with a given continuous dynamics, one would
   only have to state the content part of the inductive
   invariant and then prove that the controller satisfies
   a property with respect to that content. This file
   allows one to do exactly that.

   Below, Ind_Inv captures this typical structure of
   the inductive invariant. The "controller" Ctrl,
   captures the only reasoning that one has to do
   to prove the content part of an inductive invariant
   for a particular system. The safety proof captures
   all of the duplicated proving that we were doing.

   In the end, to prove that some forumla I is an
   invariant of a system with concrete controller
   CtrlConcrete, one only has to prove

     CtrlConcrete --> Ctrl

   with I substituted for Inv in Ctrl. This amounts
   to reasoning about real arithmetic. Once one proves
   this, one uses refinement (implication) and the
   safety proof below to show that I is an invariant.
   Of course, this doesn't eliminate the need to come
   up with I, but it at least eliminates some of the
   repetitive work.
*)

(* The distance traveled with starting velocity v,
   acceleration a, for time t. *)
Definition tdist (v:Term) (a:Term) (t:Term) : Term :=
  v*t + (/2)%R*a*t^^2.

(* The difference between the actual time
   and the most recently measured time. *)
Definition tdiff : Term :=
  "t"-"T".

(* Parameters to this module. Contains the
   delay, the invariant, a proof that the invariant
   is a state formula, and a proof of a somewhat
   complicated looking lemma. I want this lemma
   to say that Inv only uses the variables in the
   spec. There are several simple ways to state this,
   but I was unable to use any of them in the safety
   proof. Instead, I came up with this more complicated
   lemma, which is easy to use in the safety proof.
   So far, I've also found that it is easy to prove
   for the instantiations of Inv I've come up with
   for our examples, so it hasn't been an issue yet. *)
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

Module AbstractIndAccCtrlMod (Import Params : InvParameters).

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

  (* The inductive invariant implies the invariant
     which contains the actual inductive content
     specific to a system. *)
  Lemma ind_inv_inv : |- Ind_Inv --> Inv.
  Proof.
    simpl; unfold eval_comp; simpl; intuition.
    specialize (H1 (hd tr "t" - hd tr "T"))%R. intuition.
    eapply subst_formula_eq with (x:="h"); eauto;
    [ | eapply subst_formula_eq with (x:="v"); eauto];
    solve_linear.
  Qed.

  (* The safety proof showing that Inv is in fact
     an invariant of this system. *)
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
                  (apply ind_inv_inv; simpl; auto).

              apply subst_eq_next with (x:="H") (t:="h");
                solve_linear.
              apply subst_eq_next with (x:="V") (t:="v");
                solve_linear.
              apply H16; auto.
            - repeat apply subst_st_formula;
              simpl; auto. }
      + apply Always_imp. apply ind_inv_inv.
Qed.

End AbstractIndAccCtrlMod.