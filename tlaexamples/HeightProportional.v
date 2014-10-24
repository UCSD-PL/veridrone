Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

Section HeightCtrl.

  Variable d : R.
  (* The following hypothesis is not necessary
     for the safety property, but it's necessary
     for ensuring that non-Zeno behaviors are
     possible. *)
  Hypothesis Hd : (d > 0)%R.
  (* We don't have division in the language, so we
     just add a parameter, which is the inverse of
     d *)
  Variable dinv : R.
  Hypothesis Hdinv : (@eq R (d * dinv) 1)%R.

  Definition Read : Formula :=
    "T"! = "t" /\ "H"! = "h".

  Definition Evolve : Formula :=
    Continuous (["h"' ::= "v",
                 "v"' ::= 0,
                 "t"' ::= 1,
                 "H"' ::= 0,
                 "T"' ::= 0,
                 "pc"' ::= 0]).

  Definition Ctrl : Formula :=
    "v"! = --"H"*dinv.

  Definition Next : Formula :=
       ("pc" = 0 /\ Read /\ "pc"! = 1 /\
        Unchanged (["h", "t", "v"]))
    \/ ("pc" = 1 /\ Evolve /\ "t"! <= "T" + d)
    \/ ("pc" = 1 /\ Ctrl /\ "pc"! = 0 /\
        Unchanged (["h", "t", "H", "T"])).

  Definition Init : Formula :=
       (   ("v" >= 0 /\ --d <= "h" <= d*(1-"v"))
        \/ ("v" <= 0 /\ --d*(1+"v") <= "h" <= d))
    /\ "t" = 0 /\ "T" = 0 /\ "pc" = 0
    /\ "H" = "h" /\ --1 <= "v" <= 1.

  Definition Safe : Formula :=
    --d <="h" <= d.

  Definition Ind_Inv : Formula :=
    (("pc" = 0 /\ "v" >= 0) --> (--d <= "h" <= d*(1-"v"))) /\
    (("pc" = 0 /\ "v" <= 0) --> (--d*(1+"v") <= "h" <= d)) /\
    (("pc" = 1 /\ "v" >= 0) --> (--d <= "H" <= d*(1-"v") /\
                                 0 <= "h"-"H" <= "v"*("t"-"T"))) /\
    (("pc" = 1 /\ "v" <= 0) --> (--d*(1+"v") <= "H" <= d /\
                                 0 <= "H"-"h" <= "v"*("T"-"t"))) /\
    0 <= "t"-"T" <= d /\
    --1 <= "v" <= 1 /\
    ("pc"=0 \/ "pc"=1).

  Lemma ind_inv_init : |- Init --> Ind_Inv.
  Proof. Time solve_linear; solve_nonlinear. Qed.

  Lemma ind_inv_safe : |- Ind_Inv --> Safe.
  Proof. Time solve_linear.
         Time solve_nonlinear.
         Time solve_nonlinear.
         Time solve_nonlinear.
         Time solve_nonlinear.
  Time Qed.
  (* Times (Seconds): 0,14,2,40,5,0 ;; 1,0,1,1349,57,0 *)
(*         clear H7. clear H1. destruct (Rle_dec (hd tr "v") R0).
         intuition. apply Rle_trans with (r2:=((0 - d) * (1 + hd tr "v"))%R).
(*         assert (0 - d <= 0)%R by solve_linear.
         assert (1 + hd tr "v" <= 1)%R by solve_linear.*)
         pose proof (Rmult_le_compat_neg_l (0-d) (1 + hd tr "v") 1 (*H1 H7*))%R.
         solve_linear.
         solve_linear.
         solve_linear.
         destruct (Rle_dec (hd tr "v") R0).
         solve_linear.
         assert (hd tr "v" >= 0)%R by solve_linear.
         intuition.
         apply Rle_trans with (r2:=(d * (1 - hd tr "v"))%R).
         auto.
         pose proof (Rmult_le_compat_l d (1 - hd tr "v") 1)%R.
         solve_linear.
         destruct (Rle_dec (hd tr "v") R0).
         intuition.*)
         

  Lemma safety :
    |- (Init /\ []Next) --> []Safe.
  Proof.
    apply imp_trans with (F2:=Ind_Inv /\ []Next).
    - apply and_right.
      + apply and_left1. apply ind_inv_init.
      + apply and_left2. apply imp_id.
    - apply imp_trans with (F2:=[]Ind_Inv).
      + apply inv_discr_ind; auto. unfold Next, Evolve.
        Time repeat apply or_next;
          repeat first [ apply and_right |
                         apply imp_right ];
        match goal with
          | [ |- context [Continuous ?eqs] ]
              => pose "Continuous"; extract_unchanged eqs;
                 match goal with
                   | [ |- context [next_term (TermC (VarC "pc")) =
                                   next_term (TermC (ConstC (NatC 1)))] ] =>
                     match goal with
                       | [ |- context [Comp (next_term (TermC (VarC "v"))) (next_term ?e) ?op] ] =>
                         abstract (prove_diff_inv (Comp "v" e op);
                                   match goal with
                                     | [ |- (|- (?I /\ Continuous eqs) --> next ?I) ] =>
                                       extract_unchanged eqs; solve_linear
                                     | [ |- _ ] =>
                                       solve_linear
                                   end)
                     end
                   | [ |- _ ] =>
                     try abstract solve [solve_linear |
                                         prove_diff_inv TRUE; solve_linear]
                 end
          | [ |- _ ]
              => pose "Discrete";
                 try abstract solve_linear
        end.
(* 252 seconds *)
Ltac solver :=
  simpl; unfold eval_comp; simpl; intuition;
  repeat match goal with
             |- context [?e] =>
             match goal with
               | [ H : @eq R e _ |- _ ]
                 => rewrite H
             end
         end; repeat (rewrite Rminus_diag_eq;
                      [ | reflexivity ]);
  solve_linear.
solver.
solver.
solver.
solver.
Time solve_nonlinear.
(* 60 seconds *)
unfold Ctrl.
solver.
rewrite Rmult_minus_distr_l.
rewrite Rmult_1_r.
rewrite Rmult_comm.
rewrite Rmult_assoc.
rewrite Rmult_comm in Hdinv.
rewrite Hdinv.
destruct (Rle_dec (hd tr "v") R0).
intuition.
solve_linear.
assert (hd tr "v" >= 0)%R by solve_linear.
intuition.
pose proof (Rle_trans _ _ (1*(hd tr "t" - hd tr "T"))%R H22).
assert ((hd tr "v" * (hd tr "t" - hd tr "T") <= 1 * (hd tr "t" - hd tr "T"))%R).
apply Rmult_le_compat_r; solve_linear.
specialize (H20 H23).
solve_linear.
solver.
rewrite Rmult_comm.
rewrite Rmult_plus_distr_r.
rewrite Rmult_assoc.
rewrite (Rmult_minus_distr_l dinv).
rewrite Rmult_comm in Hdinv.
rewrite Hdinv.
rewrite Rmult_0_r.
destruct (Rle_dec (hd tr "v") R0);
solve_linear.
pose proof (Rle_trans _ _ (-1*(hd tr "T" - hd tr "t"))%R H21).
assert ((hd tr "v" * (hd tr "T" - hd tr "t") <= -1 * (hd tr "T" - hd tr "t"))%R).
rewrite Rmult_comm.
rewrite (Rmult_comm (-1)%R).
apply Rmult_le_compat_neg_l; solve_linear.
specialize (H19 H22).
solve_linear.

solver.
destruct (Rle_dec (hd tr "v") R0); solve_linear.
assert (hd tr "v" >= 0)%R by solve_linear.
intuition.
assert (hd tr "v" * (hd tr "t" - hd tr "T") <= hd tr "v" * d)%R.
apply Rmult_le_compat_l; solve_linear.
pose proof (Rle_trans _ _ _ H22 H20).
SearchAbout Rle.
assert (hd tr "h" <= hd tr "H" + (hd tr "v" * d))%R.
solve_linear.
solve_linear.

solver.
assert (hd tr "H" <= d)%R.
destruct (Rle_dec (hd tr "v") R0);
solve_linear.
assert (hd tr "v" >= 0)%R by solve_linear.
intuition.
apply Rle_trans with (r2:=(d * (1 - hd tr "v"))%R); auto.
apply Rle_trans with (r2:=(d*1)%R); solve_linear.
apply Rmult_le_compat_l; solve_linear.
cut (hd tr "H"*dinv <= 1)%R; solve_linear.
apply Rle_trans with (r2:=(d*dinv)%R).
assert (dinv > 0)%R.
clear H0 H2 H4 H6 H8 H9 H12 H10 H11 H15 H7 H16 H14 H13 H H3 H5 H1.
solve_nonlinear.
solve_linear.
solve_linear.

solver.
assert (-d <= hd tr "H")%R.
destruct (Rle_dec (hd tr "v") R0);
solve_linear.
apply Rle_trans with (r2:=((0 - d) * (1 + hd tr "v"))%R); auto.
apply Rle_trans with (r2:=((0-d)*1)%R); solve_linear.
apply Rmult_le_compat_neg_l; solve_linear.
cut (-1 <= hd tr "H"*dinv)%R; solve_linear.
apply Rle_trans with (r2:=(-d*dinv)%R); solve_linear.
apply Rmult_le_compat_r; solve_linear.
assert (dinv > 0)%R.
clear H0 H2 H4 H6 H8 H9 H12 H10 H11 H15 H7 H16 H14 H13 H H3 H5 H1.
solve_nonlinear.
solve_linear.
      + apply always_imp. apply ind_inv_safe.
  Qed.

End HeightCtrl.