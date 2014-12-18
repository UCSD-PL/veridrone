Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Import LibNotations.
Require Import TLA.ProofRules.
Require Import TLA.Tactics.
Require Import TLA.ArithFacts.
Require Import Modules.AbstractIndAccCtrl.
Require Import Modules.AbstractOneDimAccCtrl2.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

Module Params <: CtrlParameters.

  Variable ub : R.
  Variable d : R.
  Hypothesis Hd : (d > 0)%R.

  Variable amin : R.
  Hypothesis Hamin : (amin < 0)%R.

  Variable amax : R.
  Hypothesis Hamax : (amax > 0)%R.

End Params.

Import Params.

Module AbstractCtrl := AbstractAccDimCtrl2(Params).

Import AbstractCtrl.

Definition Read : Formula :=
  "T"! = "t" /\ "H"! = "h" /\ "V"! = "v".

Definition Evolve : Formula :=
  Continuous (["h"' ::= "v",
               "v"' ::= "a",
               "a"' ::= 0,
               "t"' ::= 1,
               "H"' ::= 0,
               "T"' ::= 0,
               "V"' ::= 0]).

Definition SafeCtrl : Formula :=
   "H" + tdist "V" amax d +
   tdist ("V" + amax*d) amax d +
   sdist ("V" + 2*amax*d)
    <= ub.

Definition Ctrl : Formula :=
     (SafeCtrl /\ "A" <= amax /\ "a"! = "A")
  \/ (SafeCtrl /\ "a"! = amax)
  \/ ("a"! = amin).

(* Attempt at a more sophisticated safety check. *)
(*
(*Definition safe_travel (h v t:Term) :=
  ("A" >= 0 /\ h + tdist v "A" t <= ub - sdist v2.*)

Definition Safe (V a:Term) : Formula :=
  (* Always moves up *)
  ((V >= 0 /\ a >= 0)
   --> "h" - "H" <= tdist V a d) /\
  (* Always moves down *)
    ((V < 0 /\ a < 0)
     --> "h" - "H" <= 0) /\
    (* Moves up for next d time *)
    ((V >= 0 /\ a < 0 /\ --a*d < V)
     --> "h" - "H" <= tdist V a d) /\
    (* Peaks in middle *)
    ((V >= 0 /\ a < 0 /\ --a*d >= V)
     (* We don't have division, so we need a
        on the left. *)
     --> a*("h" - "H") <= --V^^2*(/2)%R) /\
    (* Moves down then turns around and ends
       heigher than at the beginning *)
    ((V < 0 /\ a >= 0 /\ tdist V a d >= 0)
     --> "h" - "H" <= tdist V a d) /\
    (* Moves down, maybe turns around, but ends
       lower than at the beginning *)
    ((V < 0 /\ a >= 0 /\ tdist V a d < 0)
     --> "h" - "H" <= 0)



     ("V" >= 0 /\ "a" >= 0 /\ "A" >= 0 /\
      "H" + tdist "V" "a" d + tdist ("V" + "a"*d) "A" d
       <= ub - sdist ("V" + "a"*d + "A"*d))
  \/ ("V" >= 0 /\ "a" >= 0 /\ "A" < 0 /\
      --"A"*d < "V" + "a"*d /\
      "H" + tdist "V" "a" d + tdist ("V" + "a"*d) "A" d
       <= ub - sdist ("V" + "a"*d))
  \/ ("V" >= 0 /\ "a" >= 0 /\ "A" < 0 /\
      --"A"*d >= "V" + "a"*d /\
      "H" + tdist "V" "a" d + tdist ("V" + "a"*d) "A" d
       <= ub - sdist ("V" + "a"*d))

    (* Always moves down *)
    (("V" < 0 /\ "a" < 0)
     --> "h" - "H" <= 0) /\
    (* Moves up for next d time *)
    (("V" >= 0 /\ "a" < 0 /\ --"a"*d < "V")
     --> "h" - "H" <= tdist "V" "a" d) /\
    (* Peaks in middle *)
    (("V" >= 0 /\ "a" < 0 /\ --"a"*d >= "V")
     (* We don't have division, so we need "a"
        on the left. *)
     --> "a"*("h" - "H") <= --"V"^^2*(/2)%R) /\
    (* Moves down then turns around and ends
       heigher than at the beginning *)
    (("V" < 0 /\ "a" >= 0 /\ tdist "V" "a" d >= 0)
     --> "h" - "H" <= tdist "V" "a" d) /\
    (* Moves down, maybe turns around, but ends
       lower than at the beginning *)
    (("V" < 0 /\ "a" >= 0 /\ tdist "V" "a" d < 0)
     --> "h" - "H" <= 0)*)

Definition Next : Formula :=
     (Evolve /\ "t"! <= "T" + d)
  \/ (Ctrl /\ Read /\ Unchanged (["h", "v", "t"])).

Definition Init : Formula := AbstractCtrl.Ind_Inv.

Definition Safe : Formula :=
  "h" <= ub.

Lemma refinement :
  |- (Init /\ []Next)
       --> (AbstractCtrl.Init /\ []AbstractCtrl.Next).
Proof.
  pose proof Hd. pose proof Hamax. pose proof Hamin.
  apply and_right.
  - apply and_left1. apply imp_id.
  - apply and_left2. apply always_imp.
    repeat apply or_left.
    + unfold Evolve. apply or_right1.
      repeat apply and_right.
      * apply and_left1. apply imp_id.
      * apply and_left2. apply imp_id.
    + apply or_right2.
      apply and_right.
      * apply and_left1.
        { solve_linear; unfold InvParams.d in *;
          repeat match goal with
                   | [ H : _ |- _ ] =>
                     match type of H with
                       | @eq R _ _ => idtac
                       | _ => revert H
                     end
                 end;
          repeat match goal with
                   | [ H : @eq R _ _ |- _ ] =>
                     rewrite H
                 end; intros.
          - eapply Rle_trans; eauto.
            (*          clear H4 H6 H2 H12 H5.*)
            (*Time solve_nonlinear.*)
            admit.
          - eapply Rle_trans; eauto.
            clear H5 H4 H6 H2 H12 H11.
            Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.
          - Time solve_nonlinear.

Ltac thing t :=
match goal with
| [ _ : (t - ?e1 <= ?e2) |- 
pose proof (derive_increasing_interv_var 
(* 8, 12 solved nonlinearly *)


apply and_right; repeat apply or_left;
          try apply imp_right.
          try solve [unfold amax; solve_linear].
          - apply imp_strengthen with (F2:="h" < ubH);
            [ solve_linear | ].
            apply imp_strengthen with (F2:="v" < vt + ubV);
              [ solve_linear | ].
            solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.inv2, ub, ubV, ubv, ubv_r, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H8 in H10. clear H8 H0 H1 H5 H7 H11 H6.
              unfold amax, ubv_r in *. repeat rewrite Rplus_assoc.
              match goal with
                | [ H : Rlt ?e1 ?e2 |- Rle (Rplus ?e1 ?e3) _ ]
                  => apply Rle_trans with (r2:=Rplus e2 e3);
                    [ solve_linear | clear H ]
              end.
              Time solve_nonlinear.
            + clear H10 H11. unfold ubv_r in *. Time solve_nonlinear.
            + clear H11. unfold ubv_r in *. Time solve_nonlinear.
          - apply imp_strengthen with (F2:="h" < ubH);
            [ solve_linear | ].
            solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.inv2, ub, ubV, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H7 in H9.
              assert (0 <= hd tr "v")%R by solve_linear.
              intuition. eapply Rle_trans; eauto.
              R_simplify; solve_linear. unfold amax. simpl.
              repeat rewrite Rmult_1_r.
              R_simplify. simpl. solve_linear.
            + repeat rewrite Rplus_assoc.
              match goal with
                | [ H : Rlt ?e1 ?e2 |- Rle (Rplus ?e1 ?e3) _ ]
                  => apply Rle_trans with (r2:=Rplus e2 e3);
                    [ solve_linear | clear H ]
              end.
              rewrite H7 in H9.
              assert (hd tr "v" - x <= 0)%R by solve_linear.
              clear H8.
              unfold ubv_r in *.
              R_simplify. simpl.
              apply Rminus_le.
              R_simplify. simpl.
              rewrite Rmult_comm.
              apply Rmult_le_0; solve_linear.
              clear H10. generalize dependent (hd tr "v").
              intros. clear dependent tr.
              Time solve_nonlinear.
            + unfold ubv_r in *. Time solve_nonlinear.
          - apply imp_strengthen with (F2:="v" < --vt + ubV);
              [ solve_linear | ].
            solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.inv2, ub, ubV, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H7 in H9.
              assert (hd tr "v" + 1 * x < 0)%R by solve_linear.
              solve_linear.
            + rewrite H7 in H9. clear H10.
              unfold ubv_r in *.
              Time solve_nonlinear.
            + clear H10. unfold ubv_r in *.
              solve_linear.
            + clear H10. unfold ubv_r in *.
              Time solve_nonlinear.
          - solve_linear;
              unfold amax, AbstractCtrl.amaxinv,
              AbstractCtrl.inv2, ub, ubV, ubH, ubH_r in *;
              repeat match goal with
                       | [ H : @eq R _ _ |- _ ] =>
                         rewrite H
                     end; solve_linear.
            + rewrite H6 in H8.
              assert (0 <= hd tr "v")%R by solve_linear.
              unfold amax, ubv_r in *. clear H9.
              Time solve_nonlinear.
            + rewrite H6 in H8. clear H9.
              destruct (Rle_dec 0 (hd tr "v"))%R.
              * unfold amax, ubv_r in *. Time solve_nonlinear.
              * assert (hd tr "v" * x + / 2 * (0 - 1) * (x * (x * 1))
                      <= 0)%R
                       by (generalize dependent (hd tr "v"); intros; clear dependent tr;
                           clear r0; solve_nonlinear).
                solve_linear.
            + unfold ubv_r in *. Time solve_nonlinear. }
      * solve_linear.
Qed.

Lemma safety :
  |- (Init /\ []Next) --> []Safe.
Proof.
  apply imp_trans
  with (F2:=AbstractCtrl.Init /\ []AbstractCtrl.Next).
  - apply refinement.
  - apply AbstractCtrl.safety.
Qed.