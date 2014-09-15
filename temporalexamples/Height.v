Require Import TempLang.Syntax.
Require Import TempLang.Semantics.
Require Import Rbase.

Open Scope HP_scope.
Open Scope string_scope.

Section HeightCtrl.

  (* The delays for evaluating the condition,
     running the first assignment, and
     running the second assignment. *)
  Variable d1 : R.
  Variable d2 : R.
  Variable d3 : R.

  (* The setpoint of the controller. *)
  Variable c : R.

  (* The controller. *)
  Definition ctrl :=
    IFF `"h" < #c @ d1
    THEN "v" ::= #1 @ d2
    ELSE "v" ::= --#1 @ d3.

  (* The continuous dynamics. *)
  Definition world :=
    ["h"' ::= `"v"].

  (* The entire system. The controller runs in
     parallel with the continuous dynamics.
     This just repeats some number of times. *)
  Definition sys :=
    (ctrl || world)**.

  (* The safety property. Any behavior produced by
     the system has the invariant h > 0. *)
  (* We'll need to add some initial conditions here.
     It remains to be seen what those are. *)
  Lemma safety :
    |- |sys| --> []`"h" > #0.
  Admitted.

  (* The liveness property. Any behavior produced by
     the system has some point in time in which h = c. *)
  Lemma liveness :
    |- |sys| --> <>`"h" = #c.
  Admitted.

End HeightCtrl.