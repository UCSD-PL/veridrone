Require Import TempLang.Syntax.
Require Import TempLang.Semantics.
Require Import Rbase.

Open Scope HP_scope.
Open Scope string_scope.

Section HeightCtrl.

  Variable d1 : R.
  Variable d2 : R.
  Variable d3 : R.
  Variable c : R.

  Definition ctrl :=
    IFF `"h" < #c @ d1
    THEN "v" ::= #1 @ d2
    ELSE "v" ::= --#1 @ d3.

  Definition world :=
    ["h"' ::= `"v"].

  Definition sys :=
    ctrl || world.

  (* We'll need to add some initial conditions here.
     It remains to be seen what those are. *)
  Lemma safety :
    |- |sys| --> []`"h" > #0.
  Admitted.

  Lemma liveness :
    |- |sys| --> <>`"h" = #c.
  Admitted.

End HeightCtrl.