Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.

Open Scope HP_scope.
Open Scope string_scope.

Section HeightCtrl.

  Variable d : time.

  Definition Read : Formula :=
    "T"! = "t" /\ "H"! = "h".

  Definition Evolve : Formula :=
    Continuous (["h"' ::= "v"]) d "t".

  Definition Ctrl : Formula :=
       ("H" < 0  /\ "v"! = 1)
    \/ ("H" >= 0 /\ "v"! = --1).

  Definition Next : Formula :=
       ("pc" = 0 /\ Read /\ "pc"! = 1 /\
        Unchanged (["h", "t", "v"]))
    \/ ("pc" = 1 /\ Evolve /\
        Unchanged (["v", "H", "T"]))
    \/ ("pc" = 1 /\ Ctrl /\ "pc"! = 0 /\
        Unchanged (["h", "t", "v"])).

  Definition Init : Formula :=
    (--1 = "v" \/ "v" = 1) /\
    --d <= "h" /\ "h" <= d /\
    "t" = 0 /\ "T" = 0 /\ "pc" = 0.

  Definition Safe : Formula :=
    --2*d <="h" /\ "h" <= 2*d.

  Lemma safety :
    |- (Init /\ []Next) --> []Safe.
  Admitted.

End HeightCtrl.
