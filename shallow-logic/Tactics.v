Require Import Coq.Reals.Rdefinitions.
Require Import Coq.micromega.Psatz.

Ltac specialize_arith_hyp H :=
  repeat match type of H with
         | ?G -> _ =>
           let HH := fresh "H" in
           assert G as HH by (psatzl R);
             specialize (H HH); clear HH
         end.
