(* Exports all of the proof rules. The files
   contain the following proof rules:

     TLA.BasicProofRules: proof rules about
       TLA that are not specific to our domain,
       namely general propositional logic rules
       and temporal logic rules including a
       discrete induction rule

     TLA.DifferentialInduction: differential
       induction

     TLA.ContinuousProofRules: proof rules
       specific to our domain, in particular
       about continuous transitions, but not
       including basic differential induction
       (but including a corollary of differential
        induction)
*)

Require Export TLA.BasicProofRules.
Require Export TLA.DifferentialInduction.
Require Export TLA.ContinuousProofRules.