VeriDrone
==========

Dependencies
------------

You will need csdp:
```
apt-get install coinor-csdp
```

And you will need Z3, which you can get here:

[[https://github.com/Z3Prover/z3/releases]]

Coq Dependencies
----------------

This development uses Coq 8.5. All of the Coq dependencies, along with Coq itself, can be installed using OPAM [[http://coq.io/opam/get_started.html]]. You must install the following packages from Coq OPAM:

- coq-ext-lib
- coq-charge-core
- coq-smt-check

Directory Structure
-------------------
This project contains three directories:

1. logic - our embedding of LTL, proof rules, automation, and some arithmetic facts
2. examples - our Sys abstraction and proof rules for our Sys (System.v) as well as various systems specified and verified using Sys.
