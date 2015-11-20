VeriDrone
==========

This contains the code for our PLDI 2016 submission entitled "Modular Reasoning about Cyber-physical Systems."

To build the code, install the dependencies (see below) and then run make in the root directory.

Directory Structure
-------------------
This project contains three directories:

1. logic - the embedding of our logic, proof rules, automation, and some arithmetic facts
2. examples - our Sys abstraction and proof rules for our Sys (System.v) as well as various systems specified and verified using Sys.
3. Z3-plugin - a plugin for running Z3 on real arithmetic goals from Coq.

Dependencies
------------

You will need csdp:
```
apt-get install coinor-csdp
```

Coq Dependencies
----------------

ExtLib

Charge (revision a21ed562baf247c8bc5677fc55a594325799e193)
You can get this by running ```./get-charge.sh``
