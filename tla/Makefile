MODULES := Syntax Semantics Lib ProofRules Tactics ArithFacts Substitution
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R ../Z3-plugin Exploit -R . TLA $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
