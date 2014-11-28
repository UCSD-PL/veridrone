MODULES :=  src/z3Tactic.ml4 src/Exploit.v test-suite/Example.v
NAME := Exploit
ROOT := ./
.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	coq_makefile -R $(ROOT)/src $(NAME) \
		     $(MODULES) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
