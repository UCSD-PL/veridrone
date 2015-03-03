MODULES :=  src/z3Tactic.ml4 src/Tactic.v src/Test.v
NAME := Z3
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
