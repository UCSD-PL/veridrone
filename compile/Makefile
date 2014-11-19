MODULES := Compile
VS := $(MODULES:%=%.v)

.PHONY: coq clean compcert

compcert:
	$(MAKE) -C compcert

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -f ./_CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
