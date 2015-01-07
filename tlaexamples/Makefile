MODULES := AbstractOneDimVelCtrl AbstractOneDimAccCtrl AbstractIndAccCtrl AbstractOneDimAccCtrl2 AbstractOneDimAccCtrl3
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R ../tla TLA -R ../Z3-plugin Exploit -R . Modules $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
