MODULES :=  src/clight_degen.ml4 src/clight_degen.v
NAME := clight_degen
ROOT := ./
.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	coq_makefile -R $(ROOT)/src $(NAME) \
		-I ../compcert/_build/cfrontend \
		$(MODULES) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

#		-I ../compcert/_build/common \
#-R ../compcert/_build/common Ccommon\
#-R ../compcert/_build/driver Cdriver\
#-R ../compcert/_build/backend Cbackend\
#-R ../compcert/_build/ia32 Cia32\
#-R ../compcert/_build/extraction Cextraction\
#-R ../compcert/_build/lib Clib\
#-R ../compcert/_build/exportclight Cexportclight\
#-R ../compcert/_build/cparser Ccparser\
#-R../compcert/_build/cfrontend Ccfrontend\
