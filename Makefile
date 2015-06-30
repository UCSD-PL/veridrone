all: z3-plugin Makefile.coq
	$(MAKE) -f Makefile.coq

z3-plugin:
	$(MAKE) -C Z3-plugin


Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

clean:
	$(MAKE) -C Z3-plugin clean
	$(MAKE) -f Makefile.coq clean

check:
	# Check for z3
	apt-get install coinor-csdp

.PHONEY: all clean
