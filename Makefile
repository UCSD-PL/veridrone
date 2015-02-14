all:
	$(MAKE) -C Z3-plugin
	$(MAKE) -C tla
	$(MAKE) -C tlaexamples

clean:
	$(MAKE) -C Z3-plugin clean
	$(MAKE) -C tla clean
	$(MAKE) -C tlaexamples clean

check:
	# Check for z3
	apt-get install coinor-csdp
