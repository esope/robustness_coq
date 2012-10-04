MODULES := MyTactics \
	   Lattice Kleene \
           NatLattice SetLattice RelLattice PERLattice ERLattice \
           Robustness

VS 	:= $(MODULES:%=%.v)

.PHONY: coq doc clean

all: coq doc

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS:%=%)
	echo $(VS)
	coq_makefile $(VS) -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

doc:
	$(MAKE) -f Makefile.coq html
