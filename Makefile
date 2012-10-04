MODULES := MyTactics \
	   Lattice Kleene \
           NatLattice SetLattice RelLattice PERLattice ERLattice \
           Stutter View Robustness

VS 	:= $(MODULES:%=%.v)

COQDOCFLAGS="--gallina --interpolate --utf8"

.PHONY: coq doc clean

all: coq doc

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS:%=%)
	coq_makefile $(VS) COQDOCFLAGS = $(COQDOCFLAGS) -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

doc:
	$(MAKE) -f Makefile.coq html
