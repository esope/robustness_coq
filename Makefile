MODULES := MyTactics MyList \
	   EquivClass SetPredicates \
	   Lattice Kleene \
           NatLattice SetLattice RelLattice PERLattice ERLattice \
	   Ordinals KnasterTarski \
           Stutter Robustness \
           Examples

VS 	:= $(MODULES:%=%.v)

COQDOCFLAGS="--light --interpolate --utf8"

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
