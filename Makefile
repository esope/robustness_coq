MODULES := MyTactics MyList \
	   EquivClass SetPredicates \
	   PreLattice Fixpoints \
	   Chains Kleene \
	   Ordinals TransfiniteChains \
	   KnasterTarski \
	   NatLattice SetLattice RelLattice PERLattice ERLattice \
	   Stutter Robustness \
	   Examples

VS 	:= $(MODULES:%=%.v)

COQDOCFLAGS="--light --interpolate --utf8"

.PHONY: coq doc clean

all: coq doc

coq: Makefile.coq
	@echo "*******************************************************"
	@echo "Typechecking the Coq development..."
	@echo "*******************************************************"
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS:%=%)
	@echo "*******************************************************"
	@echo "Generating Makefile..."
	@echo "*******************************************************"
	coq_makefile $(VS) COQDOCFLAGS = $(COQDOCFLAGS) -o Makefile.coq

clean: Makefile.coq
	@echo "*******************************************************"
	@echo "Cleaning..."
	@echo "*******************************************************"
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend *~ *.glob *.v.d ^.vo

doc:
	@echo "*******************************************************"
	@echo "Building documentation..."
	@echo "*******************************************************"
	$(MAKE) -f Makefile.coq html

check:	coq
	@echo "*******************************************************"
	@echo "Checking the Coq development. This might take time..."
	@echo "*******************************************************"
	coqchk -silent -o -m $(MODULES)

wc:
	coqwc -p $(VS)
