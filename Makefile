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

COQDOCFLAGS="--light --interpolate --utf8 --lib-subtitles"
COQCHKFLAGS="-admit Omega -silent -o"

.PHONY: coq doc graph clean

all: coq_and_doc

coq: Makefile.coq
	@echo "*******************************************************"
	@echo "Typechecking the Coq development..."
	@echo "*******************************************************"
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile
	@echo "*******************************************************"
	@echo "Generating Makefile..."
	@echo "*******************************************************"
	coq_makefile $(VS) COQDOCFLAGS = $(COQDOCFLAGS) COQCHKFLAGS = $(COQCHKFLAGS) -install none -opt -o Makefile.coq

clean: Makefile.coq
	@echo "*******************************************************"
	@echo "Cleaning..."
	@echo "*******************************************************"
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -C ocamldot clean
	rm -f Makefile.coq .depend *~ *.glob *.v.d *.vo

coq_and_doc: coq
	$(MAKE) doc

doc:
	@echo "*******************************************************"
	@echo "Building documentation..."
	@echo "*******************************************************"
	$(MAKE) -f Makefile.coq html
	cp coqdoc.css html/
	$(MAKE) graph

graph:	html/toc.svg

html/toc.svg:	ocamldot/ocamldot $(MODULES:%=%.v.d)
	cat *.v.d | ocamldot/ocamldot -urls '.html' > html/graph.dot
	dot -Tsvg -o html/toc.svg html/graph.dot

ocamldot/ocamldot:
	$(MAKE) -C ocamldot

validate:	coq
	@echo "*******************************************************"
	@echo "Validating the Coq development. This might take time..."
	@echo "*******************************************************"
	$(MAKE) -f Makefile.coq validate

wc:
	coqwc -p $(VS)
