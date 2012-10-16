Robust Declassification
==========

Verification in Coq of the article
[Robust Declassification](http://www.cis.upenn.edu/~stevez/papers/ZM01b.pdf)
by Zdancewic and Myers.

Script compatible with [Coq 8.4](http://coq.inria.fr).

# Requirements:

* GNU make
* [Coq 8.4](http://coq.inria.fr)

# To build the files and generate the documentation:

Just type `make` and wait.
The documentation is placed in the `html/` subdirectory.

The command `make check` runs `coqchk` on the development.

The command `make wc` gives statistics about the development.

# Contents of the files

* `Chains.v`: Facts about ascending and descending finite chains.
* `EquivClass.v`: Facts about equivalence classes.
* `ERLattice.v`: Lattice of equivalence relations.
* `Examples.v`: Examples from the paper.
* `Fixpoints.v`: Facts about fixed points and relative fixed points.
* `Kleene.v`: Kleene fixed point theorems.
* `KnasterTarski.v`: Knaster-Tarski fixed point theorems.
* `Lattice.v`: Definitions about lattices.
* `LICENSE`: License file (MIT).
* `Makefile`: Makefile used to build the development.
* `MyList.v`: Extra facts about lists.
* `MyTactics.v`: Extra tactics.
* `NatLattice.v`: Lattice of natural numbers.
* `Ordinals.v`: Countable ordinals and their ordering relation.
* `PERLattice.v`: Lattice of partial equivalence relations.
* `README.md`: This file.
* `RelLattice.v`: Lattice of relations.
* `Robustness.v`: The core results of the paper.
* `SetLattice.v`: The lattice of sets.
* `SetPredicates.v`: Some predicates on sets.
* `Stutter.v`: Definition and facts about stuttering on finite lists.
* `TransfiniteChains.v`: Ascending and descending (countably) transfinite chains.
