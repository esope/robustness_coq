Require Import Lattice.
Require Import Arith.

Instance NatPreLattice : PreLattice nat le := {
  join := max
; meet := min
}.
Proof.
* auto with arith.
* auto with arith.
* auto using Max.max_lub.
* auto with arith.
* auto with arith.
* auto using Min.min_glb.
Defined.

Instance NatBottomPreLattice : BottomPreLattice nat le :=
{ bottom := 0 }.
Proof.
intro t. unfold leq. auto with arith.
Qed.
