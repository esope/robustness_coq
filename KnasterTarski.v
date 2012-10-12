Require Import MyTactics.
Require Import Lattice.
Require Import SetLattice.
Require Import Ordinals.

Theorem tarski_greatest_fixed_point {T order}
        `{L: CompletePreLattice T order} `{B: BottomPreLattice T order}:
  forall (f: T -> T),
    monotone f ->
    exists sup,
      is_fixed_point f sup
      /\ (forall y, is_fixed_point f y -> leq y sup).
Proof.
intros f Hf.
pose (P := fun t : T => leq t (f t)).
destruct (complete_def P) as [sup [HUB HLUB]].
exists sup.
assert (leq sup (f sup)) as H.
{ apply HLUB. intros t Ht. transitivity (f t); trivial.
  apply Hf. apply HUB; trivial.
}
 deep_splits; trivial.
* apply HUB. unfold P. apply Hf. trivial.
* intros t Ht. apply HUB. unfold P. destruct Ht; assumption.
Qed.

Fixpoint trans_iter {T order} {L: CompletePreLattice T order}
           (f: T -> T) (o: Ord) (zero : T) : T :=
  match o with
    | O_Ord => zero
    | S_Ord o' => f (trans_iter f o' zero)
    | lim_Ord os =>
      let (sup, _) :=
          (complete_def (fun t : T => exists n, t = trans_iter f (os n) zero))
      in sup
  end.
