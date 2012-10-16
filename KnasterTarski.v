Require Import MyTactics.
Require Import PreLattice.
Require Import SetLattice.
Require Export Ordinals.
Require Export Fixpoints.

(** * Knaster-Tarski least fixed point. *)
Module Lfp.

Theorem knaster_tarski {T leq}
        `{L: MeetCompletePreLattice T leq} :
  forall (f: T -> T),
    monotone f ->
    { fp |
      is_fixed_point f fp
      /\ (forall y, is_fixed_point f y -> leq fp y) }.
Proof.
intros f Hf.
pose (P := fun t : T => leq (f t) t).
destruct (meet_complete P) as [inf [HLB HGLB]].
exists inf.
assert (leq (f inf) inf) as Hinf.
{ apply HGLB. intros t Ht. transitivity (f t); trivial.
  apply Hf. apply HLB; trivial.
}
 deep_splits; trivial.
* apply HLB. unfold P. apply Hf. trivial.
* intros t Ht. apply HLB. unfold P. destruct Ht; assumption.
Qed.

Theorem generalized_knaster_tarski {T leq}
        {O: PreOrder leq}
        {J: @JoinPreLattice T leq O}
        {M: @MeetCompletePreLattice T leq O} :
  forall zero (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
    { fp |
      leq zero fp
      /\ is_fixed_point f fp
      /\ (forall y, leq zero y -> is_fixed_point f y -> leq fp y) }.
Proof.
intros zero f Hzero Hf.
pose proof
     (knaster_tarski
        (Lfp.lift zero f)
        (Lfp.lift_monotone zero f Hf)) as Hfp.
destruct Hfp as [fp [Hfp Hlfp]].
exists fp.
rewrite (Lfp.lfp_iff zero f fp Hzero Hf).
auto.
Qed.

End Lfp.

(** * Knaster-Tarski greatest fixed point. *)
Module Gfp.

Theorem knaster_tarski {T leq}
        `{L: JoinCompletePreLattice T leq} :
  forall (f: T -> T),
    monotone f ->
    { fp |
      is_fixed_point f fp
      /\ (forall y, is_fixed_point f y -> leq y fp) }.
Proof.
intros f Hf.
pose (P := fun t : T => leq t (f t)).
destruct (join_complete P) as [sup [HUB HLUB]].
exists sup.
assert (leq sup (f sup)) as Hsup.
{ apply HLUB. intros t Ht. transitivity (f t); trivial.
  apply Hf. apply HUB; trivial.
}
 deep_splits; trivial.
* apply HUB. unfold P. apply Hf. trivial.
* intros t Ht. apply HUB. unfold P. destruct Ht; assumption.
Qed.

End Gfp.
