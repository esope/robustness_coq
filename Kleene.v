Require Import MyTactics.
Require Import Lattice.
Require Import Chains.

(** * Kleene least fixed point theorems. *)
Module Lfp.
(** Kleene least fixed point theorem, generalized to an arbitraty starting point. *)
Theorem generalized_kleene {T leq}
        `{PreOrder T leq}
        `{L: JoinCompletePreLattice T leq} :
  forall zero (f: T -> T),
    leq zero (f zero) ->
    sup_continuous f ->
    { sup |
      is_sup (iteration_chain zero f) sup
      /\ is_fixed_point f sup
      /\ (forall y, leq zero y -> is_fixed_point f y -> leq sup y) }.
Proof.
intros zero f Hzero Hf_sup_continuous.
assert (monotone f) as Hf_monotone by (apply sup_continuous_monotone; trivial).
pose (chain := iteration_chain zero f).
pose (HchainSup_Directed :=
        Ascending.iteration_chain_sup_directed zero f Hzero Hf_monotone).
destruct (join_complete chain) as [sup Hsup].
destruct (Hf_sup_continuous chain sup HchainSup_Directed Hsup)
  as [sup2 [Hsup2IsSup Hsup2Eq]].
exists sup. split; trivial. split.
* split.
  - destruct Hsup2IsSup as [_ Hsup2L].
    rewrite <- Hsup2Eq. apply Hsup2L. destruct Hsup as [HsupUB _].
    apply Ascending.iteration_chain_upper_bound_im_f; auto.
  - destruct Hsup as [HsupUB HsupL]. apply HsupL.
    apply Ascending.iteration_chain_upper_bound_f; auto.
    apply HsupUB. exists 0. reflexivity.
* intros y Hzeroy Hy. destruct Hsup as [HsupUB HsupL]. apply HsupL; trivial.
  apply Ascending.fixed_point_is_upper_bound_chain; trivial.
Qed.

(** Kleene least fixed point theorem. *)
Theorem kleene {T leq}
        `{PreOrder T leq}
        `{L: JoinCompletePreLattice T leq} `{B: HasBottom T leq}:
  forall (f: T -> T),
    sup_continuous f ->
    { sup |
      is_sup (iteration_chain bottom f) sup
      /\ is_fixed_point f sup
      /\ (forall y, is_fixed_point f y -> leq sup y) }.
Proof.
intros f Hf.
pose proof
     (generalized_kleene bottom f (bottom_minimum (f bottom)) Hf)
  as HKleene.
destruct HKleene as [sup [Hsup [Hfp Hlfp]]].
exists sup. splits; auto.
* intros y Hy. apply Hlfp; trivial. apply bottom_minimum.
Qed.

End Lfp.

Module Gfp.
(** TODO *)
End Gfp.
