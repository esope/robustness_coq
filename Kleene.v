Require Import MyTactics.
Require Import PreLattice.
Require Import Chains.

(** * Kleene least fixed point theorems. *)
Module Lfp.
(** Kleene least fixed point theorem, generalized to an arbitraty starting point. *)
Theorem generalized_kleene {T leq} `{JoinCompletePreLattice T leq} :
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
Theorem kleene {T leq} `{JoinCompletePreLattice T leq} `{HasBottom T leq}:
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

(** * Kleene greatest fixed point theorems. *)
Module Gfp.

(** Kleene greatest fixed point theorem, generalized to an arbitraty starting point. *)
Theorem generalized_kleene {T leq} `{MeetCompletePreLattice T leq} :
  forall zero (f: T -> T),
    leq (f zero) zero ->
    inf_continuous f ->
    { inf |
      is_inf (iteration_chain zero f) inf
      /\ is_fixed_point f inf
      /\ (forall y, leq y zero -> is_fixed_point f y -> leq y inf) }.
Proof.
intros zero f Hzero Hf_inf_continuous.
assert (monotone f) as Hf_monotone by (apply inf_continuous_monotone; trivial).
pose (chain := iteration_chain zero f).
pose (HchainInf_Directed :=
        Descending.iteration_chain_inf_directed zero f Hzero Hf_monotone).
destruct (meet_complete chain) as [inf Hinf].
destruct (Hf_inf_continuous chain inf HchainInf_Directed Hinf)
  as [inf2 [Hinf2IsInf Hinf2Eq]].
exists inf. split; trivial. split.
* split.
  - destruct Hinf as [HinfLB HinfG]. apply HinfG.
    apply Descending.iteration_chain_lower_bound_f; auto.
    apply HinfLB. exists 0. reflexivity.
  - destruct Hinf2IsInf as [? Hinf2G].
    rewrite <- Hinf2Eq. apply Hinf2G. destruct Hinf as [HinfLB _].
    apply Descending.iteration_chain_lower_bound_im_f; auto.
* intros y Hzeroy Hy. destruct Hinf as [HinfLB HinfG]. apply HinfG; trivial.
  apply Descending.fixed_point_is_lower_bound_chain; trivial.
Qed.

(** Kleene greatest fixed point theorem. *)
Theorem kleene {T leq} `{MeetCompletePreLattice T leq} `{HasTop T leq}:
  forall (f: T -> T),
    inf_continuous f ->
    { inf |
      is_inf (iteration_chain top f) inf
      /\ is_fixed_point f inf
      /\ (forall y, is_fixed_point f y -> leq y inf) }.
Proof.
intros f Hf.
pose proof
     (generalized_kleene top f (top_maximum (f top)) Hf)
  as HKleene.
destruct HKleene as [inf [Hinf [Hfp Hlfp]]].
exists inf. splits; auto.
* intros y Hy. apply Hlfp; trivial. apply top_maximum.
Qed.

End Gfp.
