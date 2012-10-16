Require Import MyTactics.
Require Export Chains.

(** Kleene least fixed point theorem, generalized to an arbitraty starting point. *)
Theorem generalized_kleene_lfp {T leq}
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
pose (HchainSup_Directed := iteration_chain_sup_directed zero f Hzero Hf_monotone).
destruct (join_complete chain) as [sup Hsup].
destruct (Hf_sup_continuous chain sup HchainSup_Directed Hsup)
  as [sup2 [Hsup2IsSup Hsup2Eq]].
exists sup. split; trivial. split.
* split.
  - destruct Hsup2IsSup as [_ Hsup2L].
    rewrite <- Hsup2Eq. apply Hsup2L. destruct Hsup as [HsupUB _].
    apply iteration_chain_upper_bound_im_f; auto.
  - destruct Hsup as [HsupUB HsupL]. apply HsupL.
    apply iteration_chain_upper_bound_f; auto.
    apply HsupUB. exists 0. reflexivity.
* intros y Hzeroy Hy. destruct Hsup as [HsupUB HsupL]. apply HsupL; trivial.
  apply fixed_point_is_upper_bound_chain; trivial.
Qed.

Lemma iterated_fun_sup_continuous {T leq} {L: PreOrder leq}:
  forall (zero: T) (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
    sup_continuous (fun (n: nat) => n_iter f n zero).
Proof.
intros zero f Hzero Hf P nsup Hdir Hsup.
pose (g := fun (n: nat) => n_iter f n zero).
fold g. exists (g nsup). split.
* split.
  + intros R' HR'.
    destruct HR' as [n0 [HPn0 [Hn0R' HR'n0]]].
    transitivity (g n0); trivial.
    destruct Hsup as [HUB HLUB].
    specialize (HUB n0 HPn0).
    unfold g.
    apply (n_iter_monotone zero f Hzero Hf n0 nsup HUB).
  + intros R' HR'. apply HR'.
    exists nsup. split.
    - apply not_empty_is_sup_in; trivial. destruct Hdir; assumption.
    - reflexivity.
* reflexivity.
Qed.

(** * Specialization of the above function to <<zero = bottom>>. *)
Module Bottom.

Lemma n_iter_monotone {T leq} `{L: PreOrder T leq} `{HasBottom T leq}:
  forall (f: T -> T),
    monotone f ->
    monotone (fun n => n_iter f n bottom).
Proof.
intros f Hf. apply n_iter_monotone; trivial.
apply bottom_minimum.
Qed.

Lemma iteration_chain_sup_directed {T leq} `{L: PreOrder T leq} `{HasBottom T leq} :
  forall (f: T -> T),
    monotone f ->
    sup_directed (iteration_chain bottom f).
Proof.
intros f Hf. apply iteration_chain_sup_directed; trivial.
apply bottom_minimum.
Qed.

Lemma n_iter_upper_bound_f {T leq} `{L: PreOrder T leq} `{HasBottom T leq} :
  forall (f: T -> T),
    monotone f ->
    forall b,
      (forall n, leq (n_iter f n bottom) b) ->
      forall n, leq (n_iter f n bottom) (f b).
Proof.
intros f Hf b H0 n.
apply n_iter_upper_bound_f; auto; apply bottom_minimum.
Qed.

Lemma iteration_chain_upper_bound_f {T leq} `{L: PreOrder T leq} `{HasBottom T leq} :
  forall (f: T -> T),
    monotone f ->
    forall b,
      is_upper_bound (iteration_chain bottom f) b ->
      is_upper_bound (iteration_chain bottom f) (f b).
Proof.
intros f Hf b H0.
apply iteration_chain_upper_bound_f; auto; apply bottom_minimum.
Qed.

Lemma iteration_chain_upper_bound_im_f {T leq} `{L: PreOrder T leq} `{HasBottom T leq} :
  forall (f: T -> T),
    monotone f ->
    forall b,
      is_upper_bound (iteration_chain bottom f) b ->
      is_upper_bound (im f (iteration_chain bottom f)) b.
Proof.
intros f Hf b H0.
apply iteration_chain_upper_bound_im_f; auto using bottom_minimum.
Qed.

Lemma fixed_point_is_upper_bound_chain {T leq} `{L: PreOrder T leq} `{HasBottom T leq} :
  forall (f: T -> T),
    monotone f ->
    forall x,
      is_fixed_point f x ->
      is_upper_bound (iteration_chain bottom f) x.
Proof.
intros f Hf x H0.
apply fixed_point_is_upper_bound_chain; auto; apply bottom_minimum.
Qed.

(** Kleene least fixed point theorem. *)
Theorem kleene_lfp {T leq}
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
     (generalized_kleene_lfp bottom f (bottom_minimum (f bottom)) Hf)
  as HKleene.
destruct HKleene as [sup [Hsup [Hfp Hlfp]]].
exists sup. splits; auto.
* intros y Hy. apply Hlfp; trivial. apply bottom_minimum.
Qed.

Lemma iterated_fun_sup_continuous {T leq} {L: PreOrder leq}
      `{HasBottom T leq} :
  forall (f: T -> T),
    monotone f ->
    sup_continuous (fun (n: nat) => n_iter f n bottom).
Proof.
intros f Hf.
apply iterated_fun_sup_continuous; auto; apply bottom_minimum.
Qed.

End Bottom.

(* TODO: gfp *)
