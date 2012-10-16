Require Import MyTactics.
Require Import SetoidClass.
Require Import Lattice.
Require Import Chains.

Lemma is_fixed_point_monotone {T leq} `{JoinPreLattice _ leq} :
  forall (f: T -> T) x,
    monotone f ->
    is_fixed_point f x ->
    is_fixed_point f (f x).
Proof.
intros f x Hf [Hfp1 Hfp2].
split; apply Hf; assumption.
Qed.

Definition join_lift {T leq} `{JoinPreLattice T leq} zero (f: T -> T) :=
  fun x => join zero (f x).
Hint Unfold join_lift.

Lemma join_lift_leq {T leq} `{JoinPreLattice T leq} :
  forall zero (f: T -> T) x, leq zero (join_lift zero f x).
Proof.
intros zero f x. unfold join_lift. apply join_ub1.
Qed.

Lemma join_lift_monotone {T leq} `{JoinPreLattice T leq} :
  forall zero (f: T -> T),
    monotone f ->
    monotone (join_lift zero f).
Proof.
intros zero f Hf x y Hxy.
unfold join_lift.
specialize (Hf _ _ Hxy).
rewrite Hf. reflexivity.
Qed.

Lemma join_lift_fp_leq {T leq} `{JoinPreLattice _ leq} :
  forall zero (f: T -> T) x,
    is_fixed_point (join_lift zero f) x ->
    leq zero x.
Proof.
intros zero f x Hfp. unfold is_fixed_point in Hfp.
rewrite <- Hfp. apply join_ub1.
Qed.

Lemma fixpoint_join_lift {T leq} `{JoinPreLattice _ leq}:
  forall zero (f: T -> T) x,
    leq zero (f zero) ->
    monotone f ->
    ((leq zero x /\ is_fixed_point f x)
     <->
     (is_fixed_point (join_lift zero f) x)).
Proof.
intros zero f x Hzero Hf; split.
* intros [Hzerox Hfp]. destruct Hfp as [Hfp1 Hfp2]. deep_splits.
  + transitivity (f x); trivial.
    unfold join_lift. rewrite <- join_characterization.
    transitivity x; trivial.
  + rewrite Hfp2 at 1; unfold join_lift; auto using join_ub2.
* intros [Hfp1 Hfp2]. unfold join_lift in *.
  assert (leq zero x).
  { transitivity (join zero (f x)); auto using join_ub1. }
  deep_splits; trivial.
  + transitivity (join zero (f x)); trivial. apply join_ub2.
  + transitivity (join zero (f x)); trivial.
    rewrite <- join_characterization.
    transitivity (f zero); trivial.
    apply Hf; trivial.
Qed.

Lemma least_join_lift {T leq} `{JoinPreLattice T leq}:
  forall zero (f: T -> T) x,
    leq zero (f zero) ->
    monotone f ->
    ((forall y, leq zero y -> is_fixed_point f y -> leq x y)
     <->
     (forall y, is_fixed_point (join_lift zero f) y -> leq x y)).
Proof.
intros zero f x Hzero Hf; split; intros Hlfp y Hfy.
* destruct Hfy as [Hfy1 Hfy2]. transitivity (join_lift zero f y); trivial.
  apply Hlfp.
  + apply join_ub1.
  + unfold join_lift in *. split.
    - transitivity (f y); auto using join_ub2.
    - { transitivity (join (f zero) (f y)).
        * rewrite Hzero at 1. reflexivity.
        * apply join_lub; auto using join_ub1. }
* intro Hzeroy. apply Hlfp.
  rewrite <- fixpoint_join_lift; auto.
Qed.

Lemma lfp_join_lift {T leq} `{JoinPreLattice T leq}:
  forall zero (f: T -> T) x,
    leq zero (f zero) ->
    monotone f ->
    ((leq zero x
      /\ is_fixed_point f x
      /\ forall y, leq zero y -> is_fixed_point f y -> leq x y)
     <->
     (is_fixed_point (join_lift zero f) x)
     /\ forall y, is_fixed_point (join_lift zero f) y -> leq x y).
Proof.
intros zero f x Hzero Hf.
pose proof (fixpoint_join_lift zero f x Hzero Hf).
pose proof (least_join_lift zero f x Hzero Hf).
tauto.
Qed.
