Require Import MyTactics.
Require Import SetoidClass.
Require Import Lattice.

(** Some basic results about fixed points. *)

Lemma is_fixed_point_monotone {T leq} `{JoinPreLattice _ leq} :
  forall (f: T -> T) x,
    monotone f ->
    is_fixed_point f x ->
    is_fixed_point f (f x).
Proof.
intros f x Hf [Hfp1 Hfp2].
split; apply Hf; assumption.
Qed.

(** * Least fixed point above a given point. *)
Module Lfp.

Definition lift {T leq} `{JoinPreLattice T leq} zero (f: T -> T) :=
  fun x => join zero (f x).
Hint Unfold lift.

Lemma lift_leq {T leq} `{JoinPreLattice T leq} :
  forall zero (f: T -> T) x, leq zero (lift zero f x).
Proof.
intros zero f x. unfold lift. apply join_ub1.
Qed.

Lemma lift_monotone {T leq} `{JoinPreLattice T leq} :
  forall zero (f: T -> T),
    monotone f ->
    monotone (lift zero f).
Proof.
intros zero f Hf x y Hxy.
unfold lift.
specialize (Hf _ _ Hxy).
rewrite Hf. reflexivity.
Qed.

Lemma lift_fp_leq {T leq} `{JoinPreLattice _ leq} :
  forall zero (f: T -> T) x,
    is_fixed_point (lift zero f) x ->
    leq zero x.
Proof.
intros zero f x Hfp. unfold is_fixed_point in Hfp.
rewrite <- Hfp. apply join_ub1.
Qed.

Lemma fixpoint_iff {T leq} `{JoinPreLattice _ leq}:
  forall zero (f: T -> T) x,
    leq zero (f zero) ->
    monotone f ->
    ((leq zero x /\ is_fixed_point f x)
     <->
     (is_fixed_point (lift zero f) x)).
Proof.
intros zero f x Hzero Hf; split.
* intros [Hzerox Hfp]. destruct Hfp as [Hfp1 Hfp2]. deep_splits.
  + transitivity (f x); trivial.
    unfold lift. rewrite <- join_characterization.
    transitivity x; trivial.
  + rewrite Hfp2 at 1; unfold lift; auto using join_ub2.
* intros [Hfp1 Hfp2]. unfold lift in *.
  assert (leq zero x).
  { transitivity (join zero (f x)); auto using join_ub1. }
  deep_splits; trivial.
  + transitivity (join zero (f x)); trivial. apply join_ub2.
  + transitivity (join zero (f x)); trivial.
    rewrite <- join_characterization.
    transitivity (f zero); trivial.
    apply Hf; trivial.
Qed.

Lemma least_iff {T leq} `{JoinPreLattice T leq}:
  forall zero (f: T -> T) x,
    leq zero (f zero) ->
    monotone f ->
    ((forall y, leq zero y -> is_fixed_point f y -> leq x y)
     <->
     (forall y, is_fixed_point (lift zero f) y -> leq x y)).
Proof.
intros zero f x Hzero Hf; split; intros Hlfp y Hfy.
* destruct Hfy as [Hfy1 Hfy2]. transitivity (lift zero f y); trivial.
  apply Hlfp.
  + apply join_ub1.
  + unfold lift in *. split.
    - transitivity (f y); auto using join_ub2.
    - { transitivity (join (f zero) (f y)).
        * rewrite Hzero at 1. reflexivity.
        * apply join_lub; auto using join_ub1. }
* intro Hzeroy. apply Hlfp.
  rewrite <- fixpoint_iff; auto.
Qed.

Lemma lfp_iff {T leq} `{JoinPreLattice T leq}:
  forall zero (f: T -> T) x,
    leq zero (f zero) ->
    monotone f ->
    ((leq zero x
      /\ is_fixed_point f x
      /\ forall y, leq zero y -> is_fixed_point f y -> leq x y)
     <->
     (is_fixed_point (lift zero f) x)
     /\ forall y, is_fixed_point (lift zero f) y -> leq x y).
Proof.
intros zero f x Hzero Hf.
pose proof (fixpoint_iff zero f x Hzero Hf).
pose proof (least_iff zero f x Hzero Hf).
tauto.
Qed.

End Lfp.

(** * Greatest fixed point below a given point. *)
Module Gfp.

Definition lift {T leq} `{MeetPreLattice T leq} zero (f: T -> T) :=
  fun x => meet zero (f x).
Hint Unfold lift.

Lemma lift_leq {T leq} `{MeetPreLattice T leq} :
  forall zero (f: T -> T) x, leq (lift zero f x) zero.
Proof.
intros zero f x. unfold lift. apply meet_lb1.
Qed.

Lemma lift_monotone {T leq} `{MeetPreLattice T leq} :
  forall zero (f: T -> T),
    monotone f ->
    monotone (lift zero f).
Proof.
intros zero f Hf x y Hxy.
unfold lift.
specialize (Hf _ _ Hxy).
rewrite Hf. reflexivity.
Qed.

Lemma lift_fp_leq {T leq} `{MeetPreLattice _ leq} :
  forall zero (f: T -> T) x,
    is_fixed_point (lift zero f) x ->
    leq x zero.
Proof.
intros zero f x Hfp. unfold is_fixed_point in Hfp.
rewrite <- Hfp. apply meet_lb1.
Qed.

Lemma fixpoint_iff {T leq} `{MeetPreLattice _ leq}:
  forall zero (f: T -> T) x,
    leq (f zero) zero ->
    monotone f ->
    ((leq x zero /\ is_fixed_point f x)
     <->
     (is_fixed_point (lift zero f) x)).
Proof.
intros zero f x Hzero Hf; split.
* intros [Hzerox Hfp]. destruct Hfp as [Hfp1 Hfp2]. deep_splits.
  + unfold lift; rewrite Hfp1 at 1; auto using meet_lb2.
  + transitivity (f x); trivial.
    unfold lift. rewrite meet_comm.
    rewrite <- meet_characterization.
    transitivity x; trivial.
* intros [Hfp1 Hfp2]. unfold lift in *.
  assert (leq x zero).
  { transitivity (meet zero (f x)); auto using meet_lb1. }
  deep_splits; trivial.
  + transitivity (meet zero (f x)); trivial.
    rewrite meet_comm.
    rewrite <- meet_characterization.
    transitivity (f zero); trivial.
    apply Hf; trivial.
  + transitivity (meet zero (f x)); trivial. apply meet_lb2.
Qed.

Lemma greatest_iff {T leq} `{MeetPreLattice T leq}:
  forall zero (f: T -> T) x,
    leq (f zero) zero ->
    monotone f ->
    ((forall y, leq y zero -> is_fixed_point f y -> leq y x)
     <->
     (forall y, is_fixed_point (lift zero f) y -> leq y x)).
Proof.
intros zero f x Hzero Hf; split; intros Hlfp y Hfy.
* destruct Hfy as [Hfy1 Hfy2]. transitivity (lift zero f y); trivial.
  apply Hlfp.
  + apply meet_lb1.
  + unfold lift in *. split.
    - { transitivity (meet (f zero) (f y)).
        * apply meet_glb; auto using meet_lb1.
        * rewrite Hzero at 1. reflexivity. }
    - transitivity (f y); auto using meet_lb2.
* intro Hzeroy. apply Hlfp.
  rewrite <- fixpoint_iff; auto.
Qed.

Lemma gfp_iff {T leq} `{MeetPreLattice T leq}:
  forall zero (f: T -> T) x,
    leq (f zero) zero ->
    monotone f ->
    ((leq x zero
      /\ is_fixed_point f x
      /\ forall y, leq y zero -> is_fixed_point f y -> leq y x)
     <->
     (is_fixed_point (lift zero f) x)
     /\ forall y, is_fixed_point (lift zero f) y -> leq y x).
Proof.
intros zero f x Hzero Hf.
pose proof (fixpoint_iff zero f x Hzero Hf).
pose proof (greatest_iff zero f x Hzero Hf).
tauto.
Qed.

End Gfp.
