(** Predicates over sets. *)
Require Import MyTactics.
Require Import Relations.
Require Import RelationClasses.

(** * Inclusion *)
Definition set_included {A} (R: relation A) (S1 S2: A -> Prop) :=
  forall s1, S1 s1 -> exists s2, S2 s2 /\ R s1 s2.

Definition set_equiv {A} (R: relation A) (S1 S2: A -> Prop) :=
  set_included R S1 S2 /\ set_included R S2 S1.

Instance set_included_PreOrder {A} {R: relation A} `{Equivalence A R}:
  PreOrder (set_included R).
Proof.
constructor.
* intros X x Hx; exists x; split; auto.
* intros X Y Z HXY HYZ x Hx.
  destruct (HXY x Hx) as [y [Hy Hxy]].
  destruct (HYZ y Hy) as [z [Hz Hyz]].
  exists z. split. assumption. transitivity y; assumption.
Qed.

(** * Equivalence *)
Instance set_equiv_Equivalence {A} {R: relation A} `{Equivalence A R}:
  Equivalence (set_equiv R).
Proof.
constructor.
* intro X; split; reflexivity.
* intros X Y [HXY HYX]; split; intros ? ?; auto.
* intros X Y Z [HXY HYX] [HYZ HZY]; split;
  transitivity Y; auto.
Qed.

Lemma set_included_subrel {A} :
  forall (R1 R2: relation A) (E E': A -> Prop),
    (forall x y, R1 x y -> R2 x y) ->
    set_included R1 E E' ->
    set_included R2 E E'.
Proof.
intros R1 R2 E E' H H1.
intros x Hx.
destruct (H1 x Hx) as [y [Hy Hxy]].
exists y. split; auto.
Qed.

Lemma set_equiv_subrel {A} :
  forall (R1 R2: relation A) (E E': A -> Prop),
    (forall x y, R1 x y -> R2 x y) ->
    set_equiv R1 E E' ->
    set_equiv R2 E E'.
Proof.
intros R1 R2 E E' H [H1 H1'].
split; eapply set_included_subrel; eauto.
Qed.


(** * Compatibility with some relations. *)
Lemma set_included_R2_compat {A}
      (R1: relation A) {E1: Equivalence R1}
      (R2: relation A) {E2: Equivalence R2} :
  forall (x y: A),
    R2 x y ->
    set_included R1 (R2 x) (R2 y).
Proof.
intros x y H z Hz. exists z. split; auto.
transitivity x; trivial. symmetry; trivial.
Qed.

Lemma set_equiv_R2_compat {A}
      (R1: relation A) {E1: Equivalence R1}
      (R2: relation A) {E2: Equivalence R2} :
  forall (x y: A),
    R2 x y ->
    set_equiv R1 (R2 x) (R2 y).
Proof.
intros x y H. split; apply set_included_R2_compat; auto.
symmetry; trivial.
Qed.

Lemma set_equiv_view_equiv_rel {A}
  (R: relation A) {E: Equivalence R}
  (R1: relation A) {E1: Equivalence R1}
  (R2: relation A) {E2: Equivalence R2}:
  forall x y : A,
  (forall z t, R1 z t <-> R2 z t) ->
  set_equiv R (R1 x) (R1 y) ->
  set_equiv R (R2 x) (R2 y).
Proof.
intros x y H H1. split.
* intros z Hxz. rewrite <- H in Hxz.
  destruct H1 as [H1 _].
  specialize (H1 _ Hxz).
  destruct H1 as [t [? ?]]. exists t. split; trivial.
  rewrite <- H; trivial.
* intros z Hyz. rewrite <- H in Hyz.
  destruct H1 as [_ H1].
  specialize (H1 _ Hyz).
  destruct H1 as [t [? ?]]. exists t. split; trivial.
  rewrite <- H; trivial.
Qed.

Definition commute {A} (R1: relation A) (R2: relation A) :=
  forall (x y z : A),
    R1 x y ->
    R2 y z ->
    exists y', R2 x y' /\ R1 y' z.

Lemma set_included_subrel' {A}
  (R: relation A) {E: Equivalence R}
  (R1: relation A) {E1: Equivalence R1}
  (R2: relation A) {E2: Equivalence R2}:
  forall x y : A,
  (forall z t, R1 z t -> R2 z t) ->
  commute R R2 ->
  set_included R (R1 x) (R1 y) ->
  set_included R (R1 y) (R1 x) ->
  set_included R (R2 x) (R2 y).
Proof.
intros x y H12 Hcomm H1 H1' z Hxz.
destruct (H1 x) as [t [Hyt Hxt]]; auto.
symmetry in Hxt.
pose proof (Hcomm _ _ _ Hxt Hxz) as [z0 [Htz0 Hz0z]].
exists z0. split.
- transitivity t; auto.
- symmetry; trivial.
Qed.

Lemma set_equiv_subrel' {A}
  (R: relation A) {E: Equivalence R}
  (R1: relation A) {E1: Equivalence R1}
  (R2: relation A) {E2: Equivalence R2}:
  forall x y : A,
  (forall z t, R1 z t -> R2 z t) ->
  commute R R2 ->
  set_equiv R (R1 x) (R1 y) ->
  set_equiv R (R2 x) (R2 y).
Proof.
intros x y H12 Hcomm [H1 H1'].
split; apply (set_included_subrel' _ R1 R2); auto.
Qed.
