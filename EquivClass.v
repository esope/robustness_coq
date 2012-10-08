Require Import MyTactics.
Require Import RelationClasses.
Require Import Relations.
Require Import Ensembles.

(** Equivalence classes. *)

Definition class {A} (R: relation A) (x: A) := R x.
Hint Unfold class.

Lemma class_eq_inv {A} {R: relation A} {E: Equivalence R} :
  forall (x y: A),
    class R x = class R y ->
    R x y.
Proof.
intros x y H.
fold (class R x). rewrite H.
reflexivity.
Qed.

Lemma class_eq_compat {A} {R: relation A} {E: Equivalence R} :
  forall (x y: A),
    R x y ->
    class R x = class R y.
Proof.
intros x y H. apply Extensionality_Ensembles.
split; intros z Hz; compute; compute in Hz.
* transitivity x; trivial. symmetry; trivial.
* transitivity y; trivial.
Qed.

Lemma class_trans_R {A} {R: relation A} {E: Equivalence R} :
  forall (x y z: A),
    In _ (class R x) z ->
    In _ (class R y) z ->
    R x y.
Proof.
intros x y z Hx Hy. compute in Hx. compute in Hy.
transitivity z; trivial. symmetry; trivial.
Qed.

Lemma class_trans_eq {A} {R: relation A} {E: Equivalence R} :
  forall (x y z: A),
    In _ (class R x) z ->
    In _ (class R y) z ->
    class R x = class R y.
Proof.
intros x y z Hx Hy. apply class_eq_compat.
compute in Hx. compute in Hy. transitivity z; trivial. symmetry; trivial.
Qed.

Lemma class_sym {A} {R: relation A} {E: Equivalence R} :
  forall (x y: A),
    In _ (class R x) y ->
    In _ (class R y) x.
Proof.
compute. intros x y H. symmetry. trivial.
Qed.

Lemma class_refl {A} {R: relation A} {E: Equivalence R} :
  forall x, In _ (class R x) x.
Proof.
intros x. compute. reflexivity.
Qed.

Lemma class_included_rel {A}
      (R1: relation A) {E1: Equivalence R1}
      (R2: relation A) {E2: Equivalence R2} :
  inclusion _ R1 R2 ->
  forall x,
  Included _ (class R1 x) (class R2 x).
Proof.
intros H x y Hy. apply H. assumption.
Qed.

Lemma class_eq_rel {A}
      (R1: relation A) {E1: Equivalence R1}
      (R2: relation A) {E2: Equivalence R2} :
  same_relation _ R1 R2 ->
  forall x,
  class R1 x = class R2 x.
Proof.
intros [H1 H2] x. apply Extensionality_Ensembles.
split; apply class_included_rel; trivial.
Qed.

Lemma class_eq_included_rel {A}
      (R1: relation A) {E1: Equivalence R1}
      (R2: relation A) {E2: Equivalence R2} :
  inclusion _ R1 R2 ->
  forall x y,
    class R1 x = class R1 y ->
    class R2 x = class R2 y.
Proof.
intros H x y H1.
apply class_eq_compat. apply H.
apply class_eq_inv. assumption.
Qed.
