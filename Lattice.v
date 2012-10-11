(** A development on pre-lattices, which are the basis of
   information-flow label models. We first show basic properties on
   pre-lattices, then we define a toolbox for building pre-lattices,
   and a couple of basic lattices.

   The itent is to justify the label model-related Haskell code that
   lies in the Breeze interpreter.
*)

Require Import MyTactics.
Require Export RelationClasses.
Require Export SetoidClass.

(** * Definitions *)

Class PreLattice(T: Type)(order : T -> T -> Prop) :=
{ leq := order
; leq_preorder :> PreOrder leq
; join : T -> T -> T
; join_ub1 : forall t1 t2, leq t1 (join t1 t2)
; join_ub2 : forall t1 t2, leq t2 (join t1 t2)
; join_lub : forall t t1 t2, leq t1 t -> leq t2 t -> leq (join t1 t2) t
; meet : T -> T -> T
; meet_lb1 : forall t1 t2, leq (meet t1 t2) t1
; meet_lb2 : forall t1 t2, leq (meet t1 t2) t2
; meet_glb : forall t t1 t2, leq t t1 -> leq t t2 -> leq t (meet t1 t2)
}.

Class TopPreLattice(T: Type)(order : T -> T -> Prop) :=
{ topPreLattice_preLattice :> PreLattice T order
; top : T
; top_maximum : forall t, leq t top
}.

Class BottomPreLattice(T: Type)(order : T -> T -> Prop) :=
{ bottomPreLattice_preLattice :> PreLattice T order
; bottom : T
; bottom_minimum : forall t, leq bottom t
}.

Section Lattice_properties.

Context {T order} {L: PreLattice T order}.

Global Instance Lattice_setoid : Setoid T :=
{ equiv := fun x y => leq x y /\ leq y x }.
Proof.
constructor.
intros ?; split; reflexivity.
intros ? ? [? ?]; split; assumption.
intros ? ? ? [? ?] [? ?]; split; etransitivity; eassumption.
Defined.

Global Instance leq_equiv_morphism : Proper (equiv ++> equiv ++> iff) leq.
Proof.
constructor; intros; destruct H; destruct H0.
* transitivity x; trivial. transitivity x0; trivial.
* transitivity y; trivial. transitivity y0; trivial.
Qed.

Global Instance join_leq_morphism : Proper (leq ++> leq ++> leq) join.
Proof.
intros x y H x' y' H'.
apply join_lub.
- transitivity y; trivial. apply join_ub1.
- transitivity y'; trivial. apply join_ub2.
Qed.

Global Instance join_equiv_morphism : Proper (equiv ++> equiv ++> equiv) join.
Proof.
intros x y [H1 H2] x' y' [H1' H2']. split.
- rewrite H1. rewrite H1'. reflexivity.
- rewrite H2. rewrite H2'. reflexivity.
Qed.

Global Instance meet_leq_morphism : Proper (leq ++> leq ++> leq) meet.
Proof.
intros x y H x' y' H'.
apply meet_glb.
- transitivity x; trivial. apply meet_lb1.
- transitivity x'; trivial. apply meet_lb2.
Qed.

Global Instance meet_equiv_morphism : Proper (equiv ++> equiv ++> equiv) meet.
Proof.
intros x y [H1 H2] x' y' [H1' H2']. split.
- rewrite H1. rewrite H1'. reflexivity.
- rewrite H2. rewrite H2'. reflexivity.
Qed.

Lemma join_characterization : forall t1 t2,
  leq t1 t2 <-> equiv (join t1 t2) t2.
Proof.
intros t1 t2. split; intro H.
split.
  apply join_lub. assumption. reflexivity.
  apply join_ub2.
destruct H as [H1 H2]. transitivity (join t1 t2).
  apply join_ub1.
  assumption.
Qed.

Lemma join_comm : forall t1 t2,
  equiv (join t1 t2) (join t2 t1).
Proof.
intros t1 t2; split;
solve [
  apply join_lub;
  [ apply join_ub2 | apply join_ub1 ]
].
Qed.

Lemma join_assoc : forall t1 t2 t3,
  equiv (join t1 (join t2 t3)) (join (join t1 t2) t3).
Proof.
intros t1 t2 t3. split.
* apply join_lub.
  - transitivity (join t1 t2); apply join_ub1.
  - apply join_lub; [ transitivity (join t1 t2) | ];
    auto using join_ub1, join_ub2.
* apply join_lub.
  - apply join_lub; [ | transitivity (join t2 t3)];
    auto using join_ub1, join_ub2.
  - transitivity (join t2 t3); auto using join_ub1, join_ub2.
Qed.

Lemma join_self : forall t,
  equiv (join t t) t.
Proof.
intros t. split.
* apply join_lub; reflexivity.
* apply join_ub1.
Qed.

Lemma meet_characterization : forall t1 t2,
  leq t1 t2 <-> equiv (meet t1 t2) t1.
Proof.
intros t1 t2. split;
 [intros Hleq | intros [Hleq12 Hleq21]].
* split; auto using meet_lb1.
  apply meet_glb. reflexivity. assumption.
* transitivity (meet t1 t2); auto using meet_lb2.
Qed.

Lemma meet_comm : forall t1 t2,
  equiv (meet t1 t2) (meet t2 t1).
Proof.
intros t1 t2.
split; solve [ apply meet_glb; [ apply meet_lb2 | apply meet_lb1 ] ].
Qed.

Lemma meet_assoc : forall t1 t2 t3,
  equiv (meet t1 (meet t2 t3)) (meet (meet t1 t2) t3).
Proof.
intros t1 t2 t3. split.
* apply meet_glb.
  - apply meet_glb.
    apply meet_lb1.
    transitivity (meet t2 t3); auto using meet_lb2, meet_lb1.
  - transitivity (meet t2 t3); auto using meet_lb2.
* apply meet_glb.
  - transitivity (meet t1 t2); auto using meet_lb1.
  - apply meet_glb.
    transitivity (meet t1 t2); auto using meet_lb1, meet_lb2.
    apply meet_lb2.
Qed.

Lemma meet_self : forall t,
  equiv (meet t t) t.
Proof.
intros t. split.
* apply meet_lb1.
* apply meet_glb; reflexivity.
Qed.

End Lattice_properties.

Lemma join_bottom {T order} `{BottomPreLattice T order} : forall t,
  equiv (join t bottom) t.
Proof.
intros t. split.
* apply join_lub. reflexivity. apply bottom_minimum.
* apply join_ub1.
Qed.

Lemma join_top {T order} `{TopPreLattice T order} : forall t,
  equiv (join t top) top.
Proof.
intros t. split.
* apply join_lub. apply top_maximum. reflexivity.
* apply join_ub2.
Qed.

Lemma meet_bottom {T order} `{BottomPreLattice T order} : forall t,
  equiv (meet t bottom) (bottom).
Proof.
intros t. split.
* apply meet_lb2.
* apply meet_glb; [ apply bottom_minimum | reflexivity ].
Qed.

Lemma meet_top {T order} `{TopPreLattice T order} : forall t,
  equiv (meet t top) t.
Proof.
intros t. split.
* apply meet_lb1.
* apply meet_glb; [ reflexivity | apply top_maximum ].
Qed.


Definition monotone {T1 order1 T2 order2}
           `{PreLattice T1 order1} `{PreLattice T2 order2} (f : T1 -> T2) :=
  forall x y, leq x y -> leq (f x) (f y).

Lemma monotone_equiv_compat {T1 order1 T2 order2}
      `{PreLattice T1 order1} `{PreLattice T2 order2} :
  forall (f: T1 -> T2), monotone f ->
  forall x y, equiv x y -> equiv (f x) (f y).
Proof.
intros f Hf x y [Hxy Hyx]. split; auto.
Qed.

Definition upper_bounded {T1 order1 T2 order2}
           `{PreLattice T1 order1} `{PreLattice T2 order2} (f : T1 -> T2) :=
  exists y, forall x, leq (f x) y.

Definition lower_bounded  {T1 order1 T2 order2}
           `{PreLattice T1 order1} `{PreLattice T2 order2} (f : T1 -> T2) :=
  exists y, forall x, leq y (f x).

Definition directed {T order} `{PreLattice T order} (P : T -> Prop) :=
  (exists z, P z) /\
  forall x y, P x -> P y -> exists z, (P z /\ leq x z /\ leq y z).

Lemma monotone_seq_directed {T1 T2} `{L1: PreLattice T1} `{L2: PreLattice T2} :
  forall (x: T1) (f : T1 -> T2),
    monotone f ->
    directed (fun x2 => exists x1, equiv x2 (f x1)).
Proof.
intros x f Hf. split.
- exists (f x). exists x. reflexivity.
- intros x2 y2 [x1 Hx1] [y1 Hy1].
  exists (f (join x1 y1)). split.
  * exists (join x1 y1). reflexivity.
  * split.
    + rewrite Hx1. apply Hf. apply join_ub1.
    + rewrite Hy1. apply Hf. apply join_ub2.
Qed.

Definition is_upper_bound {T order} `{PreLattice T order}
           (P : T -> Prop) (y : T) :=
  forall x, P x -> leq x y.

Lemma is_upper_bound_equiv_compat {T order} `{PreLattice T order}:
  forall (P : T -> Prop) (x y : T),
    is_upper_bound P x -> equiv x y -> is_upper_bound P y.
Proof.
intros P x y Hx Hxy z Hz.
rewrite <- Hxy. auto.
Qed.

Definition is_sup {T order} `{PreLattice T order} (P : T -> Prop) (sup : T) :=
  is_upper_bound P sup /\ (forall x, is_upper_bound P x -> leq sup x).

Lemma is_sup_equiv_compat {T order} `{PreLattice T order}:
  forall (P : T -> Prop) (x y : T),
    is_sup P x -> equiv x y -> is_sup P y.
Proof.
intros P x y [HxUB HxL] Hxy. split.
eauto using is_upper_bound_equiv_compat.
intros z HzUB. rewrite <- Hxy. auto.
Qed.

Lemma is_sup_unique {T order} `{PreLattice T order} :
  forall (P : T -> Prop) sup1 sup2,
    is_sup P sup1 -> is_sup P sup2 ->
    equiv sup1 sup2.
Proof.
intros P sup1 sup2 [H1UB H1L] [H2UB H2L]. split; auto.
Qed.

Definition im {T1 order1 T2 order2}
           `{PreLattice T1 order1} `{PreLattice T2 order2}
           (f : T1 -> T2) (P : T1 -> Prop) :=
  fun x2 => exists x1, P x1 /\ equiv x2 (f x1).

Lemma directed_monotone_im {T1 order1 T2 order2}
      `{PreLattice T1 order1} `{PreLattice T2 order2}
      (f : T1 -> T2) (P : T1 -> Prop) :
  directed P ->
  monotone f ->
  directed (im f P).
Proof.
intros [Hnonempty Hdir] Hf. split.
* destruct Hnonempty as [z Hz].
  exists (f z). exists z. split; auto. reflexivity.
* intros x y [x0 [Hx0 Hx]] [y0 [Hy0 Hy]].
  destruct (Hdir x0 y0 Hx0 Hy0) as [z0 [Hz0 [Hx0z0 Hy0z0]]].
  exists (f z0). splits.
  + exists z0. split; auto. reflexivity.
  + rewrite Hx. apply Hf. trivial.
  + rewrite Hy. apply Hf. trivial.
Qed.

Definition continuous {T1 order1 T2 order2}
           `{PreLattice T1 order1} `{PreLattice T2 order2} (f : T1 -> T2) :=
  forall P sup1, directed P -> is_sup P sup1 ->
  exists sup2, is_sup (im f P) sup2 /\ equiv sup2 (f sup1).

Lemma continuous_monotone {T1 order1 T2 order2}
      `{PreLattice T1 order1} `{PreLattice T2 order2} :
  forall (f : T1 -> T2), continuous f -> monotone f.
Proof.
intros f Hcont x y Hleq.
pose (P := fun z => equiv z x \/ equiv z y).
assert (P x) as Px by (left; reflexivity).
assert (P y) as Py by (right; reflexivity).
assert (directed P) as Hdirected.
{ split.
  * exists x. left. reflexivity.
  * intros x1 x2 Hx1 Hx2. exists y. split.
    right; reflexivity.
    destruct Hx1 as [Hx1 | Hx1]; destruct Hx2 as [Hx2 | Hx2];
    rewrite Hx1; rewrite Hx2;
    split; solve [ assumption || reflexivity ].
}
assert (is_sup P y) as Hsup.
{ split; auto.
  intros z [Hz | Hz]; rewrite Hz; solve [ assumption || reflexivity ].
}
specialize (Hcont P y Hdirected Hsup).
destruct Hcont as [sup2 [Hsup2 Heq]].
rewrite <- Heq.
apply Hsup2.
exists x; split; solve [ assumption || reflexivity ].
Qed.

Class CompletePreLattice(T: Type)(order : T -> T -> Prop) :=
{ completePreLattice_preLattice :> PreLattice T order
; complete_def : forall P: T -> Prop, exists sup, is_sup P sup
}.

Lemma complete_inhabited (T: Type)(order: T -> T -> Prop)
      {C: CompletePreLattice T order} :
  inhabited T.
Proof.
destruct (complete_def (fun _ : T => False)) as [t _].
exact (inhabits t).
Qed.
