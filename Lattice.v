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

Class JoinPreLattice(T: Type)(leq : T -> T -> Prop) {H: PreOrder leq} :=
{ join : T -> T -> T
; join_ub1 : forall t1 t2, leq t1 (join t1 t2)
; join_ub2 : forall t1 t2, leq t2 (join t1 t2)
; join_lub : forall t t1 t2, leq t1 t -> leq t2 t -> leq (join t1 t2) t
}.

Class MeetPreLattice(T: Type)(leq : T -> T -> Prop) {H: PreOrder leq} :=
{ meet : T -> T -> T
; meet_lb1 : forall t1 t2, leq (meet t1 t2) t1
; meet_lb2 : forall t1 t2, leq (meet t1 t2) t2
; meet_glb : forall t t1 t2, leq t t1 -> leq t t2 -> leq t (meet t1 t2)
}.

Class PreLattice(T: Type)(leq : T -> T -> Prop) {H: PreOrder leq} :=
{ preLattice_JoinPreLattice :> JoinPreLattice T leq
; preLattice_MeetPreLattice :> MeetPreLattice T leq
}.

Class HasTop(T: Type)(leq : T -> T -> Prop) :=
{ top : T
; top_maximum : forall t, leq t top
}.

Class TopJoinPreLattice(T: Type)(leq : T -> T -> Prop) {H: PreOrder leq} :=
{ topPreLattice_preLattice :> JoinPreLattice T leq
; topPreLattice_hasTop :> HasTop T leq
}.

Class HasBottom(T: Type)(order : T -> T -> Prop) :=
{ bottom : T
; bottom_minimum : forall t, order bottom t
}.

Class BottomMeetPreLattice(T: Type)(leq : T -> T -> Prop) {H: PreOrder leq} :=
{ bottomPreLattice_preLattice :> JoinPreLattice T leq
; bottomPreLattice_hasBottom :> HasBottom T leq
}.

(** * Properties of lattices. *)
Section Lattice_properties.

Context {T} {leq: T -> T -> Prop} {P: PreOrder leq}.

Global Instance PreOrder_setoid : Setoid T :=
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

Global Instance join_leq_morphism {L: JoinPreLattice T leq}
: Proper (leq ++> leq ++> leq) join.
Proof.
intros x y H x' y' H'.
apply join_lub.
- transitivity y; trivial. apply join_ub1.
- transitivity y'; trivial. apply join_ub2.
Qed.

Global Instance join_equiv_morphism {L: JoinPreLattice T leq}
: Proper (equiv ++> equiv ++> equiv) join.
Proof.
intros x y [H1 H2] x' y' [H1' H2']. split.
- rewrite H1. rewrite H1'. reflexivity.
- rewrite H2. rewrite H2'. reflexivity.
Qed.

Global Instance meet_leq_morphism {L: MeetPreLattice T leq}
: Proper (leq ++> leq ++> leq) meet.
Proof.
intros x y H x' y' H'.
apply meet_glb.
- transitivity x; trivial. apply meet_lb1.
- transitivity x'; trivial. apply meet_lb2.
Qed.

Global Instance meet_equiv_morphism {L: MeetPreLattice T leq}
: Proper (equiv ++> equiv ++> equiv) meet.
Proof.
intros x y [H1 H2] x' y' [H1' H2']. split.
- rewrite H1. rewrite H1'. reflexivity.
- rewrite H2. rewrite H2'. reflexivity.
Qed.

Lemma join_characterization {L: JoinPreLattice T leq} : forall t1 t2,
  leq t1 t2 <-> leq (join t1 t2) t2.
Proof.
intros t1 t2. split; intro H.
* apply join_lub. assumption. reflexivity.
* transitivity (join t1 t2); auto using join_ub1.
Qed.

Lemma join_comm {L: JoinPreLattice T leq} : forall t1 t2,
  equiv (join t1 t2) (join t2 t1).
Proof.
intros t1 t2; split;
solve [
  apply join_lub;
  [ apply join_ub2 | apply join_ub1 ]
].
Qed.

Lemma join_assoc {L: JoinPreLattice T leq} : forall t1 t2 t3,
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

Lemma join_self {L: JoinPreLattice T leq} : forall t,
  equiv (join t t) t.
Proof.
intros t. split.
* apply join_lub; reflexivity.
* apply join_ub1.
Qed.

Lemma meet_characterization {L: MeetPreLattice T leq}: forall t1 t2,
  leq t1 t2 <-> leq t1 (meet t1 t2).
Proof.
intros t1 t2. split; intro Hleq.
* apply meet_glb. reflexivity. assumption.
* transitivity (meet t1 t2); auto using meet_lb2.
Qed.

Lemma meet_comm {L: MeetPreLattice T leq} : forall t1 t2,
  equiv (meet t1 t2) (meet t2 t1).
Proof.
intros t1 t2.
split; solve [ apply meet_glb; [ apply meet_lb2 | apply meet_lb1 ] ].
Qed.

Lemma meet_assoc {L: MeetPreLattice T leq} : forall t1 t2 t3,
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

Lemma meet_self {L: MeetPreLattice T leq} : forall t,
  equiv (meet t t) t.
Proof.
intros t. split.
* apply meet_lb1.
* apply meet_glb; reflexivity.
Qed.

End Lattice_properties.

Lemma join_bottom {T order} `{JoinPreLattice T order} `{HasBottom T order}:
  forall t, equiv (join t bottom) t.
Proof.
intros t. split.
* apply join_lub. reflexivity. apply bottom_minimum.
* apply join_ub1.
Qed.

Lemma join_top {T order} `{JoinPreLattice T order} `{HasTop T order}:
  forall t, equiv (join t top) top.
Proof.
intros t. split.
* apply join_lub. apply top_maximum. reflexivity.
* apply join_ub2.
Qed.

Lemma meet_bottom {T order} `{MeetPreLattice T order} `{HasBottom T order}:
  forall t, equiv (meet t bottom) (bottom).
Proof.
intros t. split.
* apply meet_lb2.
* apply meet_glb; [ apply bottom_minimum | reflexivity ].
Qed.

Lemma meet_top {T order} `{MeetPreLattice T order} `{HasTop T order}:
  forall t, equiv (meet t top) t.
Proof.
intros t. split.
* apply meet_lb1.
* apply meet_glb; [ reflexivity | apply top_maximum ].
Qed.

(** * More definitions. *)
Definition monotone {T1 order1 T2 order2}
           `{PreOrder _ order1} `{PreOrder _ order2} (f : T1 -> T2) :=
  forall x y, order1 x y -> order2 (f x) (f y).

Lemma monotone_equiv_compat {T1 order1 T2 order2}
      `{PreOrder T1 order1} `{PreOrder T2 order2} :
  forall (f: T1 -> T2), monotone f ->
  forall x y, equiv x y -> equiv (f x) (f y).
Proof.
intros f Hf x y [Hxy Hyx]. split; auto.
Qed.

Definition im {T1 T2 leq} `{PreOrder T2 leq}
           (f : T1 -> T2) (P : T1 -> Prop) :=
  fun x2 => exists x1, P x1 /\ x2 = f x1.

(** * Supremas: least upper bounds. *)
Section sup.

Definition upper_bounded {T1 T2 leq}
           `{PreOrder T2 leq} (f : T1 -> T2) :=
  exists y, forall x, leq (f x) y.

Definition sup_directed {T leq} `{PreOrder T leq} (P : T -> Prop) :=
  (exists z, P z) /\
  forall x y, P x -> P y -> exists z, (P z /\ leq x z /\ leq y z).

Lemma monotone_seq_sup_directed {T1 T2 leq1 leq2}
      `{L1: JoinPreLattice T1 leq1} `{L2: PreOrder T2 leq2} :
  forall (x: T1) (f : T1 -> T2),
    monotone f ->
    sup_directed (fun x2 => exists x1, x2 = f x1).
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

Definition is_upper_bound {T leq} `{PreOrder T leq}
           (P : T -> Prop) (y : T) :=
  forall x, P x -> leq x y.

Lemma is_upper_bound_equiv_compat {T leq} `{PreOrder T leq}:
  forall (P : T -> Prop) (x y : T),
    is_upper_bound P x -> equiv x y -> is_upper_bound P y.
Proof.
intros P x y Hx Hxy z Hz.
rewrite <- Hxy. auto.
Qed.

Definition is_sup {T leq} `{PreOrder T leq} (P : T -> Prop) (sup : T) :=
  is_upper_bound P sup /\ (forall x, is_upper_bound P x -> leq sup x).

Lemma is_sup_equiv_compat {T leq} `{PreOrder T leq}:
  forall (P : T -> Prop) (x y : T),
    is_sup P x -> equiv x y -> is_sup P y.
Proof.
intros P x y [HxUB HxL] Hxy. split.
eauto using is_upper_bound_equiv_compat.
intros z HzUB. rewrite <- Hxy. auto.
Qed.

Lemma is_sup_unique {T leq} `{PreOrder T leq} :
  forall (P : T -> Prop) sup1 sup2,
    is_sup P sup1 -> is_sup P sup2 ->
    equiv sup1 sup2.
Proof.
intros P sup1 sup2 [H1UB H1L] [H2UB H2L]. split; auto.
Qed.

Lemma sup_directed_monotone_im {T1 leq1 T2 leq2}
      `{PreOrder T1 leq1} `{PreOrder T2 leq2}
      (f : T1 -> T2) (P : T1 -> Prop) :
  sup_directed P ->
  monotone f ->
  sup_directed (im f P).
Proof.
intros [Hnonempty Hdir] Hf. split.
* destruct Hnonempty as [z Hz].
  exists (f z). exists z. split; auto.
* intros x y [x0 [Hx0 Hx]] [y0 [Hy0 Hy]].
  destruct (Hdir x0 y0 Hx0 Hy0) as [z0 [Hz0 [Hx0z0 Hy0z0]]].
  exists (f z0). splits.
  + exists z0. split; auto.
  + rewrite Hx. apply Hf. trivial.
  + rewrite Hy. apply Hf. trivial.
Qed.

Definition sup_continuous {T1 leq1 T2 leq2}
           `{PreOrder T1 leq1} `{PreOrder T2 leq2} (f : T1 -> T2) :=
  forall P sup1, sup_directed P -> is_sup P sup1 ->
  { sup2 | is_sup (im f P) sup2 /\ sup2 = f sup1 }.

Lemma sup_continuous_monotone {T1 leq1 T2 leq2}
      `{PreOrder T1 leq1} `{PreOrder T2 leq2} :
  forall (f : T1 -> T2), sup_continuous f -> monotone f.
Proof.
intros f Hcont x y Hleq.
pose (P := fun z => equiv z x \/ equiv z y).
assert (P x) as Px by (left; reflexivity).
assert (P y) as Py by (right; reflexivity).
assert (sup_directed P) as Hdirected.
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

End sup.

(** * Infemas: greatest lower bounds. *)
Section inf.

Definition lower_bounded  {T1 T2 leq}
           `{PreLattice T2 leq} (f : T1 -> T2) :=
  exists y, forall x, leq y (f x).

Definition is_lower_bound {T leq} `{PreOrder T leq}
           (P : T -> Prop) (y : T) :=
  forall x, P x -> leq y x.

Lemma is_lower_bound_equiv_compat {T leq} `{PreOrder T leq}:
  forall (P : T -> Prop) (x y : T),
    is_lower_bound P x -> equiv x y -> is_lower_bound P y.
Proof.
intros P x y Hx Hxy z Hz.
rewrite <- Hxy. auto.
Qed.

Definition is_inf {T leq} `{PreOrder T leq} (P : T -> Prop) (inf : T) :=
  is_lower_bound P inf /\ (forall x, is_lower_bound P x -> leq x inf).

Lemma is_inf_equiv_compat {T leq} `{PreOrder T leq}:
  forall (P : T -> Prop) (x y : T),
    is_inf P x -> equiv x y -> is_inf P y.
Proof.
intros P x y [HxLB HxL] Hxy. split.
eauto using is_lower_bound_equiv_compat.
intros z HzLB. rewrite <- Hxy. auto.
Qed.

Lemma is_inf_unique {T leq} `{PreOrder T leq} :
  forall (P : T -> Prop) inf1 inf2,
    is_inf P inf1 -> is_inf P inf2 ->
    equiv inf1 inf2.
Proof.
intros P inf1 inf2 [H1LB H1L] [H2LB H2L]. split; auto.
Qed.

Definition inf_directed {T leq} `{PreOrder T leq} (P : T -> Prop) :=
  (exists z, P z) /\
  forall x y, P x -> P y -> exists z, (P z /\ leq z x /\ leq z y).

Lemma monotone_seq_inf_directed {T1 T2 leq1 leq2}
      `{L1: MeetPreLattice T1 leq1} `{L2: PreOrder T2 leq2} :
  forall (x: T1) (f : T1 -> T2),
    monotone f ->
    inf_directed (fun x2 => exists x1, x2 = f x1).
Proof.
intros x f Hf. split.
- exists (f x). exists x. reflexivity.
- intros x2 y2 [x1 Hx1] [y1 Hy1].
  exists (f (meet x1 y1)). split.
  * exists (meet x1 y1). reflexivity.
  * split.
    + rewrite Hx1. apply Hf. apply meet_lb1.
    + rewrite Hy1. apply Hf. apply meet_lb2.
Qed.

Lemma inf_directed_monotone_im {T1 leq1 T2 leq2}
      `{PreOrder T1 leq1} `{PreOrder T2 leq2}
      (f : T1 -> T2) (P : T1 -> Prop) :
  inf_directed P ->
  monotone f ->
  inf_directed (im f P).
Proof.
intros [Hnonempty Hdir] Hf. split.
* destruct Hnonempty as [z Hz].
  exists (f z). exists z. split; auto.
* intros x y [x0 [Hx0 Hx]] [y0 [Hy0 Hy]].
  destruct (Hdir x0 y0 Hx0 Hy0) as [z0 [Hz0 [Hx0z0 Hy0z0]]].
  exists (f z0). splits.
  + exists z0. split; auto.
  + rewrite Hx. apply Hf. trivial.
  + rewrite Hy. apply Hf. trivial.
Qed.

Definition inf_continuous {T1 leq1 T2 leq2}
           `{PreOrder T1 leq1} `{PreOrder T2 leq2} (f : T1 -> T2) :=
  forall P inf1, inf_directed P -> is_inf P inf1 ->
  { inf2 | is_inf (im f P) inf2 /\ equiv inf2 (f inf1) }.

Lemma inf_continuous_monotone {T1 leq1 T2 leq2}
      `{PreOrder T1 leq1} `{PreOrder T2 leq2} :
  forall (f : T1 -> T2), inf_continuous f -> monotone f.
Proof.
intros f Hcont x y Hleq.
pose (P := fun z => equiv x z \/ equiv y z).
assert (P x) as Px by (left; reflexivity).
assert (P y) as Py by (right; reflexivity).
assert (inf_directed P) as Hdirected.
{ split.
  * exists x. left. reflexivity.
  * intros x1 x2 Hx1 Hx2. exists x. split.
    left; reflexivity.
    destruct Hx1 as [Hx1 | Hx1]; destruct Hx2 as [Hx2 | Hx2];
    rewrite <- Hx1; rewrite <- Hx2;
    split; solve [ assumption || reflexivity ].
}
assert (is_inf P x) as Hinf.
{ split; auto.
  intros z [Hz | Hz]; rewrite <- Hz; solve [ assumption || reflexivity ].
}
specialize (Hcont P x Hdirected Hinf).
destruct Hcont as [inf2 [Hinf2 Heq]].
rewrite <- Heq.
apply Hinf2.
exists y; split; solve [ assumption || reflexivity ].
Qed.

End inf.

(** * About and [anti_monotone]. *)
Section Flip.

Definition flip {A B} (f: A -> A -> B) x y := f y x.

Lemma flip_PreOrder {A} {leq: A -> A -> Prop} :
  PreOrder leq -> PreOrder (flip leq).
Proof.
intro H. constructor.
* intro x. unfold flip. reflexivity.
* intros x y z Hxy Hyz. unfold flip in *. transitivity y; trivial.
Qed.

Lemma equiv_flip_iff {A} {leqA: A -> A -> Prop} (PA: PreOrder leqA) :
  forall x y,
    @equiv _ (@PreOrder_setoid _ _ PA) x y
    <-> @equiv _ (@PreOrder_setoid _ _ (flip_PreOrder PA)) x y.
Proof.
intros x y; split; intros [Hxy Hyx]; split; assumption.
Qed.

Definition anti_monotone {A B leqA leqB} `{PreOrder A leqA} `{PreOrder B leqB}
           (f: A -> B) :=
  forall x y, flip leqA x y -> leqB (f x) (f y).

Lemma monotone_flip_iff {A B} {leqA: A -> A -> Prop} {leqB: B -> B -> Prop}
      (PA: PreOrder leqA) (PB: PreOrder leqB) (f: A -> B):
  @monotone _ _ _ _ PA PB f <->
  @anti_monotone _ _ _ _ (flip_PreOrder PA) PB f.
Proof.
split; intros Hf x y Hxy; apply Hf; assumption.
Qed.

Lemma anti_monotone_flip_iff {A B} {leqA: A -> A -> Prop} {leqB: B -> B -> Prop}
      (PA: PreOrder leqA) (PB: PreOrder leqB) (f: A -> B):
  @anti_monotone _ _ _ _ PA PB f <->
  @monotone _ _ _ _ (flip_PreOrder PA) PB f.
Proof.
split; intros Hf x y Hxy; apply Hf; assumption.
Qed.

Lemma sup_directed_flip_iff {A} {leq: A -> A -> Prop} (PA: PreOrder leq):
  forall P: A -> Prop,
    @sup_directed _ _ PA P <-> @inf_directed _ _ (flip_PreOrder PA) P.
Proof.
intro P; split; intros [Hinhabited HP]; split; trivial.
Qed.

Lemma inf_directed_flip_iff {A} {leq: A -> A -> Prop} (PA: PreOrder leq):
  forall P: A -> Prop,
    @inf_directed _ _ PA P <-> @sup_directed _ _ (flip_PreOrder PA) P.
Proof.
intro P; split; intros [Hinhabited HP]; split; trivial.
Qed.

Lemma is_upper_bound_flip_iff {A} {leq: A -> A -> Prop} (PA: PreOrder leq):
  forall (P: A -> Prop) x,
    @is_upper_bound _ _ PA P x <-> @is_lower_bound _ _ (flip_PreOrder PA) P x.
Proof.
intros P x; split; intros H y Hy; apply H; trivial.
Qed.

Lemma is_lower_bound_flip_iff {A} {leq: A -> A -> Prop} (PA: PreOrder leq):
  forall (P: A -> Prop) x,
    @is_lower_bound _ _ PA P x <-> @is_upper_bound _ _ (flip_PreOrder PA) P x.
Proof.
intros P x; split; intros H y Hy; apply H; trivial.
Qed.

Lemma is_sup_flip_iff {A} {leq: A -> A -> Prop} (PA: PreOrder leq):
  forall (P: A -> Prop) x,
    @is_sup _ _ PA P x <-> @is_inf _ _ (flip_PreOrder PA) P x.
Proof.
intros P x; split; intros [HUB HLUB]; split.
* rewrite <- is_upper_bound_flip_iff. assumption.
* intros z Hz. apply HLUB. rewrite is_upper_bound_flip_iff. assumption.
* rewrite is_upper_bound_flip_iff. assumption.
* intros z Hz. apply HLUB. rewrite <- is_upper_bound_flip_iff. assumption.
Qed.

Lemma is_inf_flip_iff {A} {leq: A -> A -> Prop} (PA: PreOrder leq):
  forall (P: A -> Prop) x,
    @is_inf _ _ PA P x <-> @is_sup _ _ (flip_PreOrder PA) P x.
Proof.
intros P x; split; intros [HUB HLUB]; split.
* rewrite <- is_lower_bound_flip_iff. assumption.
* intros z Hz. apply HLUB. rewrite is_lower_bound_flip_iff. assumption.
* rewrite is_lower_bound_flip_iff. assumption.
* intros z Hz. apply HLUB. rewrite <- is_lower_bound_flip_iff. assumption.
Qed.

Lemma sup_continuous_flip {T1 T2}
      {leq1: T1 -> T1 -> Prop} {leq2: T2 -> T2 -> Prop}
      (P1: PreOrder leq1) (P2: PreOrder leq2) (f : T1 -> T2) :
  @sup_continuous _ _ _ _ P1 P2 f ->
  @inf_continuous _ _ _ _ (flip_PreOrder P1) (flip_PreOrder P2) f.
Proof.
intros H P inf Hdir Hinf.
rewrite <- sup_directed_flip_iff in Hdir.
rewrite <- is_sup_flip_iff in Hinf.
specialize (H P inf Hdir Hinf).
destruct H as [sup2 [Hsup2 Heq]].
exists sup2. split.
rewrite <- is_sup_flip_iff. assumption.
subst. reflexivity.
Qed.

Lemma sup_continuous_flip_inv {T1 T2}
      {leq1: T1 -> T1 -> Prop} {leq2: T2 -> T2 -> Prop}
      (P1: PreOrder leq1) (P2: PreOrder leq2) (f : T1 -> T2) :
  @inf_continuous _ _ _ _ (flip_PreOrder P1) (flip_PreOrder P2) f ->
  @sup_continuous _ _ _ _ P1 P2 f.
Proof.
intros H P inf Hdir Hinf.
rewrite sup_directed_flip_iff in Hdir.
rewrite is_sup_flip_iff in Hinf.
specialize (H P inf Hdir Hinf).
destruct H as [sup2 [Hsup2 Heq]].
exists (f inf). split; trivial.
rewrite is_sup_flip_iff.
apply (is_inf_equiv_compat _ sup2 (f inf)); trivial.
Qed.

Lemma inf_continuous_flip {T1 T2}
      {leq1: T1 -> T1 -> Prop} {leq2: T2 -> T2 -> Prop}
      (P1: PreOrder leq1) (P2: PreOrder leq2) (f : T1 -> T2) :
  @inf_continuous _ _ _ _ P1 P2 f ->
  @sup_continuous _ _ _ _ (flip_PreOrder P1) (flip_PreOrder P2) f.
Proof.
intros H P inf Hdir Hinf.
rewrite <- inf_directed_flip_iff in Hdir.
rewrite <- is_inf_flip_iff in Hinf.
specialize (H P inf Hdir Hinf).
destruct H as [sup2 [Hsup2 Heq]].
exists (f inf). split; trivial.
rewrite <- is_inf_flip_iff.
apply (is_inf_equiv_compat _ sup2 (f inf)); trivial.
Qed.

Lemma inf_continuous_flip_inv {T1 T2}
      {leq1: T1 -> T1 -> Prop} {leq2: T2 -> T2 -> Prop}
      (P1: PreOrder leq1) (P2: PreOrder leq2) (f : T1 -> T2) :
  @sup_continuous _ _ _ _ (flip_PreOrder P1) (flip_PreOrder P2) f ->
  @inf_continuous _ _ _ _ P1 P2 f.
Proof.
intros H P inf Hdir Hinf.
rewrite inf_directed_flip_iff in Hdir.
rewrite is_inf_flip_iff in Hinf.
specialize (H P inf Hdir Hinf).
destruct H as [sup2 [Hsup2 Heq]].
exists sup2. split.
rewrite is_inf_flip_iff. assumption.
subst. reflexivity.
Qed.

End Flip.

Class JoinCompletePreLattice(T: Type)(leq : T -> T -> Prop) `{PreOrder T leq} :=
{ join_complete : forall P: T -> Prop, { sup: T | is_sup P sup }
}.

Lemma join_complete_inhabited (T: Type)(order: T -> T -> Prop)
      `{PreOrder T order} `{JoinCompletePreLattice T order} :
  inhabited T.
Proof.
destruct (join_complete (fun _ : T => False)) as [t _].
exact (inhabits t).
Qed.

Class MeetCompletePreLattice(T: Type)(leq : T -> T -> Prop) `{PreOrder T leq} :=
{ meet_complete : forall P: T -> Prop, { inf: T | is_inf P inf }
}.

Lemma meet_complete_inhabited (T: Type)(order: T -> T -> Prop)
      `{PreOrder T order} `{MeetCompletePreLattice T order} :
  inhabited T.
Proof.
destruct (meet_complete (fun _ : T => False)) as [t _].
exact (inhabits t).
Qed.

Class CompletePreLattice(T: Type)(leq : T -> T -> Prop) `{PreOrder T leq} :=
{ complete_join :> JoinCompletePreLattice T leq
; complete_meet :> MeetCompletePreLattice T leq
}.

Definition is_fixed_point {T} `{L : Setoid T} (f : T -> T) (x : T) :=
  equiv (f x) x.
