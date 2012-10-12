Require Import Lattice.

Require Import Relations.

Definition per A := { R : relation A | PER A R }.

Definition toPER {A} (R: relation A) {E: PER A R} : per A :=
  exist (PER A) R E.

Definition coarser {A} (R1 R2: per A) :=
  forall x y, proj1_sig R2 x y -> proj1_sig R1 x y.

Instance coarser_PreOrder {A} : PreOrder (@coarser A).
Proof.
constructor.
+ intros ? ? ? ?. trivial.
+ intros ? ? ? ? ? ? ? ?. auto.
Qed.

Definition intersection A (R1 R2: per A) : per A.
Proof.
destruct R1 as [R1 [Hsym1 Htrans1]].
destruct R2 as [R2 [Hsym2 Htrans2]].
exists (fun x y => R1 x y /\ R2 x y).
constructor.
* intros ? ? [? ?]. split.
    apply Hsym1. trivial.
    apply Hsym2. trivial.
* intros ? ? ? [? ?] [? ?]. split.
    eapply Htrans1. eassumption. trivial.
    eapply Htrans2. eassumption. trivial.
Defined.

Instance PERJoinPreLattice {A} : JoinPreLattice (per A) coarser :=
{ join := intersection A }.
Proof.
* intros [? [? ?]] [? [? ?]] ? ? [? ?]. trivial.
* intros [? [? ?]] [? [? ?]] ? ? [? ?]. trivial.
* intros [? [? ?]] [? [? ?]] [? [? ?]] ? ? ? ? ?.
    unfold coarser in *. simpl in *. split; auto.
Defined.

Definition union A (R1 R2: per A) : per A.
Proof.
destruct R1 as [R1 [Hsym1 Htrans1]].
destruct R2 as [R2 [Hsym2 Htrans2]].
exists (clos_trans A (union A R1 R2)).
constructor.
* intros x y Hxy. induction Hxy.
  - destruct H.
    + apply t_step. left. apply Hsym1. trivial.
    + apply t_step. right. apply Hsym2. trivial.
  - apply (t_trans A (union A R1 R2) z y x); trivial.
* intros x y z Hxy Hyz. generalize dependent z.
  induction Hxy; intros t Hyt.
  - apply (t_trans A (union A R1 R2) x y t).
    + apply t_step. destruct H; [left|right]; assumption.
    + assumption.
  - apply (t_trans A (union A R1 R2) x z t).
    + apply IHHxy1. assumption.
    + assumption.
Defined.

Instance PERMeetPreLattice {A} : MeetPreLattice (per A) coarser :=
{ meet := union A }.
Proof.
* intros [? [? ?]] [? [? ?]] ? ? ?. apply t_step. left. trivial.
* intros [? [? ?]] [? [? ?]] ? ? ?. apply t_step. right. trivial.
* intros [R1 [Hsym1 Htrans1]]
         [R2 [Hsym2 Htrans2]]
         [R3 [Hsym3 Htrans3]] H12 H23 x y Hplus.
  unfold coarser in *; simpl in *. induction Hplus.
  - destruct H; auto.
  - eauto.
Defined.

Definition per_top A : per A.
Proof.
exists (fun _ _ => False). intuition.
Defined.

Instance PERHasTop {A} : HasTop (per A) coarser :=
{ top := per_top A }.
Proof.
unfold per_top. simpl.
intros ? ? ? ?. simpl in *. tauto.
Defined.

Definition per_bottom A : per A.
Proof.
exists (fun _ _ => True). intuition.
Defined.

Instance PERHasBottom {A} : HasBottom (per A) coarser :=
{ bottom := per_bottom A }.
Proof.
unfold per_bottom.
intros ? ? ? ?. simpl in *. trivial.
Defined.

Module FAMILY.

  Definition big_union {A B} (f: A -> per B) : per B.
  Proof.
  exists (fun x y => forall a, proj1_sig (f a) x y).
  constructor.
  * intros x y H a. specialize (H a).
    destruct (f a) as [R [Hsym Htrans]].
    simpl in *. auto.
  * intros x y z Hxy Hyz a.
    specialize (Hxy a). specialize (Hyz a).
    destruct (f a) as [R [Hsym Htrans]].
    simpl in *. eauto.
  Defined.

  Lemma big_union_upper_bound {A B} :
    forall (f: A -> per B),
    forall a, coarser (f a) (big_union f).
  Proof.
  intros f a x y H. auto.
  Qed.

  Lemma big_union_least {A B} :
    forall (f: A -> per B),
    forall (bound: per B),
      (forall a, coarser (f a) bound) ->
      coarser (big_union f) bound.
  Proof.
  intros f bound Hbound x y H a. specialize (Hbound a x y H). trivial.
  Qed.

End FAMILY.

Module SET.

  Definition big_union {A} (S: per A -> Prop) : per A.
  Proof.
  exists (fun x y => forall R, S R -> proj1_sig R x y).
  constructor.
  * intros x y Hxy R HR. specialize (Hxy R HR).
    destruct R as [R [Hsym Htrans]]. simpl in *. auto.
  * intros x y z Hxy Hyz R HR.
    specialize (Hxy R HR). specialize (Hyz R HR).
    destruct R as [R [Hsym Htrans]]. simpl in *. eauto.
  Defined.

  Lemma big_union_is_sup {A} :
    forall (S: per A -> Prop), is_sup S (big_union S).
  Proof.
  intros S. split.
  * intros R HR x y Runion. apply Runion. trivial.
  * Require Import Classical.
    intros R HR. apply NNPP.
    unfold coarser; simpl. intro H.
    assert (exists x y, proj1_sig R x y /\ exists R, S R /\ ~ proj1_sig R x y)
      as [x [y [Hxy [R' [HR' HR'xy]]]]] by firstorder.
    clear H.
    apply HR'xy. apply HR; trivial.
  Qed.

End SET.

Instance PERJoinCompletePreLattice {A} :
  JoinCompletePreLattice (per A) coarser := { }.
Proof.
intros P.
exists (SET.big_union P). apply SET.big_union_is_sup.
Defined.
