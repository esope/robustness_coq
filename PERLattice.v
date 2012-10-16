Require Import Relations.
Require Import PreLattice.
Require Import Chains.

Definition per A := { R : relation A | PER R }.

Definition toPER {A} (R: relation A) {E: PER R} : per A :=
  exist PER R E.

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

  Lemma big_union_monotone_zero {A} (zero: per A) (f: per A -> per A):
    monotone f ->
    monotone (fun zero => FAMILY.big_union (fun n => n_iter f n zero)).
  Proof.
    intros Hf R1 R2 HR x y Hxy n.
    unfold FAMILY.big_union in Hxy. simpl in Hxy.
    apply (n_iter_monotone_zero f Hf n R1 R2 HR x y).
    auto.
  Qed.

  Definition big_intersection {A B} (f: A -> per B) : per B.
  Proof.
  exists (clos_trans _ (fun x y => exists a, proj1_sig (f a) x y)).
  constructor.
  * intros x y H. induction H.
    + apply t_step. destruct H as [a H].
      exists a.
      destruct (f a) as [R [HRefl Hsym]].
      simpl in *. auto.
    + apply (t_trans _ _ z y x); auto.
  * intros x y z Hxy Hyz. apply (t_trans _ _ x y z); auto.
  Defined.

  Lemma big_intersection_lower_bound {A B} :
    forall (f: A -> per B),
    forall a, coarser (big_intersection f) (f a).
  Proof.
  intros f a x y H. apply t_step. eauto.
  Qed.

  Lemma big_intersection_greatest {A B} :
    forall (f: A -> per B),
    forall (bound: per B),
      (forall a, coarser bound (f a)) ->
      coarser bound (big_intersection f).
  Proof.
  intros f bound Hbound x y H.
  simpl in H. induction H.
  * destruct H as [a H]. apply (Hbound a _ _ H).
  * destruct bound as [bound [Hrefl Hsym]]. simpl in *. eauto.
  Qed.

  Lemma big_intersection_monotone_zero {A} (zero: per A) (f: per A -> per A):
    monotone f ->
    monotone (fun zero => FAMILY.big_intersection (fun n => n_iter f n zero)).
  Proof.
    intros Hf R1 R2 HR x y Hxy.
    unfold FAMILY.big_intersection in *. simpl in *.
    induction Hxy.
    * apply t_step. destruct H as [n H]. exists n.
      apply (n_iter_monotone_zero f Hf n R1 R2 HR x y). trivial.
    * apply (t_trans _ _ x y z); auto.
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

  Definition big_intersection {A} (S: per A -> Prop) : per A.
  Proof.
  exists (clos_trans _ (fun x y => exists R, S R /\ proj1_sig R x y)).
  constructor.
  * intros x y Hxy. induction Hxy.
    + apply t_step. destruct H as [R [HSR HRxy]].
      exists R. split; trivial.
      destruct R as [R [Hrefl Hsym]]. simpl in *. auto.
    + apply (t_trans _ _ z y x); auto.
  * intros x y z Hxy Hyz. apply (t_trans _ _ x y z); auto.
  Defined.

  Lemma big_intersection_is_inf {A} :
    forall (S: per A -> Prop), is_inf S (big_intersection S).
  Proof.
  intros S. split.
  * intros R HR x y Runion. apply t_step. eauto.
  * intros R HR x y Hxy. unfold big_intersection in Hxy. simpl in Hxy.
    induction Hxy.
    + destruct H as [R' [HSR' HR'xy]].
      apply (HR R' HSR' _ _ HR'xy).
    + destruct R as [R [Hrefl Hsym]]. simpl in *. eauto.
  Qed.

End SET.

Instance PERJoinCompletePreLattice {A} :
  JoinCompletePreLattice (per A) coarser := { }.
Proof.
intros P.
exists (SET.big_union P). apply SET.big_union_is_sup.
Defined.

Instance ERMeetCompletePreLattice {A} :
  MeetCompletePreLattice (per A) coarser := { }.
Proof.
intros P.
exists (SET.big_intersection P). apply SET.big_intersection_is_inf.
Defined.
