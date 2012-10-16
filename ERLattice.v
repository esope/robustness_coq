Require Import Relations.
Require Export Lattice.
Require Import Kleene.

Definition er A := { R : relation A | Equivalence R }.

Definition toER {A} (R: relation A) {E: Equivalence R} : er A :=
  exist Equivalence R E.

Definition coarser {A} (R1 R2: er A) :=
  forall x y, proj1_sig R2 x y -> proj1_sig R1 x y.

Instance coarser_PreOrder {A} : PreOrder (@coarser A).
Proof.
constructor.
+ intros ? ? ? ?. trivial.
+ intros ? ? ? ? ? ? ? ?. auto.
Qed.

Definition intersection A (R1 R2: er A) : er A.
Proof.
destruct R1 as [R1 [Hrefl1 Hsym1 Htrans1]].
destruct R2 as [R2 [Hrefl2 Hsym2 Htrans2]].
exists (fun x y => R1 x y /\ R2 x y).
constructor.
* intros R. split; trivial.
* intros ? ? [? ?]. split.
    apply Hsym1. trivial.
    apply Hsym2. trivial.
* intros ? ? ? [? ?] [? ?]. split.
    eapply Htrans1. eassumption. trivial.
    eapply Htrans2. eassumption. trivial.
Defined.

Definition union A (R1 R2: er A) : er A.
Proof.
destruct R1 as [R1 [HRefl1 Hsym1 Htrans1]].
destruct R2 as [R2 [HRefl2 Hsym2 Htrans2]].
exists (clos_trans A (union A R1 R2)).
constructor.
* intros x. apply t_step. left. trivial.
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

Instance ERJoinPreLattice {A} : JoinPreLattice (er A) coarser :=
{ join := intersection A }.
Proof.
* intros [? [? ? ?]] [? [? ? ?]] ? ? [? ?]. trivial.
* intros [? [? ? ?]] [? [? ? ?]] ? ? [? ?]. trivial.
* intros [? [? ? ?]] [? [? ? ?]] [? [? ? ?]] ? ? ? ? ?.
    unfold coarser in *. simpl in *. split; auto.
Defined.

Instance ERMeetPreLattice {A} : MeetPreLattice (er A) coarser :=
{ meet := union A }.
Proof.
* intros [? [? ? ?]] [? [? ? ?]] ? ? ?. apply t_step. left. trivial.
* intros [? [? ? ?]] [? [? ? ?]] ? ? ?. apply t_step. right. trivial.
* intros [R1 [Hrefl1 Hsym1 Htrans1]]
         [R2 [Hrefl2 Hsym2 Htrans2]]
         [R3 [Hrefl3 Hsym3 Htrans3]] H12 H23 x y Hplus.
  unfold coarser in *; simpl in *. induction Hplus.
  - destruct H; auto.
  - eauto.
Defined.

Definition er_top_rel A : relation A := eq.

Definition er_top A : er A.
Proof.
exists (er_top_rel A). intuition.
Defined.

Instance ERHasTop {A} : HasTop (er A) coarser :=
{ top := er_top A }.
Proof.
unfold er_top.
intros [R E] x y H. simpl in *. rewrite H. reflexivity.
Defined.

Definition er_bottom_rel A : relation A := fun _ _ => True.

Instance er_bottom_rel_Equivalence A : Equivalence (er_bottom_rel A).
Proof.
intuition.
Qed.

Hint Resolve er_bottom_rel_Equivalence.

Definition er_bottom A : er A.
Proof.
exists (er_bottom_rel A). auto.
Defined.

Instance ERHasBottom {A} : HasBottom (er A) coarser :=
{ bottom := er_bottom A }.
Proof.
unfold er_bottom.
intros ? ? ? ?. simpl in *. compute. trivial.
Defined.

Module FAMILY.

  Definition big_union {A B} (f: A -> er B) : er B.
  Proof.
  exists (fun x y => forall a, proj1_sig (f a) x y).
  constructor.
  * intros x a. destruct (f a) as [R [Hrefl Hsym Htrans]].
    simpl. trivial.
  * intros x y H a. specialize (H a).
    destruct (f a) as [R [Hrefl Hsym Htrans]].
    simpl in *. auto.
  * intros x y z Hxy Hyz a.
    specialize (Hxy a). specialize (Hyz a).
    destruct (f a) as [R [HRefl Hsym Htrans]].
    simpl in *. eauto.
  Defined.

  Lemma big_union_upper_bound {A B} :
    forall (f: A -> er B),
    forall a, coarser (f a) (big_union f).
  Proof.
  intros f a x y H. auto.
  Qed.

  Lemma big_union_least {A B} :
    forall (f: A -> er B),
    forall (bound: er B),
      (forall a, coarser (f a) bound) ->
      coarser (big_union f) bound.
  Proof.
  intros f bound Hbound x y H a. specialize (Hbound a x y H). trivial.
  Qed.

  Lemma big_union_monotone_zero {A} (zero: er A) (f: er A -> er A):
    monotone f ->
    monotone (fun zero => FAMILY.big_union (fun n => n_iter f n zero)).
  Proof.
    intros Hf R1 R2 HR x y Hxy n.
    unfold FAMILY.big_union in Hxy. simpl in Hxy.
    apply (n_iter_monotone_zero f Hf n R1 R2 HR x y).
    auto.
  Qed.

  Definition big_intersection {A B} (f: A -> er B) : er B.
  Proof.
  exists (clos_refl_trans _ (fun x y => exists a, proj1_sig (f a) x y)).
  constructor.
  * intro x. apply rt_refl.
  * intros x y H. induction H.
    + apply rt_step. destruct H as [a H].
      exists a.
      destruct (f a) as [R [HRefl Hsym Htrans]].
      simpl in *. auto.
    + apply rt_refl.
    + apply (rt_trans _ _ z y x); auto.
  * intros x y z Hxy Hyz. apply (rt_trans _ _ x y z); auto.
  Defined.

  Lemma big_intersection_lower_bound {A B} :
    forall (f: A -> er B),
    forall a, coarser (big_intersection f) (f a).
  Proof.
  intros f a x y H. apply rt_step. eauto.
  Qed.

  Lemma big_intersection_greatest {A B} :
    forall (f: A -> er B),
    forall (bound: er B),
      (forall a, coarser bound (f a)) ->
      coarser bound (big_intersection f).
  Proof.
  intros f bound Hbound x y H.
  simpl in H. induction H.
  * destruct H as [a H]. apply (Hbound a _ _ H).
  * destruct bound as [bound [Hrefl Hsym Htrans]]. simpl. auto.
  * destruct bound as [bound [Hrefl Hsym Htrans]]. simpl in *. eauto.
  Qed.

  Lemma big_intersection_monotone_zero {A} (zero: er A) (f: er A -> er A):
    monotone f ->
    monotone (fun zero => FAMILY.big_intersection (fun n => n_iter f n zero)).
  Proof.
    intros Hf R1 R2 HR x y Hxy.
    unfold FAMILY.big_intersection in *. simpl in *.
    induction Hxy.
    * apply rt_step. destruct H as [n H]. exists n.
      apply (n_iter_monotone_zero f Hf n R1 R2 HR x y). trivial.
    * apply rt_refl.
    * apply (rt_trans _ _ x y z); auto.
  Qed.

End FAMILY.

Module SET.

  Definition big_union {A} (S: er A -> Prop) : er A.
  Proof.
  exists (fun x y => forall R, S R -> proj1_sig R x y).
  constructor.
  * intros x R HR. destruct R as [R [Hrefl Hsym Htrans]].
    simpl. trivial.
  * intros x y Hxy R HR. specialize (Hxy R HR).
    destruct R as [R [Hrefl Hsym Htrans]]. simpl in *. auto.
  * intros x y z Hxy Hyz R HR.
    specialize (Hxy R HR). specialize (Hyz R HR).
    destruct R as [R [Hrefl Hsym Htrans]]. simpl in *. eauto.
  Defined.

  Lemma big_union_is_sup {A} :
    forall (S: er A -> Prop), is_sup S (big_union S).
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

  Definition big_intersection {A} (S: er A -> Prop) : er A.
  Proof.
  exists (clos_refl_trans _ (fun x y => exists R, S R /\ proj1_sig R x y)).
  constructor.
  * intros x. apply rt_refl.
  * intros x y Hxy. induction Hxy.
    + apply rt_step. destruct H as [R [HSR HRxy]].
      exists R. split; trivial.
      destruct R as [R [Hrefl Hsym Htrans]]. simpl in *. auto.
    + apply rt_refl.
    + apply (rt_trans _ _ z y x); auto.
  * intros x y z Hxy Hyz. apply (rt_trans _ _ x y z); auto.
  Defined.

  Lemma big_intersection_is_inf {A} :
    forall (S: er A -> Prop), is_inf S (big_intersection S).
  Proof.
  intros S. split.
  * intros R HR x y Runion. apply rt_step. eauto.
  * intros R HR x y Hxy. unfold big_intersection in Hxy. simpl in Hxy.
    induction Hxy.
    + destruct H as [R' [HSR' HR'xy]].
      apply (HR R' HSR' _ _ HR'xy).
    + destruct R as [R [Hrefl Hsym Htrans]]. simpl. auto.
    + destruct R as [R [Hrefl Hsym Htrans]]. simpl in *. eauto.
  Qed.

End SET.

Instance ERJoinCompletePreLattice {A} :
  JoinCompletePreLattice (er A) coarser := { }.
Proof.
intros P.
exists (SET.big_union P). apply SET.big_union_is_sup.
Defined.

Instance ERMeetCompletePreLattice {A} :
  MeetCompletePreLattice (er A) coarser := { }.
Proof.
intros P.
exists (SET.big_intersection P). apply SET.big_intersection_is_inf.
Defined.
