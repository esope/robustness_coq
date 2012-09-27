Require Export Lattice.

Require Import Relations.

Definition er A := { R : relation A | Equivalence R }.

Definition toER {A} (R: relation A) {E: Equivalence R} : er A :=
  exist Equivalence R E.

Definition er_coarser {A} (R1 R2: er A) :=
  forall x y, proj1_sig R2 x y -> proj1_sig R1 x y.

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

Instance RelPreLattice {A} : PreLattice (er A) er_coarser :=
{ join := intersection A
; meet := union A
}.
Proof.
* constructor.
  + intros ? ? ? ?. trivial.
  + intros ? ? ? ? ? ? ? ?. auto.
* intros [? [? ? ?]] [? [? ? ?]] ? ? [? ?]. trivial.
* intros [? [? ? ?]] [? [? ? ?]] ? ? [? ?]. trivial.
* intros [? [? ? ?]] [? [? ? ?]] [? [? ? ?]] ? ? ? ? ?.
    unfold er_coarser in *. simpl in *. split; auto.
* intros [? [? ? ?]] [? [? ? ?]] ? ? ?. apply t_step. left. trivial.
* intros [? [? ? ?]] [? [? ? ?]] ? ? ?. apply t_step. right. trivial.
* intros [R1 [Hrefl1 Hsym1 Htrans1]]
         [R2 [Hrefl2 Hsym2 Htrans2]]
         [R3 [Hrefl3 Hsym3 Htrans3]] H12 H23 x y Hplus.
  unfold er_coarser in *; simpl in *. induction Hplus.
  - destruct H; auto.
  - eauto.
Defined.

Definition er_top_rel A : relation A := eq.

Definition er_top A : er A.
Proof.
exists (er_top_rel A). intuition.
Defined.

Instance RelTopPreLattice {A} : TopPreLattice (er A) er_coarser :=
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

Instance RelBottomPreLattice {A} : BottomPreLattice (er A) er_coarser :=
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

  Lemma big_union_uper_bound {A B} :
    forall (f: A -> er B),
    forall a, leq (f a) (big_union f).
  Proof.
  intros f a x y H. auto.
  Qed.

  Lemma big_union_least {A B} :
    forall (f: A -> er B),
    forall (bound: er B),
      (forall a, leq (f a) bound) ->
      leq (big_union f) bound.
  Proof.
  intros f bound Hbound x y H a. specialize (Hbound a x y H). trivial.
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
    unfold leq; unfold er_coarser; simpl. intro H.
    assert (exists x y, proj1_sig R x y /\ exists R, S R /\ ~ proj1_sig R x y)
      as [x [y [Hxy [R' [HR' HR'xy]]]]] by firstorder.
    clear H.
    apply HR'xy. apply HR; trivial.
  Qed.

End SET.

Instance RelCompletePreLattice {A} :
  CompletePreLattice (er A) er_coarser := { }.
Proof.
intros P HP.
exists (SET.big_union P). apply SET.big_union_is_sup.
Defined.
