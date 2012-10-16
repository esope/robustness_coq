Require Import PreLattice.
Require Import Relations.

Definition coarser {A} (R1 R2: relation A) :=
  forall x y, R2 x y -> R1 x y.

Instance coarser_PreOrder {A} : PreOrder (@coarser A).
Proof.
constructor.
+ intros ? ? ? ?. trivial.
+ intros ? ? ? ? ? ? ? ?. auto.
Qed.

Definition intersection A (R1 R2: relation A) : relation A :=
  fun x y => R1 x y /\ R2 x y.

Instance RelJoinPreLattice {A} : JoinPreLattice (relation A) coarser :=
{ join := intersection A }.
Proof.
* intros ? ? ? ? [? ?]. trivial.
* intros ? ? ? ? [? ?]. trivial.
* intros ? ? ? ? ? ? ? ?. split; auto.
Defined.

Instance RelMeetPreLattice {A} : MeetPreLattice (relation A) coarser :=
{ meet := union A }.
Proof.
* intros ? ? ? ? ?. left. trivial.
* intros ? ? ? ? ?. right. trivial.
* intros ? ? ? ? ? ? ? [? | ?]; auto.
Defined.

Instance RelHasTop {A} : HasTop (relation A) coarser :=
{ top := fun _ _ => False }.
Proof.
intros ? ? ? ?. tauto.
Defined.

Instance RelHasBottom {A} : HasBottom (relation A) coarser :=
{ bottom := fun _ _ => True }.
Proof.
intros ? ? ? ?. trivial.
Defined.

Module FAMILY.

  Definition big_union {A B} (f: A -> relation B) : relation B :=
    fun x y => forall a, f a x y.

  Lemma big_union_upper_bound {A B} :
    forall (f: A -> relation B),
    forall a, coarser (f a) (big_union f).
  Proof.
  intros f a x y H. auto.
  Qed.

  Lemma big_union_least {A B} :
    forall (f: A -> relation B),
    forall (bound: relation B),
      (forall a, coarser (f a) bound) ->
      coarser (big_union f) bound.
  Proof.
  intros f bound Hbound x y H a. specialize (Hbound a x y H). trivial.
  Qed.

End FAMILY.

Module SET.

  Definition big_union {A} (S: relation A -> Prop) : relation A :=
    fun x y => forall R, S R -> R x y.

  Lemma big_union_is_sup {A} :
    forall (S: relation A -> Prop), is_sup S (big_union S).
  Proof.
  intros S. split.
  * intros R HR x y Runion. apply Runion. trivial.
  * Require Import Classical.
    intros R HR. apply NNPP.
    unfold coarser; simpl. intro H.
    assert (exists x y, R x y /\ ~big_union S x y)
      as [x [y [Hxy HS]]] by firstorder.
    clear H.
    apply HS. intros R' HR'. apply HR; trivial.
  Qed.

End SET.

Instance RelJoinCompletePreLattice {A} :
  JoinCompletePreLattice (relation A) coarser := { }.
Proof.
intros P.
exists (SET.big_union P). apply SET.big_union_is_sup.
Defined.
