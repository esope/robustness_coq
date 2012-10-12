Require Import Lattice.

Require Import Ensembles.
Require Import Constructive_sets.

Instance SetIncluded_PreOrder {A} : PreOrder (Included A).
Proof with auto with sets.
* constructor...
Qed.


Instance SetJoinPreLattice {A} : JoinPreLattice (Ensemble A) (Included A) :=
{ join := Union A }.
Proof with auto with sets.
* idtac...
* idtac...
* intros S S1 S2 H1 H2 x Hx. inversion Hx; subst; auto.
Defined.

Instance SetMeetPreLattice {A} : MeetPreLattice (Ensemble A) (Included A) :=
{ meet := Intersection A }.
Proof with auto with sets.
* intros S1 S2 x Hx. inversion Hx; subst; auto.
* intros S1 S2 x Hx. inversion Hx; subst; auto.
* idtac...
Defined.

Instance SetHasTop {A} : HasTop (Ensemble A) (Included A) :=
{ top := Full_set A }.
Proof.
intros S x Hx. constructor.
Defined.

Instance SetHasBottom {A} : HasBottom (Ensemble A) (Included A) :=
{ bottom := Empty_set A }.
Proof.
intros. auto with sets.
Defined.

Module FAMILY.

  Definition big_union {A B} (f: A -> Ensemble B) : Ensemble B :=
    fun b => exists a, f a b.

  Lemma big_union_upper_bound {A B} :
    forall (f: A -> Ensemble B),
    forall a, Included _ (f a) (big_union f).
  Proof.
  intros f a b H. exists a. trivial.
  Qed.

  Lemma big_union_least {A B} :
    forall (f: A -> Ensemble B),
    forall (bound: Ensemble B),
      (forall a, Included _ (f a) bound) ->
      Included _ (big_union f) bound.
  Proof.
  intros f bound Hbound x [y Hy]. specialize (Hbound y x Hy). trivial.
  Qed.

End FAMILY.

Module SET.

  Definition big_union {A} (S: Ensemble (Ensemble A)) : Ensemble A :=
    fun a => exists aset, S aset /\ aset a.

  Lemma big_union_is_sup {A} :
    forall (S: Ensemble (Ensemble A)), is_sup S (big_union S).
  Proof.
  intros S. split.
  * intros aset Haset a Ha. exists aset. auto.
  * Require Import Classical.
    intros aset Haset. apply NNPP. intro H.
    assert (exists a, (big_union S) a /\ ~ aset a)
      as [a [Ha Haseta]] by firstorder.
    destruct Ha as [aset' [HPaset' Haset'a]].
    apply Haseta. apply (Haset aset'); trivial.
  Qed.

End SET.

Instance SetJoinCompletePreLattice {A} :
  JoinCompletePreLattice (Ensemble A) (Included A) := { }.
Proof.
intros P.
exists (SET.big_union P). apply SET.big_union_is_sup.
Defined.
