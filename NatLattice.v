Require Import MyTactics.
Require Import Lattice.
Require Import Arith.
Require Import Omega.
Require Import Classical.

Instance NatJoinPreLattice : JoinPreLattice nat le :=
{ join := max }.
Proof.
* auto with arith.
* auto with arith.
* auto using Max.max_lub.
Defined.

Instance NatMeetPreLattice : MeetPreLattice nat le :=
{ meet := min }.
Proof.
* auto with arith.
* auto with arith.
* auto using Min.min_glb.
Qed.

Instance NatHasBottom : HasBottom nat le :=
{ bottom := 0 }.
Proof.
intro t. auto with arith.
Qed.

Lemma not_empty_is_sup_in :
  forall (P: nat -> Prop) (sup: nat),
    (exists n, P n) ->
    is_sup P sup ->
    P sup.
Proof.
intros P sup [n0 Hn0] H.
generalize dependent P. revert n0. induction sup; intros n0 P Hn0 Hsup.
* destruct Hsup. specialize (H n0 Hn0).
  compute in H. destruct n0; trivial.
  exfalso. omega.
* destruct (eq_nat_dec n0 (S sup)).
  + congruence.
  + assert (n0 <= sup).
    { destruct Hsup. specialize (H n0 Hn0). compute in H. omega. }
    pose (P' n := P (S n)).
    assert (exists n1, P' n1) as [n1 Hn1].
    { apply NNPP. intro Hempty.
      assert (forall n, ~ P' n) as HP' by firstorder. clear Hempty.
      { unfold P' in HP'.
        assert (is_upper_bound P 0) as H0.
        { intros m Hm. destruct m.
          - reflexivity.
          - exfalso. apply (HP' _ Hm).
        }
        destruct Hsup as [_ HLUB].
        specialize (HLUB _ H0). omega.
      }
    }
    destruct Hsup as [HUB HLUB].
    assert (is_sup P' sup) as Hsup'.
    { unfold P'. split.
      - intros m Hm. specialize (HUB _ Hm). omega.
      - intros m Hm.
        assert (S sup <= S m) as HSm.
        { apply HLUB. intros k Hk.
          destruct k. auto with arith.
          assert (k <= m). { apply Hm. eauto. }
          auto with arith.
        }
        auto with arith.
    }
    specialize (IHsup _ P' Hn1 Hsup').
    assumption.
Qed.

(** The set of all natural numbers. *)
Definition Naturals : nat -> Prop := fun _ => True.

Lemma Naturals_directed : directed Naturals.
Proof.
split.
* exists 0. compute. trivial.
* intros m n Hm Hn. exists (max m n). splits.
  - compute. trivial.
  - auto with arith.
  - auto with arith.
Qed.
