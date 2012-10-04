Require Import MyTactics.
Require Export List.
Require Import RelationClasses.

Inductive stutter_equiv {A} : list A -> list A -> Prop :=
| stutter_nil: stutter_equiv nil nil
| stutter_same:
    forall a l1 l2,
      stutter_equiv l1 l2 ->
      stutter_equiv (a :: l1) (a :: l2)
| stutter_left:
    forall a l1 l2,
      stutter_equiv (a :: l1) l2 ->
      stutter_equiv (a :: a :: l1) l2
| stutter_right:
    forall a l1 l2,
      stutter_equiv l1 (a :: l2) ->
      stutter_equiv l1 (a :: a :: l2)
.
Hint Constructors stutter_equiv.

Lemma stutter_equiv_refl {A} :
  forall (l : list A),
    stutter_equiv l l.
Proof.
intros x. induction x; auto.
Qed.

Hint Extern 3 (stutter_equiv _ _) => reflexivity.

Lemma stutter_equiv_sym {A} :
  forall (l1 l2 : list A),
    stutter_equiv l1 l2 ->
    stutter_equiv l2 l1.
Proof.
intros x y Hxy. induction Hxy; auto.
Qed.

Lemma stutter_equiv_cons_inv {A} :
  forall a1 a2 (l1 l2 : list A),
    stutter_equiv (a1 :: l1) (a2 :: l2) ->
    a1 = a2.
Proof.
intros a1 a2 l1 l2 H.
remember (a1 :: l1) as l1'.
remember (a2 :: l2) as l2'.
generalize dependent l2. generalize dependent l1.
revert a2. revert a1.
rename l1' into l1. rename l2' into l2.
induction H; intros a1' a2' l1' H1' l2' H2'; inversion H1'; subst; eauto.
* inversion H2'; subst; eauto.
* inversion H2'; subst; eauto.
Qed.

Lemma stutter_equiv_cons_left_inv {A} :
  forall a (l1 l2: list A),
    stutter_equiv (a :: l1) l2 ->
    exists l2', l2 = a :: l2'.
Proof.
intros a l1 l2 H.
remember (a :: l1) as l1'.
generalize dependent l1. revert a.
rename l1' into l1.
induction H; intros a' l' Heq; inversion Heq; subst; eauto.
apply stutter_equiv_cons_inv in H. subst. eauto.
Qed.

Lemma stutter_equiv_cons_right_inv {A} :
  forall a (l1 l2: list A),
    stutter_equiv l1 (a :: l2) ->
    exists l1', l1 = a :: l1'.
Proof.
intros a l1 l2 H.
apply stutter_equiv_sym in H.
eapply stutter_equiv_cons_left_inv. eauto.
Qed.

Lemma stutter_equiv_cons_right_add_left {A} :
  forall a (l1 l2: list A),
    stutter_equiv l1 (a :: l2) ->
    stutter_equiv (a :: l1) (a :: l2).
Proof.
intros a l1 l2 H.
destruct (stutter_equiv_cons_right_inv _ _ _ H) as [l1' H'].
subst. auto.
Qed.

Lemma stutter_equiv_cons_left_add_right {A} :
  forall a (l1 l2: list A),
    stutter_equiv (a :: l1) l2 ->
    stutter_equiv (a :: l1) (a :: l2).
Proof.
intros a l1 l2 H.
destruct (stutter_equiv_cons_left_inv _ _ _ H) as [l2' H'].
subst. auto.
Qed.

Lemma stutter_equiv_nil_left_inv {A} :
  forall (l: list A),
    stutter_equiv nil l ->
    l = nil.
Proof.
intros l2 H12. remember nil as l1.
induction H12; try congruence.
specialize (IHstutter_equiv Heql1). congruence.
Qed.

Lemma stutter_equiv_nil_right_inv {A} :
  forall (l: list A),
    stutter_equiv l nil ->
    l = nil.
Proof.
intros l H. apply stutter_equiv_nil_left_inv.
apply stutter_equiv_sym. assumption.
Qed.

Lemma stutter_equiv_cons_end_inv {A} :
  forall a1 a2 (l1 l2 : list A),
    stutter_equiv (l1 ++ a1 :: nil) (l2 ++ a2 :: nil) ->
    a1 = a2.
Proof.
intros a1 a2 l1 l2 H.
remember (l1 ++ a1 :: nil) as l1'.
remember (l2 ++ a2 :: nil) as l2'.
generalize dependent l2. generalize dependent l1.
revert a2. revert a1.
rename l1' into l1. rename l2' into l2.
induction H; intros a1' a2' l1' H1' l2' H2'; inversion H1'; subst.
* exfalso. destruct l1'; simpl in H1'; congruence.
* destruct l1' as [|a1'' l1']; destruct l2' as [|a2'' l2']; simpl in *.
  - congruence.
  - exfalso. inversion H1'; subst.
    apply stutter_equiv_nil_left_inv in H. subst.
    destruct l2'; simpl in H2'; congruence.
  - exfalso. inversion H2'; subst.
    apply stutter_equiv_nil_right_inv in H. subst.
    destruct l1'; simpl in H1'; congruence.
  - inversion H1'; subst. inversion H2'; subst. eauto.
* destruct l1' as [| a1'' l1'].
  - exfalso. inversion H1.
  - rewrite <- app_comm_cons in H1. inversion H1; subst.
    destruct l2' as [| a2'' l2'].
    + apply stutter_equiv_cons_inv in H. subst. eauto.
    + rewrite <- app_comm_cons in H.
      apply stutter_equiv_cons_inv in H. subst.
      eauto.
* destruct l2' as [| a2'' l2'].
  - exfalso. inversion H2'.
  - rewrite <- app_comm_cons in H2'. inversion H2'; subst.
    destruct l1' as [| a1'' l1'].
    + apply stutter_equiv_cons_inv in H. subst. eauto.
    + rewrite <- app_comm_cons in H.
      apply stutter_equiv_cons_inv in H. subst.
      eauto.
Qed.

Lemma stutter_equiv_cons_end_left_inv {A} :
  forall a (l1 l2: list A),
    stutter_equiv (l1 ++ a :: nil) l2 ->
    exists l2', l2 = l2' ++ a :: nil.
Proof.
intros a l1 l2 H.
remember (l1 ++ a :: nil) as l1'.
generalize dependent l1. revert a.
rename l1' into l1.
induction H; intros a' l' Heq; eauto.
* destruct l' as [| a'' l'].
  - inversion Heq; subst.
    apply stutter_equiv_nil_left_inv in H. subst. eauto.
  - rewrite <- app_comm_cons in Heq. inversion Heq; subst.
    destruct (IHstutter_equiv a' l' eq_refl) as [l0 Hl0].
    subst.
    exists (a'' :: l0). apply app_comm_cons.
* destruct l' as [| a'' l'].
  - exfalso. inversion Heq.
  - rewrite <- app_comm_cons in Heq. inversion Heq; subst.
    destruct (IHstutter_equiv a' l') as [l0 Hl0].
    congruence. subst. eauto.
* subst. destruct (IHstutter_equiv a' l' eq_refl) as [l0 Hl0].
  exists (a :: l0). rewrite <- app_comm_cons. congruence.
Qed.

Lemma stutter_equiv_cons_end_right_inv {A} :
  forall a (l1 l2: list A),
    stutter_equiv l1 (l2 ++ a :: nil) ->
    exists l1', l1 = l1' ++ a :: nil.
Proof.
intros a l1 l2 H.
apply stutter_equiv_sym in H.
eapply stutter_equiv_cons_end_left_inv. eauto.
Qed.

Lemma stutter_equiv_cons_end_right_add_left {A} :
  forall a (l1 l2: list A),
    stutter_equiv l1 (l2 ++ a :: nil) ->
    stutter_equiv (l1 ++ a :: nil) (l2 ++ a :: nil).
Proof.
intros a l1 l2 H.
remember (l2 ++ a :: nil) as l2'.
generalize dependent l2. revert a.
rename l2' into l2.
induction H; intros a' l2' Heq.
* exfalso. destruct l2'; simpl in Heq; congruence.
* destruct l2' as [| a2'' l2'].
  - inversion Heq; subst.
    apply stutter_equiv_nil_right_inv in H. subst.
    simpl. auto.
  - rewrite <- app_comm_cons in Heq. inversion Heq; subst.
    rewrite <- app_comm_cons. apply stutter_same.
    eauto.
* subst. rewrite <- app_comm_cons. rewrite <- app_comm_cons.
  apply stutter_left. rewrite app_comm_cons. eauto.
* destruct l2' as [|a2'' l2'].
  - exfalso. inversion Heq.
  - rewrite <- app_comm_cons in Heq. inversion Heq; subst.
    apply stutter_right. eauto.
Qed.

Lemma stutter_equiv_cons_end_left_add_right {A} :
  forall a (l1 l2: list A),
    stutter_equiv (l1 ++ a :: nil) l2 ->
    stutter_equiv (l1 ++ a :: nil) (l2 ++ a :: nil).
Proof.
intros a l1 l2 H.
apply stutter_equiv_sym.
apply stutter_equiv_cons_end_right_add_left.
apply stutter_equiv_sym. trivial.
Qed.

Lemma stutter_equiv_trans_strong {A} :
  forall n (l1 l2 l3: list A),
    length l1 + length l2 + length l3 <= n ->
    stutter_equiv l1 l2 ->
    stutter_equiv l2 l3 ->
    stutter_equiv l1 l3.
Proof.
intros n; induction n; intros l1 l2 l3 Hn H12 H23.
* destruct l1; destruct l2; destruct l3; simpl in Hn; auto.
* inversion H12; subst; simpl in Hn; auto.
  - inversion H23; subst; simpl in Hn.
    + apply stutter_same. apply (IHn l0 l4 l2); auto.
    + apply (IHn (a :: l0) (a :: l1) l3);
      auto using stutter_equiv_cons_right_add_left.
    + apply stutter_right.
      apply (IHn (a :: l0) (a :: l4) (a0 :: l2)); auto.
  - apply stutter_left.
    apply (IHn (a :: l0) l2 l3); auto.
  - inversion H23; subst; simpl in Hn.
    + apply (IHn l1 (a :: l4) (a :: l2));
      auto using stutter_equiv_cons_left_add_right.
    + apply (IHn l1 (a :: l4) l3); auto.
    + apply stutter_right.
      apply (IHn l1 (a :: a :: l4) (a0 :: l2)); auto.
Qed.

Lemma stutter_equiv_trans {A} :
  forall (l1 l2 l3: list A),
    stutter_equiv l1 l2 ->
    stutter_equiv l2 l3 ->
    stutter_equiv l1 l3.
Proof.
intros l1 l2 l3 H12 H23.
apply (stutter_equiv_trans_strong (length l1 + length l2 + length l3) l1 l2 l3);
trivial.
Qed.

Instance stutter_equiv_Equivalence {A} : Equivalence (@stutter_equiv A).
Proof.
constructor.
* exact stutter_equiv_refl.
* exact stutter_equiv_sym.
* exact stutter_equiv_trans.
Defined.

Lemma stutter_equiv_in {A} :
  forall (l1 l2 : list A),
    stutter_equiv l1 l2 ->
    forall a, In a l1 -> In a l2.
Proof.
intros l1 l2 H a Ha. induction H.
* inversion Ha.
* destruct Ha as [Ha | Ha].
  - left; congruence.
  - right; auto.
* destruct Ha as [Ha | Ha].
  - subst; apply IHstutter_equiv. left; trivial.
  - destruct Ha as [Ha | Ha]; apply IHstutter_equiv.
    + left; congruence.
    + right; trivial.
* right. auto.
Qed.

Lemma stutter_equiv_app_left {A} :
  forall (l l1 l2: list A),
    stutter_equiv l1 l2 ->
    stutter_equiv (l ++ l1) (l ++ l2).
Proof.
intros l l1 l2 H. induction l; simpl; auto.
Qed.

Lemma stutter_equiv_app_right {A} :
  forall (l l1 l2: list A),
    stutter_equiv l1 l2 ->
    stutter_equiv (l1 ++ l) (l2 ++ l).
Proof.
intros l. induction l; intros l1 l2 H.
* repeat rewrite app_nil_r. assumption.
* replace (a :: l) with ((a :: nil) ++ l) by reflexivity.
  repeat rewrite app_assoc. apply IHl.
  clear IHl l. induction H; simpl; auto.
Qed.

Lemma stutter_equiv_congruence {A} :
  forall (l1 l2 l3 l4: list A),
    stutter_equiv l1 l2 ->
    stutter_equiv l3 l4 ->
    stutter_equiv (l1 ++ l3) (l2 ++ l4).
Proof.
intros l1 l2 l3 l4 H12 H34.
transitivity (l2 ++ l3).
apply stutter_equiv_app_right; assumption.
apply stutter_equiv_app_left; assumption.
Qed.

Fixpoint repeat {A} (a: A) (n: nat) : list A :=
match n with
| O => nil
| S n => a :: repeat a n
end.

Lemma stutter_equiv_repeat {A} :
  forall (a: A) n,
    stutter_equiv (a :: nil) (a :: repeat a n).
Proof.
intros a n. induction n; simpl; auto.
Qed.

Lemma repeat_length {A} :
  forall (a: A) n, length (repeat a n) = n.
Proof.
intros a n. induction n; simpl in *; auto.
Qed.

Lemma repeat_nth {A} :
  forall (a a0 : A) k n,
    k < n ->
    nth k (repeat a n) a0 = a.
Proof.
intros a a0 k n H.
generalize dependent k. revert a. induction n; intros a k H; auto.
simpl. destruct k; auto.
Qed.

Lemma stutter_one_inv {A} :
  forall a (l: list A),
    stutter_equiv l (a :: nil) ->
    exists n, l = a :: repeat a n.
Proof.
intros a l H. induction l.
* apply stutter_equiv_nil_left_inv in H. congruence.
* assert (a0 = a). { apply stutter_equiv_cons_inv in H. assumption. }
  subst a0. inversion H; subst.
  + exists 0. apply stutter_equiv_nil_right_inv in H1. subst. reflexivity.
  + destruct IHl as [n Heq]; trivial.
    exists (S n). rewrite Heq. reflexivity.
Qed.

Lemma stutter_two_inv {A} :
  forall a1 a2 (l: list A),
    a1 <> a2 ->
    stutter_equiv l (a1 :: a2 :: nil) ->
    exists n1 n2, l = a1 :: repeat a1 n1 ++ a2 :: repeat a2 n2.
Proof.
intros a1 a2 l Ha Hl. induction l.
* apply stutter_equiv_nil_left_inv in Hl. congruence.
* assert (a = a1). { apply stutter_equiv_cons_inv in Hl. assumption. }
  subst a. destruct l as [| a l].
  + inversion Hl; subst.
    - apply stutter_equiv_nil_left_inv in H0. congruence.
    - congruence.
  + inversion Hl; subst.
    - destruct (stutter_one_inv _ _ H0) as [n2 Hn2].
      exists 0. exists n2. simpl. congruence.
    - destruct IHl as [n1 [n2 Heq]]; trivial.
      exists (S n1). exists n2. simpl. congruence.
    - congruence.
Qed.

Lemma stutter_equiv_app_left_inv {A} :
  forall a (l1 l2 l3: list A),
    stutter_equiv (l1 ++ a :: l2) l3 ->
    exists l1' l2',
      l3 = l1' ++ a :: l2'
      /\ stutter_equiv (l1 ++ a :: nil) (l1' ++ a :: nil)
      /\ stutter_equiv (a :: l2) (a :: l2').
Proof.
intros a l1 l2 l3 H.
remember (l1 ++ a :: l2) as l1'.
generalize dependent l2. revert a l1. rename l1' into l1.
induction H; intros a' l1' l2' Heq.
* exfalso. destruct l1'; inversion Heq.
* destruct l1' as [|a1' l1'].
  - inversion Heq; subst.
    exists nil. exists l2. simpl. auto.
  - rewrite <- app_comm_cons in Heq. inversion Heq; subst.
    destruct (IHstutter_equiv a' l1' l2' eq_refl) as [l1'' [l2'' [? [? ?]]]].
    subst.
    exists (a1' :: l1''). exists l2''.
    repeat rewrite <- app_comm_cons. auto.
* destruct l1' as [|a1' l1'].
  - inversion Heq; subst.
    destruct (IHstutter_equiv a' nil l1 eq_refl) as [l1'' [l2'' [? [? ?]]]].
    subst. exists l1''. exists l2''. auto.
  - rewrite <- app_comm_cons in Heq. inversion Heq; subst.
    destruct (stutter_equiv_cons_left_inv _ _ _ H) as [l2'' H2''].
    subst.
    destruct (IHstutter_equiv a' l1' l2' H2) as [l1'' [l0 [? [? ?]]]].
    exists l1''. exists l0. splits; trivial.
    { destruct l1'' as [|a1'' l1''].
      * inversion H0; subst. clear H0.
        destruct (stutter_one_inv _ _ H1) as [n Hn].
        rewrite <- app_comm_cons. rewrite Hn.
        apply stutter_left. symmetry. apply stutter_equiv_repeat.
      * rewrite <- app_comm_cons in H0. inversion H0; subst.
        repeat rewrite <- app_comm_cons.
        rewrite <- app_comm_cons in H1.
        apply stutter_equiv_cons_right_add_left. trivial.
    }
* subst. destruct l1' as [|a1' l1'].
  - assert (a' = a). { apply stutter_equiv_cons_inv in H. assumption. }
    subst. exists (a :: nil). exists l2. simpl; auto.
  - rewrite <- app_comm_cons in H.
    assert (a1' = a). { apply stutter_equiv_cons_inv in H. assumption. }
    subst.
    destruct (IHstutter_equiv a' (a :: l1') l2' eq_refl)
      as [l1'' [l2'' [? [? ?]]]].
    { destruct l1'' as [|a1'' l1''].
      * inversion H0; subst. clear H0. simpl in *.
        destruct (stutter_one_inv _ _ H1) as [n Hn].
        exists (a' :: nil). exists l2''.
        splits; trivial.
        simpl. rewrite Hn. apply stutter_right.
        symmetry. apply stutter_equiv_repeat.
      * rewrite <- app_comm_cons in H0. inversion H0; subst. clear H0.
        exists (a1'' :: a1'' :: l1''). exists l2''.
        repeat rewrite <- app_comm_cons. auto.
    }
Qed.

Lemma stutter_equiv_app_right_inv {A} :
  forall a (l1 l2 l3: list A),
    stutter_equiv l1 (l2 ++ a :: l3) ->
    exists l2' l3',
      l1 = l2' ++ a :: l3'
      /\ stutter_equiv (l2' ++ a :: nil) (l2 ++ a :: nil)
      /\ stutter_equiv (a :: l3') (a :: l3).
Proof.
intros a l1 l2 l3 H.
symmetry in H.
destruct (stutter_equiv_app_left_inv _ _ _ _ H) as [l2' [l3' [? [? ?]]]].
exists l2'. exists l3'. symmetry in H1. symmetry in H2. auto.
Qed.

