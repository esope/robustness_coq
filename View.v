Require Import MyTactics.
Require Export List.
Require Import Relations.
Require Import RelationClasses.
Require Import Stutter.

(* Views *)
Fixpoint same_view {A} (R: relation A) (l1 l2: list A) :=
  match (l1, l2) with
    | (nil, nil) => True
    | (a1 :: l1, a2 :: l2) => R a1 a2 /\ same_view R l1 l2
    | _ => False
  end.

Instance same_view_Equivalence {A}
         (R: relation A) {E: Equivalence R} : Equivalence (same_view R).
Proof.
constructor.
* intro l. induction l; simpl; intuition.
* intros l1. induction l1; intros l2 H12.
  + destruct l2; simpl in *; auto.
  + destruct l2; simpl; auto.
    destruct H12. intuition.
* intros l1. induction l1; intros l2 l3 H12 H23.
  + destruct l2; destruct l3; simpl in *; auto.
  + destruct l2; destruct l3; simpl in *; try tauto.
    destruct H12; destruct H23. intuition eauto.
Qed.

Hint Extern 3 (same_view _ _ _) => reflexivity.

Lemma same_view_cons_left_inv {A} (R: relation A) :
  forall a1 (l1 l2: list A),
    same_view R (a1 :: l1) l2 ->
    exists a2 l2', R a1 a2 /\ l2 = a2 :: l2'.
Proof.
intros a1 l1 l2 H.
destruct l2 as [| a2 l2]; simpl in H; intuition eauto.
Qed.

Lemma same_view_cons_right_inv {A} (R: relation A) :
  forall a2 (l1 l2: list A),
    same_view R l1 (a2 :: l2) ->
    exists a1 l1', R a1 a2 /\ l1 = a1 :: l1'.
Proof.
intros a2 l1 l2' H.
generalize dependent l2'. revert a2.
induction l1; intros a2 l2' H; simpl in H; intuition eauto.
Qed.

Lemma same_view_app_left {A} (R: relation A) {E: Equivalence R} :
  forall (l l1 l2: list A),
    same_view R l1 l2 ->
    same_view R (l ++ l1) (l ++ l2).
Proof.
intros l. induction l; intros l1 l2 H.
* assumption.
* simpl. intuition.
Qed.

Lemma same_view_app_right {A} (R: relation A) {E: Equivalence R} :
  forall (l l1 l2: list A),
    same_view R l1 l2 ->
    same_view R (l1 ++ l) (l2 ++ l).
Proof.
intros l. induction l; intros l1 l2 H.
* repeat rewrite app_nil_r. assumption.
* replace (a :: l) with ((a :: nil) ++ l) by reflexivity.
  repeat rewrite app_assoc.
  apply IHl. clear IHl l.
  generalize dependent l2. induction l1; intros l2 H.
  - destruct l2.
    + simpl; intuition.
    + simpl in H. destruct H.
  - destruct l2.
    + simpl in H. destruct H.
    + destruct H. simpl. intuition.
Qed.

Lemma same_view_congruence {A} (R: relation A) {E: Equivalence R} :
  forall (l1 l2 l3 l4: list A),
    same_view R l1 l2 ->
    same_view R l3 l4 ->
    same_view R (l1 ++ l3) (l2 ++ l4).
Proof.
intros l1 l2 l3 l4 H12 H34.
transitivity (l2 ++ l3).
apply same_view_app_right; trivial.
apply same_view_app_left; trivial.
Qed.

Lemma same_view_length {A} (R: relation A) :
  forall l1 l2,
    same_view R l1 l2 -> length l1 = length l2.
Proof.
intros l1. induction l1; intros l2 H; destruct l2; simpl in *; intuition.
Qed.

Lemma same_view_nth {A} (R: relation A) :
  forall n a l1 l2,
    n < length l1 ->
    n < length l2 ->
    same_view R l1 l2 ->
    R (nth n l1 a) (nth n l2 a).
Proof.
intros n.
induction n; intros a l1 l2 H;
destruct l1; destruct l2; simpl in *; intuition.
Qed.

Lemma nth_same_view {A} (R: relation A) :
  forall l1 l2,
    length l1 = length l2 ->
    (forall a n, n < length l1 ->
                 n < length l2 ->
                 R (nth n l1 a) (nth n l2 a)) ->
    same_view R l1 l2.
Proof.
intros l1.
induction l1; intros l2 Hlength H; destruct l2;
simpl in Hlength; intuition. split.
* apply (H a 0); auto.
* apply IHl1.
  - congruence.
  - intros a' n H1 H2. apply (H a' (S n)); auto.
Qed.

Lemma same_view_characterization {A} (R: relation A):
  forall l1 l2,
    same_view R l1 l2 <->
    (length l1 = length l2
     /\ forall a n, n < length l1 ->
                    n < length l2 ->
                    R (nth n l1 a) (nth n l2 a)).
Proof.
intros l1 l2. split; intro H.
* split.
  - eauto using same_view_length.
  - intros a n H1 H2. apply same_view_nth; assumption.
* destruct H as [Hlength Hnth].
  apply nth_same_view; assumption.
Qed.

Lemma In_nth {A} :
  forall a (l: list A),
    In a l -> exists n, n < length l /\ forall b, nth n l b = a.
Proof.
intros a l H. generalize dependent a. induction l; intros a' H'.
* destruct H'.
* destruct H'.
  + subst a'. exists 0. split; auto.
  + destruct (IHl a' H) as [n [Hn Hnth]].
    exists (S n). split; auto.
Qed.

Lemma same_view_in {A} {R: relation A}:
  forall a1 l1 l2,
    In a1 l1 ->
    same_view R l1 l2 ->
    exists a2, In a2 l2 /\ R a1 a2.
Proof.
intros a1 l1 l2 Ha1 H.
rewrite same_view_characterization in H.
destruct H as [Hlength HR].
destruct (In_nth _ _ Ha1) as [n [Hn Hna1]].
exists (nth n l2 a1). split.
apply nth_In. congruence.
rewrite <- (Hna1 a1) at 1.
apply HR; congruence.
Qed.

Lemma view_stutter {A} {R: relation A} {E: Equivalence R}:
  forall (t1 t2: list A),
    stutter_equiv t1 t2 ->
    exists t0,
      stutter_equiv t1 t0 /\
      same_view R t0 t2.
Proof.
intros t1 t2 H. induction H.
* exists nil. split. reflexivity. reflexivity.
* destruct IHstutter_equiv as [l0 [Hl1 Hl2]].
  exists (a :: l0). deep_splits; auto.
* destruct IHstutter_equiv as [l0 [Hl1 Hl2]].
  exists l0. split; auto.
* destruct IHstutter_equiv as [l0 [Hl1 Hl2]].
  exists (a :: l0). split.
  + destruct (stutter_equiv_cons_right_inv _ _ _ H). subst.
    destruct (stutter_equiv_cons_left_inv _ _ _ Hl1). subst.
    auto.
  + destruct l0; destruct Hl2. deep_splits; trivial. reflexivity.
Qed.

Lemma stutter_equiv_one_view {A} (R: relation A) {E: Equivalence R} :
  forall (l: list A) a1 a2,
    R a1 a2 ->
    stutter_equiv (a2 :: nil) (a2 :: l) ->
    exists t0 : list A,
      stutter_equiv (a1 :: nil) t0 /\ same_view R t0 (a2 :: l).
Proof.
intro l. induction l; intros a1 a2 Ha1a2 Hl.
* exists (a1 :: nil). deep_splits; trivial. reflexivity.
* assert (a = a2).
  { inversion Hl; subst.
    - apply (stutter_equiv_nil_left_inv) in H0. congruence.
    - trivial. } subst.
  assert (stutter_equiv (a2 :: nil) (a2 :: l)) as H'.
  { inversion Hl; subst.
    - apply (stutter_equiv_nil_left_inv) in H0. congruence.
    - assumption. }
  destruct (IHl _ _ Ha1a2 H') as [l0 [H1l0 Hl02]].
  exists (a1 :: l0). deep_splits; trivial.
  apply stutter_equiv_cons_left_add_right. assumption.
Qed.

Lemma repeat_same_view {A} (R: relation A) {E: Equivalence R}:
  forall a1 a2 (l: list A),
    stutter_equiv l (a1 :: nil) ->
    R a1 a2 ->
    same_view R l (repeat a2 (length l)).
Proof.
intros a1 a2 l Hl HR.
rewrite same_view_characterization. split.
* symmetry. apply repeat_length.
* intros a n H1 H2.
  rewrite repeat_nth; trivial.
  destruct (stutter_one_inv _ _ Hl) as [m Heq].
  assert (l = repeat a1 (S m)) as Hlm by assumption.
  assert (length l = S m). { rewrite Hlm. apply repeat_length. }
  rewrite Hlm.
  rewrite repeat_nth; auto.
Qed.

Lemma repeat_two_same_view {A} (R: relation A) {E: Equivalence R}:
  forall a1 a2 a1' a2' n1 n2,
    R a1 a1' ->
    R a2 a2' ->
    same_view R
      (repeat a1  n1 ++ a2  :: repeat a2  n2)
      (repeat a1' n1 ++ a2' :: repeat a2' n2).
Proof.
intros a1 a2 a1' a2' n1 n2 H1 H2. induction n1.
* simpl. split; trivial.
  clear a1 a1' H1. induction n2.
  + simpl. trivial.
  + simpl. split; assumption.
* simpl. split; assumption.
Qed.

(* This lemma is WRONG!!
Lemma stutter_view_swap {A} {S: sys A}
      {R: relation A} {E: Equivalence R} :
  forall (t1 t0 t2 : trace S),
    stutter t1 t0 ->
    view R t0 t2 ->
    exists t0', view R t1 t0' /\ stutter t0' t2.

Example: suppose
R a a1, R a a2 and a1 <> a2:
we have
stutter [a] [a;a] and view R [a;a] [a1;a2]
but there is no way to commute the relations. Indeed:
view R [a] [a]  ... and we're stuck, or
view R [a] [a1] ... and we're stuck, or
view R [a] [a2] ... and we're stuck!
*)

(* This lemma is WRONG!!
Lemma view_stutter_swap {A} {S: sys A}
      {R: relation A} {E: Equivalence R} :
  forall (t1 t0 t2 : trace S),
    view R t1 t0 ->
    stutter t0 t2 ->
    exists t0', stutter t1 t0' /\ view R t0' t2.

Example: suppose
R a a1, R a a2 and a1 <> a2:
we have
view R [a1;a2] [a;a] and stutter [a;a] [a]
but there is no way to commute the relations. Indeed:
stutter [a1;a2] [a1;...;a1;a2;...;a2] ... and we're stuck!
*)

Lemma same_view_subrel {A}
      (R1: relation A) {E1: Equivalence R1}
      (R2: relation A) {E2: Equivalence R2} :
  (forall x y, R1 x y -> R2 x y) ->
  forall l l': list A,
    same_view R1 l l' ->
    same_view R2 l l'.
Proof.
intros H12 l l' H1.
generalize dependent l'. induction l; intros l' H1.
* destruct l'; [| destruct H1]. auto.
* destruct l' as [| a' l']; [destruct H1 |].
  destruct H1 as [Haa' Hll'].
  split; auto.
Qed.

Lemma same_view_repeats_inv {A} (R: relation A) {E: Equivalence R}:
  forall n1 n2 x y (l: list A),
    same_view R l (x :: repeat x n1 ++ y :: repeat y n2) ->
    exists (x' y' : A) (l' : list A),
      l = x' :: l' ++ y' :: nil /\ R y y'.
Proof.
intro n1; induction n1; intros n2 x y l H.
* destruct l as [|x' l]; [destruct H|]. destruct H as [Hx'x H].
  destruct l as [|y' l]; [destruct H|]. destruct H as [Hy'y H].
  exists x'.
  destruct l as [|z' l].
  + destruct n2; [| destruct H].
    exists y'. exists nil. split. trivial. symmetry; trivial.
  + destruct n2; [destruct H|].
    assert (exists y' l', z' :: l = l' ++ y' :: nil /\ R y' y) as H'.
    { clear x x' y' Hx'x Hy'y.
      generalize dependent z'. generalize dependent l.
      induction n2; intros l z' H.
      * destruct H as [Hz'y H]. destruct l; [| destruct H].
        exists z'. exists nil. tauto.
      * destruct H as [_ H].
        destruct l as [|t l]; [destruct H|].
        specialize (IHn2 _ _ H).
        destruct IHn2 as [t' [l' [Heq HR]]].
        exists t'. exists (z' :: l'). split.
        - rewrite Heq. rewrite app_comm_cons. trivial.
        - trivial.
    }
    destruct H' as [t' [l' [Heq HR]]].
    exists t'. destruct l' as [|u l'].
    - inversion Heq; subst. exists (y' :: nil). split.
      trivial. symmetry; trivial.
    - rewrite <- app_comm_cons in Heq. inversion Heq; subst.
      exists (y' :: u :: l'). split. trivial. symmetry; trivial.
* destruct l as [|x' l]; [destruct H|]. destruct H as [Hx'x H].
  simpl in H. specialize (IHn1 _ _ _ _ H).
  destruct IHn1 as [t' [y' [l' [Heq HR]]]].
  exists x'. exists y'.
  subst. exists (t' :: l'). split.
  rewrite app_comm_cons. trivial. trivial.
Qed.

Lemma same_view_app_inv_left {A} {R: relation A} {E: Equivalence R}:
  forall l1 l2 l3 : list A,
    same_view R (l1 ++ l2) l3 ->
    exists l1' l2',
      l3 = l1' ++ l2'
      /\ same_view R l1 l1'
      /\ same_view R l2 l2'.
Proof.
intros l1; induction l1; intros l2 l3 H.
* exists nil. exists l3. splits; trivial. reflexivity.
* rewrite <- app_comm_cons in H. destruct l3 as [|a3 l3]; [destruct H|].
  destruct H as [Haa3 H].
  destruct (IHl1 _ _ H) as [l1' [l2' [Heq [H1 H2]]]].
  clear IHl1.
  exists (a3 :: l1'). exists l2'. split.
  + rewrite Heq. apply app_comm_cons.
  + deep_splits; trivial.
Qed.

Lemma same_view_app_inv_right {A} {R: relation A} {E: Equivalence R}:
  forall l1 l2 l3 : list A,
    same_view R l1 (l2 ++ l3) ->
    exists l2' l3',
      l1 = l2' ++ l3'
      /\ same_view R l2 l2'
      /\ same_view R l3 l3'.
Proof.
intros l1 l2 l3 H.
apply same_view_app_inv_left. symmetry. trivial.
Qed.
