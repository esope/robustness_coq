(*

Verification of the article:

Robust Declassification
Steve Zdancewic, Andrew C. Myers

In Proc. of 14th IEEE Computer Security Foundations Workshop (CSFW),
pages 15-23, Cape Breton, Canada, June 2001.

http://www.cis.upenn.edu/~stevez/papers/ZM01b.pdf

*)

Require Import Relations.
Require Import List.
Require Import RelationClasses.

Record sys (state: Type) :=
{ next : relation state
; next_refl : reflexive state next
}.

Arguments next [state] _ _ _.

Lemma sys_union_next_refl:
  forall A (s1 s2: sys A),
    reflexive A (union A (next s1) (next s2)).
Proof.
intros A s1 s2.
intro x. left. destruct s1 as [next next_refl]. simpl. apply next_refl.
Qed.

Definition sys_union {A} (s1 s2: sys A) : sys A :=
{| next := union A (next s1) (next s2)
;  next_refl := sys_union_next_refl A s1 s2
|}.

Fixpoint is_trace {A} (S: sys A) (l : list A) : Prop :=
match l with
| nil => False
| a :: nil => True
| a1 :: ((a2 :: _) as l2) => next S a1 a2 /\ is_trace S l2
end.

Lemma is_trace_tail {A} {S: sys A}:
  forall a1 a2 (l: list A),
    is_trace S (a1 :: a2 :: l) ->
    is_trace S (a2 :: l).
Proof.
intros a1 a2 l H.
simpl. simpl in H. destruct l. trivial. intuition.
Qed.

Definition trace {A} (S: sys A) := { l: list A | is_trace S l }.

Definition trace_one {A} (S: sys A) (x: A) : trace S.
Proof.
exists (x :: nil). simpl. trivial.
Defined.

Definition hd {A} {S: sys A} (tr : trace S) : A :=
match tr with
| exist nil H => match H with end
| exist (a :: _) _ => a
end.

Definition is_trace_from {A} {S: sys A} (tr: trace S) (s : A) : Prop :=
  hd tr = s.

(* lifts a binary function from lists to traces *)
Definition lift_trace {A B} {S: sys A}
           (f: list A -> list A -> B) (t1 t2: trace S) : B :=
  f (proj1_sig t1) (proj1_sig t2).

Instance lift_Equivalence
         {A} {S: sys A} (R: relation (list A)) {E: Equivalence R}
: Equivalence (@lift_trace A Prop S R).
Proof.
unfold lift_trace.
constructor.
* intros [? ?]. simpl. reflexivity.
* intros [? ?] [? ?] ?. simpl in *. symmetry. assumption.
* intros [? ?] [? ?] [? ?] ? ?. simpl in *. etransitivity; eassumption.
Defined.


Module Stutter. (* proofs about stutter_equiv *)

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
(* * inversion H2'; subst; eauto. *)
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

Lemma stutter_equiv_trans_strong {A} :
  forall n (l1 l2 l3: list A),
    length l1 + length l2 + length l3 <= n ->
    stutter_equiv l1 l2 ->
    stutter_equiv l2 l3 ->
    stutter_equiv l1 l3.
Proof.
Require Import Omega.
intros n; induction n; intros l1 l2 l3 Hn H12 H23.
* destruct l1; destruct l2; destruct l3; simpl in Hn;
  try solve [exfalso; omega]; auto.
* inversion H12; subst; simpl in Hn; auto.
  - inversion H23; subst; simpl in Hn.
    + apply stutter_same. apply (IHn l0 l4 l2); auto. omega.
    + apply (IHn (a :: l0) (a :: l1) l3);
      auto using stutter_equiv_cons_right_add_left. simpl; omega.
    + apply stutter_right.
      apply (IHn (a :: l0) (a :: l4) (a0 :: l2)); auto. simpl; omega.
  - apply stutter_left.
    apply (IHn (a :: l0) l2 l3); auto. simpl; omega.
  - inversion H23; subst; simpl in Hn.
    + apply (IHn l1 (a :: l4) (a :: l2));
      auto using stutter_equiv_cons_left_add_right. simpl; omega.
    + apply (IHn l1 (a :: l4) l3); auto. simpl; omega.
    + apply stutter_right.
      apply (IHn l1 (a :: a :: l4) (a0 :: l2)); auto. simpl; omega.
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

Lemma is_trace_stutter {A} {S: sys A} :
  forall l1 l2,
    is_trace S l1 ->
    stutter_equiv l1 l2 ->
    is_trace S l2.
Proof.
intros l1 l2 Htrace H12.
induction H12.
* inversion Htrace.
* destruct l1.
  - apply stutter_equiv_nil_left_inv in H12.
    subst. auto.
  - destruct l2. simpl; trivial.
    destruct Htrace.
    apply stutter_equiv_cons_inv in H12. subst.
    split; auto.
* apply IHstutter_equiv. apply (is_trace_tail a). assumption.
* split. apply next_refl. auto.
Qed.






End Stutter.

Definition set_included {A} (R: relation A) (S1 S2: A -> Prop) :=
  forall s1, S1 s1 -> exists s2, S2 s2 /\ R s1 s2.

Definition set_equiv {A} (R: relation A) (S1 S2: A -> Prop) :=
  set_included R S1 S2 /\ set_included R S2 S1.

Require Import RelationClasses.
Instance set_equiv_Equivalence {A} {R: relation A} `{Equivalence A R}:
  Equivalence (set_equiv R).
Proof.
constructor.
* intro X; split.
  intros x Hx; exists x; split; [assumption | reflexivity].
  intros x Hx; exists x; split; [assumption | reflexivity].
* intros X Y [HXY HYX]; split; intros ? ?; auto.
* intros X Y Z [HXY HYX] [HYZ HZY]; split.
  - intros x Hx.
    destruct (HXY x Hx) as [y [Hy Hxy]].
    destruct (HYZ y Hy) as [z [Hz Hyz]].
    exists z. split. assumption. transitivity y; assumption.
  - intros z Hz.
    destruct (HZY z Hz) as [y [Hy Hzy]].
    destruct (HYX y Hy) as [x [Hx Hyx]].
    exists x. split. assumption. transitivity y; assumption.
Defined.

Definition stutter {A} {S: sys A} (t1 t2: trace S) : Prop :=
  lift_trace Stutter.stutter_equiv t1 t2.

Definition set_stutter {A} {S: sys A} := set_equiv (@stutter A S).

(* Views *)
Module View.
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
exfalso; omega.
exfalso; omega.
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
simpl in Hlength; try solve [intuition | exfalso; omega ].
simpl. split.
* apply (H a 0); simpl; omega.
* apply IHl1.
  - congruence.
  - intros a' n H1 H2.
    apply (H a' (S n)); simpl; omega.
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

Definition same_view_trace {A} {S: sys A} (R: relation A) (t1 t2: trace S) :=
  lift_trace (same_view R) t1 t2.

Definition view {A} {S: sys A} (R: relation A) (t: trace S)
: trace S -> Prop :=
  same_view_trace R t.

Lemma view_stutter_one_included {A} {S: sys A}
      (R: relation A) {E: Equivalence R} :
  forall s1 s2,
    R s1 s2 ->
    set_included stutter
              (view R (trace_one S s1))
              (view R (trace_one S s2)).
Proof.
intros s1 s2 H [l Hl] Hs.
destruct l. inversion Hl.
compute in Hs.
destruct l.
- exists (trace_one S a). split.
  compute. destruct Hs. split; trivial.
  + transitivity s1. symmetry; assumption. assumption.
  + compute. reflexivity.
- exfalso. tauto.
Qed.

Lemma view_stutter_one {A} {S: sys A}
      (R: relation A) {E: Equivalence R} :
  forall s1 s2,
    R s1 s2 ->
    set_equiv stutter
              (view R (trace_one S s1))
              (view R (trace_one S s2)).
Proof.
intros s1 s2 H.
split; apply view_stutter_one_included; auto.
symmetry; assumption.
Qed.

Lemma view_stutter_compat_included {A} {S: sys A}
      (R: relation A) {E: Equivalence R} :
  forall (t1 t2: trace S),
    same_view_trace R t1 t2 ->
    set_included stutter (view R t1) (view R t2).
Proof.
intros t1 t2 H12.
destruct t1 as [[| a1 l1] Hl1].
(* nil: absurd *) destruct Hl1.
destruct t2 as [[| a2 l2] Hl2].
(* nil: absurd *) destruct Hl2.
destruct H12 as [Ha1a2 Hl1l2].
intros [[| a l] Hal Ha1l1al].
(* nil: absurd *) destruct Hal.
destruct Ha1l1al as [Ha1a Hl1l].
exists (exist _ _ Hal). split.
* split.
  - intuition eauto.
  - transitivity l1. symmetry; trivial. trivial.
* reflexivity.
Qed.

Lemma view_stutter_compat {A} {S: sys A}
      (R: relation A) {E: Equivalence R} :
  forall (t1 t2: trace S),
    view R t1 t2 ->
    set_equiv stutter (view R t1) (view R t2).
Proof.
intros t1 t2 H12. split.
* apply view_stutter_compat_included; trivial.
* apply view_stutter_compat_included; trivial.
  symmetry; trivial.
Qed.

Lemma view_stutter_aux {A} {R: relation A} {E: Equivalence R}:
  forall (t1 t2: list A),
    Stutter.stutter_equiv t1 t2 ->
    exists t0,
      Stutter.stutter_equiv t1 t0 /\
      same_view R t0 t2.
Proof.
intros t1 t2 H. induction H.
* exists nil. split. reflexivity. reflexivity.
* destruct IHstutter_equiv as [l0 [Hl1 Hl2]].
  exists (a :: l0). split.
  auto.
  split. reflexivity. assumption.
* destruct IHstutter_equiv as [l0 [Hl1 Hl2]].
  exists l0. split; auto.
* destruct IHstutter_equiv as [l0 [Hl1 Hl2]].
  exists (a :: l0). split.
  + destruct (Stutter.stutter_equiv_cons_right_inv _ _ _ H). subst.
    destruct (Stutter.stutter_equiv_cons_left_inv _ _ _ Hl1). subst.
    auto.
  + destruct l0; destruct Hl2.
    split. reflexivity. split; trivial.
Qed.

Lemma view_stutter {A} {S: sys A} {R: relation A} {E: Equivalence R}:
  forall (t1 t2: trace S),
    stutter t1 t2 ->
    exists t0,
      stutter t1 t0 /\
      view R t0 t2.
Proof.
intros [t1 H1] [t2 H2] H.
destruct (view_stutter_aux _ _ H) as [t0 [Ht1t0 Ht0t2]].
exists (exist _ _ (Stutter.is_trace_stutter _ _ H1 Ht1t0)).
split; assumption.
Qed.

Lemma stutter_equiv_one_view {A} (R: relation A) {E: Equivalence R} :
  forall (l: list A) a1 a2,
    R a1 a2 ->
    Stutter.stutter_equiv (a2 :: nil) (a2 :: l) ->
    exists t0 : list A,
      Stutter.stutter_equiv (a1 :: nil) t0 /\ same_view R t0 (a2 :: l).
Proof.
intro l. induction l; intros a1 a2 Ha1a2 Hl.
* exists (a1 :: nil). split. reflexivity.
  split. assumption. reflexivity.
* assert (a = a2).
  { inversion Hl; subst.
    - apply (Stutter.stutter_equiv_nil_left_inv) in H0. congruence.
    - trivial. } subst.
  assert (Stutter.stutter_equiv (a2 :: nil) (a2 :: l)) as H'.
  { inversion Hl; subst.
    - apply (Stutter.stutter_equiv_nil_left_inv) in H0. congruence.
    - assumption. }
  destruct (IHl _ _ Ha1a2 H') as [l0 [H1l0 Hl02]].
  exists (a1 :: l0). split.
  - apply Stutter.stutter_equiv_cons_left_add_right. assumption.
  - split; assumption.
Qed.

Lemma test_included {A} {S: sys A} (R: relation A) {E: Equivalence R} :
  forall (c: trace S -> Prop) (t1 t2: trace S),
    set_included stutter (view R t1) c ->
    set_included (view R) c (view R t2) ->
    set_included stutter (view R t1) (view R t2).
Proof.
intros c t1 t2 Ht1c Hct2.
intros t Ht1t.
destruct (Ht1c t Ht1t) as [t1' [Hct1' Htt1']].
destruct (Hct2 t1' Hct1') as [t2' [Ht2t2' Ht1't2']].
exists t1'. split.
+ transitivity t2'. assumption. symmetry. assumption.
+ assumption.
Qed.

End View.

(* Observations *)
Definition obs_from {A} (s : A) (S: sys A) (R: relation A)
: (trace S -> Prop) -> Prop :=
  fun tView =>
    exists (t : trace S), tView = View.view R t /\ is_trace_from t s.

(* Observational equivalence *)
Definition obs_eq {A} (S: sys A) (R: relation A) : relation A :=
  fun s1 s2 =>
    set_equiv (set_equiv (stutter)) (obs_from s1 S R) (obs_from s2 S R).

Instance obs_eq_Equivalence {A} (S: sys A) (R: relation A) {E: Equivalence R}
: Equivalence (obs_eq S R).
Proof.
unfold obs_eq.
constructor.
* intro s. reflexivity.
* intros s1 s2 H. symmetry. assumption.
* intros s1 s2 s3 H12 H23. transitivity (obs_from s2 S R); assumption.
Defined.

Lemma obs_from_self {A} {S: sys A} (R: relation A) {E: Equivalence R}:
  forall s (t: trace S),
    is_trace_from t s ->
    obs_from s S R (View.view R t).
Proof.
intros s [l Hl] H.
destruct l as [| s' l'].
* inversion Hl.
* compute in H. subst.
  exists (exist _ _ Hl). split; reflexivity.
Qed.

Require Import ERLattice.

(* The security property *)
Definition SP {A} (S: sys A) (R: relation A) {E: Equivalence R} :=
  leq (toER (obs_eq S R)) (toER R).

Lemma SP_iff1 {A} (S: sys A) (R: relation A) {E: Equivalence R} :
  SP S R
  <->
  (forall s1 s2,
     R s1 s2 ->
     set_equiv (set_equiv stutter) (obs_from s1 S R) (obs_from s2 S R)).
Proof.
reflexivity.
Qed.

Lemma SP_iff2 {A} (S: sys A) (R: relation A) {E: Equivalence R} :
  SP S R
  <->
  (forall s1 s2,
     R s1 s2 ->
     forall (t1: trace S),
       is_trace_from t1 s1 ->
       exists (t2: trace S),
         is_trace_from t2 s2 /\
         set_equiv stutter (View.view R t1) (View.view R t2)).
Proof.
split; intro H.
* intros s1 s2 HR t1 Ht1.
  specialize (H s1 s2 HR). simpl in H.
  destruct H as [H _].
  specialize (H (View.view R t1) (obs_from_self _ _ _ Ht1)).
  destruct H as [v [Hvs2 Ht1v]].
  destruct Hvs2 as [t2 [Hv Ht2s2]].
  subst v.
  exists t2. auto.
* intros s1 s2 HR. simpl in *. split.
  + intros v1 [t1 [Hv1 Ht1s1]].
    subst v1.
    specialize (H s1 s2 HR t1 Ht1s1).
    destruct H as [t2 [Ht2s2 Ht1t2]].
    exists (View.view R t2). auto using obs_from_self.
  + intros v2 [t2 [Hv2 Ht2s2]].
    subst v2.
    symmetry in HR.
    specialize (H s2 s1 HR t2 Ht2s2).
    destruct H as [t1 [Ht1s1 Ht2t1]].
    exists (View.view R t1). auto using obs_from_self.
Qed.

Lemma prop_2_1 {A} (S: sys A) (R: relation A) {E: Equivalence R} :
  leq (toER R) (toER (obs_eq S R)).
Proof.
intros s1 s2 [H12 _]. simpl.
specialize (H12 (View.view R (trace_one S s1))).
destruct H12 as [v [Hv Hs1v]]. apply obs_from_self; auto. reflexivity.
destruct Hv as [t [Hv Hts2]]. subst v.
destruct Hs1v as [H _].
specialize (H (trace_one S s1)).
destruct H as [t2 [Htt2 Ht1t2]]. reflexivity.
destruct t as [[| s l] Hl]; [destruct Hl |].
compute in Hts2. subst s.
destruct (Stutter.stutter_equiv_cons_left_inv _ _ _ Ht1t2) as [l' ?].
destruct t2 as [l2 ?]. simpl in H. subst.
destruct Htt2. symmetry. assumption.
Qed.

Lemma corollary_2_1 {A} (S: sys A) (R: relation A) {E: Equivalence R} :
  SP S R -> equiv (toER R) (toER (obs_eq S R)).
Proof.
intros H. split.
apply prop_2_1. assumption.
Qed.

Lemma SP_bottom {A} (S: sys A) :
  SP S (er_bottom_rel A).
Proof.
intros s1 s2 H. split.
* intros s [t [Ht Hts]]. subst s. clear H.
  destruct t as [l Hl]. generalize dependent s1.
  induction l; intros s1 Hs1.
  - destruct Hl.
  - compute in Hs1. subst a.
    destruct l as [| a' l'].
    + { exists (View.view (er_bottom_rel A) (trace_one S s2)). split.
        * apply obs_from_self; auto. reflexivity.
        * split.
          - intros s Hs. exists s. split.
            + destruct s as [[| a' l'] Hl']; [destruct Hl'|].
              destruct l' as [| a'' l''].
              compute. tauto.
              compute in Hs. tauto.
            + reflexivity.
          - intros s Hs. exists s. split.
            + destruct s as [[| a' l'] Hl']; [destruct Hl'|].
              destruct l' as [| a'' l''].
              compute. tauto.
              compute in Hs. tauto.
            + reflexivity. }
    + { destruct Hl as [Hs1a' Hl'].
        specialize (IHl Hl' a').
        destruct IHl as [v [Hv Ha'l'v]]. reflexivity.
        destruct Hv as [t [Hv Hts2]]. subst v.
        exists (View.view (er_bottom_rel A) t). split.
        * apply obs_from_self; auto.
        * split.
          + admit.
          + admit. }
* admit.
Admitted.

Lemma SP_top {A} (S: sys A) :
  SP S (proj1_sig (er_top A)).
Proof.
intros s1 s2 H. rewrite H.
reflexivity.
Qed.
