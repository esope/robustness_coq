(*

Verification of the article:

Robust Declassification
Steve Zdancewic, Andrew C. Myers

In Proc. of 14th IEEE Computer Security Foundations Workshop (CSFW),
pages 15-23, Cape Breton, Canada, June 2001.

http://www.cis.upenn.edu/~stevez/papers/ZM01b.pdf

*)

Require Import MyTactics.
Require Import Relations.
Require Import List.
Require Import RelationClasses.
Require Import Stutter.

Ltac equivalence_reflexivity :=
  match goal with
    | E: Equivalence ?R |- ?R _ _ => reflexivity
  end.
Hint Extern 3 => equivalence_reflexivity.
Hint Extern 3 (_ = _) => reflexivity.

Record sys (state: Type) :=
{ next : relation state
; next_refl : reflexive state next
}.

Arguments next [state] _ _ _.

Ltac sys_next_reflexivity :=
  match goal with
    | S: sys _ |- next ?S _ _ => apply next_refl
  end.
Hint Extern 3 => sys_next_reflexivity.

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

Definition sys_included {A} (S1 S2: sys A) :=
  forall x y, next S1 x y -> next S2 x y.

Lemma sys_union_included_left {A} (S1 S2: sys A) :
  sys_included S1 (sys_union S1 S2).
Proof.
intros x u H. left. trivial.
Qed.

Lemma sys_union_included_right {A} (S1 S2: sys A) :
  sys_included S2 (sys_union S1 S2).
Proof.
intros x y H. right. trivial.
Qed.

Fixpoint is_trace {A} (S: sys A) (l : list A) : Prop :=
match l with
| nil => False
| a :: nil => True
| a1 :: ((a2 :: _) as l2) => next S a1 a2 /\ is_trace S l2
end.

Hint Extern 3 (is_trace _ _) => compute; trivial.

Lemma is_trace_map_included {A} :
  forall (l: list A) (S1 S2: sys A),
    sys_included S1 S2 ->
    is_trace S1 l ->
    is_trace S2 l.
Proof.
intros l S1 S2 Hincl H. induction l.
* compute. trivial.
* destruct l as [|b l]; auto.
  destruct H as [Hab H]. split; auto.
Qed.

Lemma is_trace_tail {A} {S: sys A}:
  forall a1 a2 (l: list A),
    is_trace S (a1 :: a2 :: l) ->
    is_trace S (a2 :: l).
Proof.
intros a1 a2 l H.
simpl. simpl in H. destruct l. trivial. intuition.
Qed.

Lemma is_trace_app_inv_tail {A} {S: sys A}:
  forall a (l1 l2: list A),
    is_trace S (l1 ++ a :: l2) ->
    is_trace S (a :: l2).
Proof.
intros a l1. revert a. induction l1; intros a2 l2 H.
* assumption.
* rewrite <- app_comm_cons in H. destruct l1 as [|a1 l1].
  + destruct H. assumption.
  + rewrite <- app_comm_cons in H. destruct H as [Haa1 H].
    rewrite app_comm_cons in H. auto.
Qed.

Lemma is_trace_app_inv_head {A} {S: sys A}:
  forall a (l1 l2: list A),
    is_trace S (l1 ++ a :: l2) ->
    is_trace S (l1 ++ a :: nil).
Proof.
intros a l1. revert a. induction l1; intros a2 l2 H; auto.
rewrite <- app_comm_cons in H. destruct l1 as [|a1 l1].
+ destruct H. rewrite <- app_comm_cons. split; eauto.
+ rewrite <- app_comm_cons in H. destruct H as [Haa1 H].
  rewrite app_comm_cons in H.
  rewrite <- app_comm_cons. split; eauto.
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
* split; auto.
Qed.

Lemma is_trace_repeat {A} {S: sys A} :
  forall a n, is_trace S (a :: repeat a n).
Proof.
intros a n. induction n; simpl.
* trivial.
* split; auto.
Qed.


Lemma is_trace_repeat_remove_prefix {A} {S: sys A} :
  forall a b n (l: list A),
    is_trace S (repeat a n ++ b :: l) ->
    is_trace S (b :: l).
Proof.
intros a b n l H.
induction n.
* assumption.
* apply IHn; auto.
  unfold repeat in H. fold (repeat a n) in H.
  rewrite <- app_comm_cons in H. clear IHn.
  destruct n.
  + destruct H. assumption.
  + unfold repeat in H. fold (repeat a n) in H.
    rewrite <- app_comm_cons in H.
    destruct H.
    unfold repeat. fold (repeat a n).
    rewrite <- app_comm_cons.
    assumption.
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

Lemma is_trace_repeat_prefix {A} {S: sys A} :
  forall (t: trace S) a n,
    next S a (hd t) ->
    is_trace S (a :: repeat a n ++ proj1_sig t).
Proof.
intros t a n H. induction n.
* destruct t as [[| b l] Hl]; [destruct Hl |]. simpl. split.
  + assumption.
  + destruct l; trivial.
* destruct t as [[| b l] Hl]; [destruct Hl |].
  simpl proj1_sig in *. simpl in H.
  unfold repeat. fold (repeat a n). split; auto.
Qed.

Lemma is_trace_repeat_two {A} {S: sys A} :
  forall a b n m,
    next S a b ->
    is_trace S (a :: repeat a n ++ b :: repeat b m).
Proof.
intros a b n m H.
pose proof (@is_trace_repeat _ S b m) as Htrace.
pose (t := exist _ _ Htrace).
replace (b :: repeat b m) with (proj1_sig t) by reflexivity.
apply is_trace_repeat_prefix. assumption.
Qed.

Definition is_trace_from {A} {S: sys A} (tr: trace S) (s : A) : Prop :=
  hd tr = s.

Ltac is_trace_from_reflexivity :=
  match goal with
    | |- is_trace_from _ _ => reflexivity
  end.
Hint Extern 3 => is_trace_from_reflexivity.

Definition trace_cons {A} {S: sys A}
           (s : A) (t : trace S) (H: next S s (hd t)) : trace S.
Proof.
destruct t as [l Hl].
assert (is_trace S (s :: l)) as Htrace.
{ destruct l as [| s' l].
  + destruct Hl.
  + split. exact H. exact Hl. }
exact (exist _ _ Htrace).
Defined.

Lemma trace_cons_is_trace_from {A} {S: sys A}:
  forall (s : A) (t : trace S) (H: next S s (hd t)),
    is_trace_from (trace_cons s t H) s.
Proof.
intros s t H.
destruct t as [[| a l] Hl]; auto.
Qed.

Lemma is_trace_app {A} {S: sys A}:
  forall a1 a2 (l1 l2: list A),
    is_trace S (l1 ++ a1 :: nil) ->
    next S a1 a2 ->
    is_trace S (a2 :: l2) ->
    is_trace S (l1 ++ a1 :: a2 :: l2).
Proof.
intros a1 a2 l1. revert a1 a2.
induction l1; intros a1 a2 l2 H1 Hnext H2.
* split; trivial.
* rewrite <- app_comm_cons in H1. destruct l1 as [| a1' l1].
  + destruct H1 as [Haa1 _]. deep_splits; trivial.
  + rewrite <- app_comm_cons in H1. destruct H1 as [Haa1' H1].
    rewrite <- app_comm_cons. rewrite <- app_comm_cons. split; trivial.
    apply IHl1; trivial.
Qed.

Lemma is_trace_app' {A} {S: sys A}:
  forall a (l1 l2: list A),
    is_trace S (l1 ++ a :: nil) ->
    is_trace S (a :: l2) ->
    is_trace S (l1 ++ a :: l2).
Proof.
intros a l1 l2 H1 H2. destruct l2 as [|a2 l2].
* assumption.
* destruct H2 as [Haa2 H2].
apply is_trace_app; trivial.
Qed.

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
* intros [? ?]. auto.
* intros [? ?] [? ?] ?. simpl in *. symmetry. assumption.
* intros [? ?] [? ?] [? ?] ? ?. simpl in *. etransitivity; eassumption.
Defined.

Definition set_included {A} (R: relation A) (S1 S2: A -> Prop) :=
  forall s1, S1 s1 -> exists s2, S2 s2 /\ R s1 s2.

Definition set_equiv {A} (R: relation A) (S1 S2: A -> Prop) :=
  set_included R S1 S2 /\ set_included R S2 S1.

Require Import RelationClasses.
Instance set_included_PreOrder {A} {R: relation A} `{Equivalence A R}:
  PreOrder (set_included R).
Proof.
constructor.
* intros X x Hx; exists x; split; auto.
* intros X Y Z HXY HYZ x Hx.
  destruct (HXY x Hx) as [y [Hy Hxy]].
  destruct (HYZ y Hy) as [z [Hz Hyz]].
  exists z. split. assumption. transitivity y; assumption.
Qed.

Instance set_equiv_Equivalence {A} {R: relation A} `{Equivalence A R}:
  Equivalence (set_equiv R).
Proof.
constructor.
* intro X; split; reflexivity.
* intros X Y [HXY HYX]; split; intros ? ?; auto.
* intros X Y Z [HXY HYX] [HYZ HZY]; split;
  transitivity Y; auto.
Qed.

Definition stutter {A} {S: sys A} (t1 t2: trace S) : Prop :=
  lift_trace stutter_equiv t1 t2.

Hint Extern 3 (stutter _ _) => compute; reflexivity.

Lemma stutter_stutter_equiv {A} {S: sys A}:
  forall (t1 t2: trace S),
    stutter t1 t2 -> stutter_equiv (proj1_sig t1) (proj1_sig t2).
Proof.
intros t1 t2 H. assumption.
Qed.

Ltac simpl_stutter_ctx :=
  match goal with
    | H: stutter _ _ |- _ =>
      apply stutter_stutter_equiv in H;
      simpl proj1_sig in H;
      simpl_stutter_ctx
    | _ => idtac
  end.

Ltac simpl_stutter := unfold stutter; unfold lift_trace; simpl proj1_sig.

Lemma stutter_repeat {A} {S: sys A} :
  forall (a: A) n,
    stutter (trace_one S a) (exist _ _ (is_trace_repeat a n)).
Proof.
intros a n. apply stutter_equiv_repeat.
Qed.

Lemma set_included_subrel {A} :
  forall (R1 R2: relation A) (E E': A -> Prop),
    (forall x y, R1 x y -> R2 x y) ->
    set_included R1 E E' ->
    set_included R2 E E'.
Proof.
intros R1 R2 E E' H H1.
intros x Hx.
destruct (H1 x Hx) as [y [Hy Hxy]].
exists y. split; auto.
Qed.

Lemma set_equiv_subrel {A} :
  forall (R1 R2: relation A) (E E': A -> Prop),
    (forall x y, R1 x y -> R2 x y) ->
    set_equiv R1 E E' ->
    set_equiv R2 E E'.
Proof.
intros R1 R2 E E' H [H1 H1'].
split; eapply set_included_subrel; eauto.
Qed.

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

Definition view {A} {S: sys A} (R: relation A) (t1 t2: trace S) :=
  lift_trace (same_view R) t1 t2.

Hint Extern 3 (view _ _ _) => compute; reflexivity.

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
- exists (trace_one S a). split; auto.
  destruct Hs. split; trivial.
  transitivity s1. symmetry; assumption. assumption.
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
    view R t1 t2 ->
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
exists (exist _ _ Hal). deep_splits.
* intuition eauto.
* transitivity l1. symmetry; trivial. trivial.
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

Lemma view_stutter {A} {S: sys A} {R: relation A} {E: Equivalence R}:
  forall (t1 t2: trace S),
    stutter t1 t2 ->
    exists t0,
      stutter t1 t0 /\
      view R t0 t2.
Proof.
intros [t1 H1] [t2 H2] H.
destruct (view_stutter_aux _ _ H) as [t0 [Ht1t0 Ht0t2]].
exists (exist _ _ (is_trace_stutter _ _ H1 Ht1t0)).
split; assumption.
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
    View.same_view
      R
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

Lemma exploit_set_included_stutter_view {A} {S: sys A}
      {R: relation A} {E: Equivalence R}:
  forall (t1 t2: trace S),
    set_included stutter (View.view R t1) (View.view R t2) ->
    exists t0 : trace S, View.view R t2 t0 /\ stutter t1 t0.
Proof.
intros t1 t2 H.
apply H. reflexivity.
Qed.

Lemma exploit_set_equiv_stutter_view {A} {S: sys A}
      {R: relation A} {E: Equivalence R}:
  forall (t1 t2: trace S),
    set_equiv stutter (View.view R t1) (View.view R t2) ->
    exists t0 : trace S, View.view R t2 t0 /\ stutter t1 t0.
Proof.
intros t1 t2 [H _].
apply exploit_set_included_stutter_view. trivial.
Qed.

Lemma included_view_R {A} {S: sys A} (R: relation A) {E: Equivalence R}:
  forall (t1 t2: trace S),
    set_included stutter (View.view R t1) (View.view R t2) ->
    forall s1,
      In s1 (proj1_sig t1) ->
      exists s2, In s2 (proj1_sig t2) /\ R s1 s2.
Proof.
intros t1 t2 Ht1t2 s1 Hs1t1.
specialize (Ht1t2 t1).
destruct Ht1t2 as [t2' [Ht2t2' Ht1t2']]. reflexivity.
destruct t2 as [l2 Hl2]. destruct t2' as [l2' Hl2'].
unfold view in Ht2t2'. unfold lift_trace in Ht2t2'. simpl in *.
apply (View.same_view_in _ l2').
apply (stutter_equiv_in _ _ Ht1t2' s1 Hs1t1).
symmetry. assumption.
Qed.

Lemma set_included_view_same {A} {R: relation A} {E: Equivalence R}:
  forall a (l1 l2: list A),
    set_included stutter_equiv
                 (same_view R l1) (same_view R l2) ->
    set_included stutter_equiv
                 (same_view R (a :: l1)) (same_view R (a :: l2)).
Proof.
intros a l1 l2 H l Hl.
destruct l as [| a0  l0]; [destruct Hl |].
destruct Hl as [Haa0 Hl1l0].
specialize (H l0 Hl1l0).
destruct H as [l0' [Hl2l0' Hl0l0']].
exists (a0 :: l0'). deep_splits; auto.
Qed.

Lemma set_equiv_view_same {A} {R: relation A} {E: Equivalence R}:
  forall a (l1 l2: list A),
    set_equiv stutter_equiv
              (same_view R l1) (same_view R l2) ->
    set_equiv stutter_equiv
              (same_view R (a :: l1)) (same_view R (a :: l2)).
Proof.
intros a l1 l2 [H H'].
split; apply set_included_view_same; trivial.
Qed.

Lemma set_included_view_cons_right_add_right
      {A} {R: relation A} {E: Equivalence R}:
  forall a (l1 l2: list A),
    set_included stutter_equiv
                 (same_view R l1) (same_view R (a :: l2)) ->
    set_included stutter_equiv
                 (same_view R l1) (same_view R (a :: a :: l2)).
Proof.
intros a l1 l2 H l Hl.
specialize (H l Hl).
destruct H as [l0 [Hl2l0 Hll0]].
destruct l0 as [| a0 l0]; [destruct Hl2l0 |].
destruct Hl2l0 as [Haa0 Hl2l0].
destruct (stutter_equiv_cons_right_inv _ _ _ Hll0) as [l' ?].
subst l.
destruct l1 as [| a1 l1]; [destruct Hl |].
destruct Hl as [Ha1a0 Hl1l'].
exists (a0 :: a0 :: l0). deep_splits; auto.
Qed.

Lemma set_included_view_cons_left_add_right
      {A} {R: relation A} {E: Equivalence R}:
  forall a (l1 l2: list A),
    set_included stutter_equiv
                 (same_view R (a :: l1)) (same_view R l2) ->
    set_included stutter_equiv
                 (same_view R (a :: l1)) (same_view R (a :: l2)).
Proof.
intros a1 l1 l2 H l Hl.
destruct l as [| a l]; [destruct Hl |].
specialize (H (a :: l) Hl).
destruct H as [l0 [Hl2l0 Hll0]].
destruct Hl as [Ha1a Hl1l].
exists (a :: l0). deep_splits; trivial.
apply stutter_equiv_cons_left_add_right. trivial.
Qed.

Lemma view_set_included_view {A} {R: relation A} {E: Equivalence R} :
  forall (l1 l2: list A),
    same_view R l1 l2 ->
    set_included stutter_equiv (same_view R l1) (same_view R l2).
Proof.
intro l1; induction l1; intros l2 H l Hl.
* destruct l2; [| destruct H].
  destruct l; [| destruct Hl].
  exists nil. split; reflexivity.
* rename a into a1.
  destruct l2 as [| a2 l2]; [destruct H|].
  destruct H as [Ha1a2 Hl1l2].
  destruct l as [| a l]; [destruct Hl |].
  destruct Hl as [Ha1a Hl1l].
  specialize (IHl1 l2 Hl1l2 l Hl1l).
  destruct IHl1 as [l0 [Hl2l0 Hll0]].
  exists (a :: l0). deep_splits; auto.
  { transitivity a1. symmetry. trivial. trivial. }
Qed.

Lemma view_set_equiv_view {A} {R: relation A} {E: Equivalence R} :
  forall (l1 l2: list A),
    same_view R l1 l2 ->
    set_equiv stutter_equiv (same_view R l1) (same_view R l2).
Proof.
intros l1 l2 H. split; apply view_set_included_view.
trivial. symmetry; trivial.
Qed.

Lemma view_subrel {A} {S: sys A}
      (R1: relation A) {E1: Equivalence R1}
      (R2: relation A) {E2: Equivalence R2} :
  (forall x y, R1 x y -> R2 x y) ->
  forall t t': trace S,
    view R1 t t' ->
    view R2 t t'.
Proof.
intros H12 t t' H1.
destruct t as [l Hl]. destruct t' as [l' Hl'].
unfold view in *. unfold lift_trace in *. simpl in *.
clear Hl Hl'.
generalize dependent l'. induction l; intros l' H1.
* destruct l'; [| destruct H1]. auto.
* destruct l' as [| a' l']; [destruct H1 |].
  destruct H1 as [Haa' Hll'].
  split; auto.
Qed.

Lemma set_equiv_view_equiv_rel {A} (S: sys A)
  (R1: relation A) {E1: Equivalence R1}
  (R2: relation A) {E2: Equivalence R2}:
  forall t t' : trace S,
  (forall x y, R1 x y <-> R2 x y) ->
  set_equiv stutter (View.view R1 t) (View.view R1 t') ->
  set_equiv stutter (View.view R2 t) (View.view R2 t').
Proof.
intros t t' H H1.
assert (forall x y, R1 x y -> R2 x y) as H12 by firstorder.
assert (forall x y, R2 x y -> R1 x y) as H21 by firstorder.
clear H. split.
* intros t0 Htt0.
  destruct H1 as [H1 _].
  apply (view_subrel R2 R1) in Htt0; trivial.
  specialize (H1 t0 Htt0).
  destruct H1 as [t1 [Ht't1 Htt1]].
  exists t1. split.
  + apply (view_subrel R1 R2); trivial.
  + trivial.
* intros t0 Htt0.
  destruct H1 as [_ H1].
  apply (view_subrel R2 R1) in Htt0; trivial.
  specialize (H1 t0 Htt0).
  destruct H1 as [t1 [Ht't1 Htt1]].
  exists t1. split.
  + apply (view_subrel R1 R2); trivial.
  + trivial.
Qed.

Lemma same_view_repeats_inv {A} (R: relation A) {E: Equivalence R}:
  forall n1 n2 x y (l: list A),
    View.same_view R l (x :: repeat x n1 ++ y :: repeat y n2) ->
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

End View.

(* Observations *)
Definition obs_from {A} (s : A) (S: sys A) (R: relation A)
: (trace S -> Prop) -> Prop :=
  fun tView =>
    exists (t : trace S), tView = View.view R t /\ is_trace_from t s.

Lemma exploit_obs_included {A} {S: sys A}
      {R: relation A} {E: Equivalence R}:
  forall (t : trace S) s1 s2,
    set_included (set_equiv stutter) (obs_from s1 S R) (obs_from s2 S R) ->
    is_trace_from t s1 ->
    exists t1 t2,
      is_trace_from t2 s2
      /\ View.view R t2 t1
      /\ stutter t t1.
Proof.
intros t s1 s2 H Ht.
specialize (H (View.view R t)).
destruct H as [v [[t' [Hv Ht's2]] Htt']].
exists t. split; trivial.
subst v.
apply View.exploit_set_equiv_stutter_view in Htt'.
destruct Htt' as [t0 [Ht't0 Htt0]].
eauto.
Qed.

Lemma exploit_obs_included_one {A} {S: sys A}
      {R: relation A} {E: Equivalence R}:
  forall s1 s2,
    set_included (set_equiv stutter) (obs_from s1 S R) (obs_from s2 S R) ->
      exists t1 t2,
        is_trace_from t2 s2
        /\ View.view R t2 t1
        /\ stutter (trace_one S s1) t1.
Proof.
intros s1 s2 H.
apply (exploit_obs_included _ s1); auto.
Qed.

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
Qed.

Lemma obs_from_self {A} {S: sys A} (R: relation A) {E: Equivalence R}:
  forall s (t: trace S),
    is_trace_from t s ->
    obs_from s S R (View.view R t).
Proof.
intros s [l Hl] H.
destruct l as [| s' l'].
* inversion Hl.
* compute in H. subst.
  exists (exist _ _ Hl). split; auto.
Qed.

Lemma exploit_obs_eq {A} {S: sys A}
      {R: relation A} {E: Equivalence R}:
  forall (t : trace S) s1 s2,
    obs_eq S R s1 s2 ->
    is_trace_from t s1 ->
    exists t1 t2,
      is_trace_from t2 s2
      /\ View.view R t2 t1
      /\ stutter t t1.
Proof.
intros t s1 s2 [H _] Ht.
apply (exploit_obs_included _ s1); trivial.
Qed.

Lemma exploit_obs_eq_one {A} {S: sys A}
      {R: relation A} {E: Equivalence R}:
  forall s1 s2,
    obs_eq S R s1 s2 ->
      exists t1 t2,
        is_trace_from t2 s2
        /\ View.view R t2 t1
        /\ stutter (trace_one S s1) t1.
Proof.
intros s1 s2 H.
apply (exploit_obs_eq _ s1). trivial. reflexivity.
Qed.

Require Import ERLattice.

Lemma view_compat_ER_equiv {A} (S: sys A):
  forall (R1 R2: relation A) (E1: Equivalence R1) (E2: Equivalence R2)
         (t t': trace S),
    View.view R1 t t' ->
    equiv (toER R1) (toER R2) ->
    View.view R2 t t'.
Proof.
intros R1 R2 E1 E2 t t' HR1 Heq.
destruct t as [l Hl]. destruct t' as [l' Hl'].
generalize dependent l'. induction l; intros l' Hl' HR1.
* destruct Hl.
* destruct l as [| b l].
  + destruct l' as [| a' l']; [destruct Hl' |]. destruct l' as [| b' l'].
    - compute in HR1. split; auto.
      destruct Heq as [H12 H21]. apply H21. compute. tauto.
    - destruct HR1 as [_ H]. destruct H.
  + destruct l' as [| a' l']; [destruct Hl' |]. destruct l' as [| b' l'].
    - compute in HR1. exfalso. tauto.
    - destruct HR1 as [Haa' H].
      { split.
        * destruct Heq as [H12 H21]. apply H21. assumption.
        * destruct Hl as [Hab Hl]. destruct Hl' as [Ha'b' Hl'].
          apply (IHl Hl _ Hl' H).
      }
Qed.

Lemma obs_from_compat_ER_included {A} (S: sys A):
  forall (R1 R2: relation A) (E1: Equivalence R1) (E2: Equivalence R2) s,
    equiv (toER R1) (toER R2) ->
    set_included (set_equiv eq) (obs_from s S R1) (obs_from s S R2).
Proof.
intros R1 R2 E1 E2 s Heq.
intros v [t [Hv Hts]]. subst v.
exists (View.view R2 t). deep_splits.
+ exists t. split; trivial.
+ intros t0 Htt0. exists t0. split; trivial.
  apply (view_compat_ER_equiv S R1 R2 E1 E2); auto.
+ intros t0 Htt0. exists t0. split; trivial.
  apply (view_compat_ER_equiv S R2 R1 E2 E1). trivial. symmetry; trivial.
Qed.

Lemma obs_from_compat_ER_equiv {A} (S: sys A):
  forall (R1 R2: relation A) (E1: Equivalence R1) (E2: Equivalence R2) s,
    equiv (toER R1) (toER R2) ->
    set_equiv (set_equiv eq) (obs_from s S R1) (obs_from s S R2).
Proof.
intros R1 R2 E1 E2 s Heq.
split; eapply obs_from_compat_ER_included; eauto.
symmetry; trivial.
Qed.

Lemma obs_eq_compat_ER_equiv {A} (S: sys A):
  forall (R1 R2: relation A) (E1: Equivalence R1) (E2: Equivalence R2) s s',
    obs_eq S R1 s s' ->
    equiv (toER R1) (toER R2) ->
    obs_eq S R2 s s'.
Proof.
intros R1 R2 E1 E2 s s' HR1 Heq.
assert (forall x y : trace S -> Prop,
          set_equiv eq x y -> set_equiv stutter x y) as Haux.
{ intros x y Hxy. apply (set_equiv_subrel eq stutter); trivial.
  clear. intros x y H. subst. reflexivity. }
split.
* transitivity (obs_from s S R1).
  + apply (set_included_subrel (set_equiv eq) (set_equiv stutter)); trivial.
    eapply obs_from_compat_ER_included; eauto. symmetry; trivial.
  + transitivity (obs_from s' S R1).
    - destruct HR1. assumption.
    - apply (set_included_subrel (set_equiv eq) (set_equiv stutter)); trivial.
      eapply obs_from_compat_ER_included; eauto.
* symmetry in Heq. symmetry in HR1. transitivity (obs_from s' S R1).
  + apply (set_included_subrel (set_equiv eq) (set_equiv stutter)); trivial.
    eapply obs_from_compat_ER_included; eauto.
  + transitivity (obs_from s S R1).
    - destruct HR1. assumption.
    - apply (set_included_subrel (set_equiv eq) (set_equiv stutter)); trivial.
      eapply obs_from_compat_ER_included; eauto. symmetry; trivial.
Qed.

(* The security property *)
Definition SP {A} (S: sys A) (R: relation A) {E: Equivalence R} :=
  leq (toER (obs_eq S R)) (toER R).

Lemma SP_compat_ER_equiv {A} (S: sys A):
  forall (R1 R2: relation A) (E1: Equivalence R1) (E2: Equivalence R2),
    SP S R1 ->
    equiv (toER R1) (toER R2) ->
    SP S R2.
Proof.
intros R1 R2 E1 E2 HSP Heq.
intros s1 s2 HR2.
simpl. eapply (obs_eq_compat_ER_equiv _ R1 R2); eauto.
apply HSP. destruct Heq. auto.
Qed.

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

Lemma obs_eq_R {A} {S: sys A} {R: relation A} {E: Equivalence R}:
  forall s s' : A,
    obs_eq S R s s' ->
    R s s'.
Proof.
intros s1 s2 H12.
apply exploit_obs_eq_one in H12.
destruct H12 as [t1 [t2 [Ht2s2 [Ht2t1 Hs1t1]]]].
destruct t2 as [[| s l2] Hl2]; [destruct Hl2 |].
compute in Ht2s2. subst s.
destruct (stutter_equiv_cons_left_inv _ _ _ Hs1t1) as [l' ?].
destruct t1 as [l1 ?]. simpl in H. subst.
destruct Ht2t1. symmetry. assumption.
Qed.

Lemma prop_2_1 {A} (S: sys A) (R: relation A) {E: Equivalence R} :
  leq (toER R) (toER (obs_eq S R)).
Proof.
exact (@obs_eq_R A S R E).
Qed.

Lemma corollary_2_1 {A} (S: sys A) (R: relation A) {E: Equivalence R} :
  SP S R -> equiv (toER R) (toER (obs_eq S R)).
Proof.
intros H. split.
apply prop_2_1. assumption.
Qed.

(* Auxiliary lemmas for SP_bottom *)
Module SP_bottom_aux.

Lemma view_bottom {A} :
  forall (l1 l2: list A),
    View.same_view (er_bottom_rel A) l1 l2 <-> length l1 = length l2.
Proof.
intros l1 l2.
rewrite View.same_view_characterization. split.
* intros [? _]; assumption.
* intros H. split; trivial.
  intros a n H1 H2. compute. trivial.
Qed.

Lemma view_bottom_trace {A} {S: sys A} :
  forall (t1 t2: trace S),
    View.view (er_bottom_rel A) t1 t2
    <-> length (proj1_sig t1) = length (proj1_sig t2).
Proof.
intros [l1 Hl1] [l2 Hl2].
apply view_bottom.
Qed.

Lemma replicate_trace_bottom {A} {S: sys A} :
  forall a (t: trace S),
    exists (t': trace S),
      is_trace_from t' a
      /\ View.view (er_bottom_rel A) t t'
      /\ stutter (trace_one S a) t'.
Proof.
intros a t.
exists (exist _ _ (is_trace_repeat a (length (proj1_sig t) - 1))).
splits.
* reflexivity.
* rewrite view_bottom_trace. simpl. rewrite repeat_length.
  destruct t as [[| b l] Hl]; [destruct Hl |]. auto.
* apply stutter_repeat.
Qed.

Lemma set_included_obs_from_bottom {A} {S: sys A}:
  forall s1 s2,
    set_included (set_equiv stutter)
                 (obs_from s1 S (er_bottom_rel A))
                 (obs_from s2 S (er_bottom_rel A)).
Proof.
intros s1 s2 v Hv.
destruct Hv as [t [Hv Hts1]]. subst v.
destruct (replicate_trace_bottom s2 t) as [t' [Ht's2 [Htt' Ht']]].
exists (View.view (er_bottom_rel A) t'). deep_splits.
* apply obs_from_self; auto.
* intros t0 Htt0. exists t0. split.
  + transitivity t. symmetry; assumption. assumption.
  + reflexivity.
* intros t0 Ht't0. exists t0. split.
  + transitivity t'. assumption. assumption.
  + reflexivity.
Qed.

Lemma obs_eq_bottom {A} {S: sys A}:
  forall s1 s2,
    obs_eq S (er_bottom_rel A) s1 s2.
Proof.
intros s1 s2. split; auto using set_included_obs_from_bottom.
Qed.

End SP_bottom_aux.

Lemma SP_bottom {A} (S: sys A) :
  SP S (er_bottom_rel A).
Proof.
intros s1 s2 H. apply SP_bottom_aux.obs_eq_bottom.
Qed.

Lemma SP_top {A} (S: sys A) :
  SP S (proj1_sig (er_top A)).
Proof.
intros s1 s2 H. rewrite H.
reflexivity.
Qed.

(* TODO: Declassification set D, at the end of section 2.3 *)

Module Example1. (* Section 3 *)

Require Import Bool.

Record state :=
{ time : bool
; high : bool
; password : bool
; query : bool
; result : bool
}.

Lemma eq_state_dec : forall (s1 s2: state), {s1 = s2} + {s1 <> s2}.
Proof.
intros [t1 h1 p1 q1 r1] [t2 h2 p2 q2 r2].
destruct (bool_dec t1 t2); [| right; congruence].
destruct (bool_dec h1 h2); [| right; congruence].
destruct (bool_dec p1 p2); [| right; congruence].
destruct (bool_dec q1 q2); [| right; congruence].
destruct (bool_dec r1 r2); [| right; congruence].
left. congruence.
Defined.

(* The step function of the system *)
Definition step (s: state) : state :=
if time s
then s
else
{| time := true;
   high := high s;
   password := password s;
   query := query s;
   result := if bool_dec (password s) (query s)
            then negb (result s)
            else result s
|}.

(* The relation that describes the execution of the system. *)
Definition exec : relation state :=
  fun s1 s2 => s2 = s1 \/ s2 = step s1.

Lemma exec_refl : forall s, exec s s.
Proof.
intro s. left. reflexivity.
Qed.

Definition password_checker : sys state :=
  {| next := exec; next_refl := exec_refl |}.

(* The observation that the observer is interested in. *)
Definition R : relation state :=
  fun s s' =>
    time s = time s' /\ query s = query s' /\ result s = result s'.

Instance R_Equivalence : Equivalence R.
Proof.
unfold R. constructor.
* intro s. intuition.
* intros s1 s2 H. intuition.
* intros s1 s2 s3 H12 H23. simpl in *. intuition; eauto.
Qed.
Hint Resolve R_Equivalence.

(* For the following lemma, it is crucial that password and query
   are booleans. *)
Lemma time_false_R_step_password :
  forall s1 s2 : state,
    time s1 = false ->
    R s1 s2 ->
    R (step s1) (step s2) ->
    password s1 = password s2.
Proof.
intros s1 s2 Hfalse H H'.
destruct H as [Ht [Hq Hr]].
unfold step in H'.
rewrite <- Ht in H'. clear Ht.
rewrite <- Hq in H'. clear Hq.
rewrite <- Hr in H'. clear Hr.
rewrite Hfalse in H'. clear Hfalse.
destruct H' as [Ht [Hq Hr]]. simpl in *.
clear Ht Hq.
destruct (bool_dec (password s1) (query s1));
  destruct (bool_dec (password s2) (query s1)).
* congruence.
* exfalso. destruct (result s1); simpl in Hr; congruence.
* exfalso. destruct (result s1); simpl in Hr; congruence.
* destruct (query s1); destruct (password s1);
  destruct (password s2); congruence.
Qed.

Lemma step_time_false_neq :
  forall s,
    time s = false ->
    s <> step s.
Proof.
intros s H. unfold step.
destruct s as [t h p q r]. simpl in *.
subst t.
congruence.
Qed.

Lemma step_time_true_eq :
  forall s,
    time s = true ->
    s = step s.
Proof.
intros s H. unfold step.
destruct s as [t h p q r]. simpl in *.
subst t.
reflexivity.
Qed.

Lemma R_step_time_false :
  forall s s',
    R s s' ->
    time s = false ->
    (time s = false -> password s = password s') ->
    R (step s) (step s').
Proof.
intros s s' HR Hfalse Hpassword.
destruct s  as [t  h  p  q  r].
destruct s' as [t' h' p' q' r'].
unfold step in *. simpl in *.
subst t.
destruct HR as [Htime [Hquery Hresult]].
simpl in *.
rewrite <- Htime.
deep_splits; trivial.
specialize (Hpassword eq_refl). subst. reflexivity.
Qed.

Lemma time_false_not_R_step :
  forall s,
    time s = false ->
    ~ R s (step s).
Proof.
intros s Hfalse HR.
unfold step in *. rewrite Hfalse in HR.
destruct s as [t h p q r].
destruct HR as [Ht [Hq Hr]].
simpl in *.
congruence.
Qed.

Lemma step_projection :
  forall s, step s = step (step s).
Proof.
intros [t h p q r].
destruct t; unfold step; simpl.
+ reflexivity.
+ f_equal.
Qed.

Definition trace_step (s : state) : trace password_checker.
Proof.
refine (trace_cons s (trace_one password_checker (step s)) _).
* right. reflexivity.
Defined.

Lemma stutter_password_checker :
  forall t : trace password_checker,
    stutter t (trace_one password_checker (hd t))
    \/ stutter t (trace_step (hd t)).
Proof.
intros [l Hl]. induction l.
* destruct Hl.
* destruct l as [| b l].
  - clear IHl. simpl_stutter. auto.
  - simpl. destruct Hl as [Hab Hbl].
    specialize (IHl Hbl). destruct IHl as [IHl | IHl].
    + { simpl in IHl. destruct Hab as [Hab | Hab]; subst b.
        * left. apply stutter_left. assumption.
        * right. apply stutter_same. assumption.
      }
    + { simpl in IHl. destruct Hab as [Hab | Hab]; subst b.
        * right. apply stutter_left. assumption.
        * right. apply stutter_same.
          transitivity (step a :: step (step a) :: nil).
          + assumption.
          + rewrite <- step_projection.
            apply stutter_left. reflexivity.
      }
Qed.

Lemma time_false_obs_password :
  forall s s': state,
    obs_eq password_checker R s s' ->
    time s = false ->
    R s s' ->
    password s = password s'.
Proof.
intros s s' Hobs Hfalse HR.
apply time_false_R_step_password; trivial.
destruct s  as [t  h  p  q  r].
destruct s' as [t' h' p' q' r'].
destruct HR as [Htime [Hquery Hresult]].
simpl in *. subst.
rewrite <- Htime in *. clear Htime. unfold step. simpl.
deep_splits.
simpl. destruct (bool_dec p p').
* subst. reflexivity.
* exfalso. apply n. clear n.
  pose (s := {|
              time := false;
              high := h;
              password := p;
              query := q';
              result := r' |}). fold s in Hobs.
  pose (s' := {|
               time := false;
               high := h';
               password := p';
               query := q';
               result := r' |}). fold s' in Hobs.
  destruct Hobs as [Hss' Hs's].
  assert (is_trace password_checker (s :: step s :: nil)) as Htrace.
  { split; auto. right; reflexivity. }
  pose (t := exist _ _ Htrace).
  specialize (Hss' (View.view R t)).
  destruct Hss' as [v' [[t0' [Hv' Ht0's']] Htt0']].
  { exists t. split; reflexivity. }
  subst v'.
  assert (In (step s') (proj1_sig t0')).
  { destruct (stutter_password_checker t0') as [H | H].
    * exfalso.
      eapply (time_false_not_R_step s); trivial.
      assert (forall a, In a (proj1_sig t) -> R a (hd t0')) as Haux.
      { intros a Ha.
        destruct Htt0' as [Htt0' _].
        destruct (View.included_view_R _ _ _ Htt0' a Ha) as [a' [Ha' Haa']].
        transitivity a'; trivial.
        pose proof (stutter_equiv_in _ _ H a' Ha') as H0.
        destruct H0.
        + rewrite H0. reflexivity.
        + destruct H0.
      }
      transitivity (hd t0').
      + apply Haux. unfold t. simpl. eauto.
      + symmetry. apply Haux. unfold t. simpl. eauto.
    * destruct t0' as [[| a0 l0] Hl0]; [destruct Hl0 |].
      simpl in H. simpl proj1_sig. compute in Ht0's'. fold s' in Ht0's'.
      subst.
      apply (stutter_equiv_in (proj1_sig (trace_step s'))).
      + symmetry. assumption.
      + right. simpl. eauto.
  }
  assert (R (step s') s \/ R (step s') (step s)) as [? | ?].
  { destruct Htt0' as [Htt0' Ht0't].
    destruct (View.included_view_R _ _ _ Ht0't _ H) as [s1 [Hs1 Hs's1]].
    destruct Hs1.
    + subst s1. eauto.
    + destruct H0.
      - subst s1. eauto.
      - destruct H0.
  }
  + destruct H0 as [H0 _].
    unfold s' in H0; unfold step in H0; simpl in H0. congruence.
  + destruct H0 as [_ [ _ H0]].
    unfold s' in H0; unfold step in H0; simpl in H0.
    destruct (bool_dec p' q'); destruct (bool_dec p q').
    - congruence.
    - destruct r'; simpl in H0; congruence.
    - destruct r'; simpl in H0; congruence.
    - destruct p; destruct p'; destruct q'; try congruence.
Qed.

Lemma stutter_one_stutter_view {A} {S: sys A} {R: relation A} {E: Equivalence R}:
  forall (s s' : A) (l : list A),
    R s s' ->
    forall (Hl: is_trace S (s :: l)),
    stutter (exist _ (s :: l) Hl) (trace_one S s) ->
    exists s2 : trace S -> Prop,
      obs_from s' S R s2 /\
      set_equiv stutter (View.view R (exist _ (s :: l) Hl)) s2.
Proof.
intros s s' l HR Hl Hstutter.
pose (t' := exist _ _
            (@is_trace_repeat _ S s' (length l))).
exists (View.view R t'). split.
* exists t'. split; reflexivity.
* assert (stutter (trace_one S s') t')
    by apply stutter_repeat.
  split.
  - intros t0 Htt0. exists t0. split.
    + transitivity (exist _ _ Hl); try assumption.
      symmetry. unfold t'.
      unfold View.view. unfold lift_trace. simpl proj1_sig.
      apply (View.repeat_same_view R s s'); trivial.
    + reflexivity.
  - intros t0 Htt0. exists t0. split.
    + transitivity t'; try assumption.
      unfold t'.
      unfold View.view. unfold lift_trace. simpl proj1_sig.
      apply (View.repeat_same_view R s s'); trivial.
    + reflexivity.
Qed.

Lemma R_included_obs:
  forall (s s': state),
    R s s' ->
    R (step s) (step s') ->
    set_included (set_equiv stutter)
                 (obs_from s password_checker R)
                 (obs_from s' password_checker R).
Proof.
intros s s' HR HR'.
intros v [t [Hv Hts]]. subst v.
destruct (stutter_password_checker t) as [H | H].
- destruct t as [[| a l] Hl]; [destruct Hl |].
  compute in Hts. subst a. simpl_stutter_ctx.
  apply stutter_one_stutter_view; trivial.
- destruct t as [[| a l] Hl]; [destruct Hl |].
  compute in Hts. subst a. simpl_stutter_ctx.
  { case_eq (time s); intro Htime'.
    * pose proof (step_time_true_eq _ Htime') as Hstep.
      rewrite <- Hstep in H. clear Hstep.
      assert (stutter_equiv (s :: l) (s :: nil)) as H'.
      { transitivity (s :: s :: nil). assumption. auto. }
      clear H. apply stutter_one_stutter_view; trivial.
    * pose proof (step_time_false_neq _ Htime') as Hstep.
      destruct (stutter_two_inv _ _ _ Hstep H) as [n1 [n2 Heq]].
      clear Hstep.
      pose (l' :=
              s' :: repeat s' n1
              ++ step s' :: repeat (step s') n2).
      assert (is_trace password_checker l') as Htrace'.
      { apply is_trace_repeat_two. right; reflexivity. }
      pose (t' := exist _ _ Htrace').
      exists (View.view R t'). split.
      + exists t'. split; reflexivity.
      + split.
        - intros t0 Ht0. exists t0.
          { split.
            * transitivity (exist _ _ Hl); trivial.
              symmetry.
              unfold t'. unfold View.view. unfold lift_trace. simpl.
              split; trivial.
              inversion Heq; subst.
              apply View.repeat_two_same_view; trivial.
            * reflexivity.
          }
        - intros t0 Ht0. exists t0.
          { split.
            * transitivity t'; trivial.
              unfold t'. unfold View.view. unfold lift_trace. simpl.
              split; trivial.
              inversion Heq; subst.
              apply View.repeat_two_same_view; trivial.
            * reflexivity.
          }
  }
Qed.

Lemma R_time_included_obs:
  forall (s s': state),
    R s s' ->
    (time s = false -> password s = password s') ->
    set_included (set_equiv stutter)
                 (obs_from s password_checker R)
                 (obs_from s' password_checker R).
Proof.
intros s s' HR Htime.
apply R_included_obs; trivial.
case_eq (time s); intro H.
* repeat rewrite <- step_time_true_eq; trivial.
  destruct HR as [Ht _]. congruence.
* apply R_step_time_false; trivial.
Qed.

Lemma obs_eq_iff :
  forall s s',
    obs_eq password_checker R s s'
    <->
    (time s = time s' /\ query s = query s' /\ result s = result s'
     /\ (time s = false -> password s = password s')).
Proof.
intros s s'. split.
* intro Hobs_eq.
  cut (R s s' /\ (R s s' -> time s = false -> password s = password s')).
  + intros [? ?]. unfold R in *. intuition.
  + split.
    - apply (obs_eq_R _ _ Hobs_eq).
    - intros Hr Hfalse. apply time_false_obs_password; auto.
* intro H.
  assert (R s s' /\ (time s = false -> password s = password s'))
    as [HR Htime]. { unfold R. intuition. }
  clear H. split.
  + apply R_time_included_obs; trivial.
  + apply R_time_included_obs; trivial.
    - symmetry. trivial.
    - intro H. symmetry. apply Htime. destruct HR as [Ht _]. congruence.
Qed.

End Example1.

Module Example2.

(* TODO *)

End Example2.


Definition is_attack {A} (RA: relation A) {E: Equivalence RA} (Attack: sys A):=
  SP Attack RA.

Definition attack_on {A} (S: sys A) (Attack: sys A) := sys_union S Attack.

Require Ensembles.
Definition is_robust {A} (S: sys A) (AttackClass: sys A -> Prop)
           {RA: relation A} {E: Equivalence RA}
           (H: Ensembles.Included _ AttackClass (@is_attack _ RA E)) :=
  forall (Attack : sys A),
    Ensembles.In _ AttackClass Attack ->
    leq (toER (obs_eq (sys_union S Attack) RA)) (toER (obs_eq S RA)).

Lemma full_class_included {A} (RA: relation A) {E: Equivalence RA}:
  Ensembles.Included _ (is_attack RA) (is_attack RA).
Proof.
intros S HS. assumption.
Qed.

(* Preliminary lemmas for lemma A.1 *)
Lemma SP_one_make_trace {A} (R : relation A) {E : Equivalence R} (S : sys A):
  forall s s' (l : list A),
    R s s' ->
    exists (a' : A) (l' : list A),
      is_trace S (s' :: l' ++ a' :: nil)
      /\ R s a'
      /\ exists l'',
           stutter_equiv (s :: s :: nil) l''
           /\ View.same_view R l'' (s' :: l' ++ a' :: nil)
           /\ is_trace S l''.
Proof.
intros s s' l HR.
exists s'. exists nil. deep_splits; auto.
exists (s :: s :: nil). deep_splits; auto.
Qed.

Lemma SP_two_make_trace {A} (R : relation A) {E : Equivalence R}
      (S1 S2 : sys A):
  sys_included S1 S2 ->
  forall a s s' (l : list A),
    SP S1 R ->
    R s s' ->
    next S1 s a ->
    s <> a ->
    exists (a' : A) (l' : list A),
      is_trace S2 (s' :: l' ++ a' :: nil)
      /\ R a a'
      /\ exists l'',
           stutter_equiv (s :: a :: nil) l''
           /\ View.same_view R l'' (s' :: l' ++ a' :: nil)
           /\ is_trace S2 l''.
Proof.
intros Hincl a s s' l HSP HR Hnext Hneq.
specialize (HSP _ _ HR). simpl in HSP.
assert (is_trace S1 (s :: a :: nil)) as Htrace0 by auto.
pose (t0 := exist _ _ Htrace0).
apply (exploit_obs_eq t0) in HSP; try reflexivity.
destruct HSP as [t0'' [t0' [Ht0's' [Ht0't0'' Ht0t0'']]]].
symmetry in Ht0t0''.
pose proof (stutter_two_inv _ _ _ Hneq Ht0t0'') as H.
destruct H as [n1 [n2 Hn]].
unfold View.view in Ht0't0''. unfold lift_trace in Ht0't0''.
rewrite Hn in Ht0't0''.
pose proof (View.same_view_repeats_inv _ _ _ _ _ _ Ht0't0'')
  as Hinv.
destruct Hinv as [s'' [a' [l' [Heq HR']]]].
assert (s' = s'').
{ destruct t0' as [l0' Hl0']. simpl proj1_sig in *.
  destruct l0' as [|x0' l0']; [destruct Hl0'|].
  compute in Ht0's'. congruence. }
subst s''.
exists a'. exists l'. splits; trivial.
* destruct t0' as [[|x' l0'] Hl']; [destruct Hl'|].
  apply (is_trace_map_included _ _ _ Hincl).
  simpl in Heq. congruence.
* exists (proj1_sig t0''). splits.
  - symmetry. assumption.
  - rewrite <- Heq. rewrite Hn. symmetry. assumption.
  - apply (is_trace_map_included _ _ _ Hincl).
    destruct t0''; trivial.
Qed.

Lemma SP_make_trace {A} (R : relation A) {E : Equivalence R} (S1 S2 : sys A):
  forall a s s' (l : list A),
    SP S1 R ->
    SP S2 R ->
    R s s' ->
    next (sys_union S1 S2) s a ->
    exists (a' : A) (l' : list A),
      is_trace (sys_union S1 S2) (s' :: l' ++ a' :: nil)
      /\ R a a'
      /\ exists l'',
           stutter_equiv (s :: a :: nil) l''
           /\ View.same_view R l'' (s' :: l' ++ a' :: nil)
           /\ is_trace (sys_union S1 S2) l''.
Proof.
Require Import Classical.
intros a s s' l HSP1 HSP2 HR Hnext.
destruct (classic (s = a)) as [H | H].
* subst. apply SP_one_make_trace; auto.
* destruct Hnext as [Hnext1 | Hnext2].
  + apply (SP_two_make_trace R _ _ (sys_union_included_left _ _) _ s);
    auto.
  + apply (SP_two_make_trace R _ _ (sys_union_included_right _ _) _ s);
    auto.
Qed.

Lemma SP_sys_union_included {A} {R: relation A} {E: Equivalence R} :
  forall (S1 S2: sys A) (s1 s1': A),
    SP S1 R ->
    SP S2 R ->
    R s1 s1' ->
    set_included
      (set_equiv stutter)
      (obs_from s1 (sys_union S1 S2) R)
      (obs_from s1' (sys_union S1 S2) R).
Proof.
Require Import Classical.
intros S1 S2 s1 s1' H1 H2 Hs1s1' v1 [t1 [Hv1 Ht1s1]]. subst v1.
destruct t1 as [l1 Hl1].
destruct l1 as [| a1 l1]; [destruct Hl1 |].
generalize dependent a1.
generalize dependent s1'. generalize dependent s1.
induction l1; intros s1 s1' Hs1s1' a1 Hl1 Hs1.
+ { compute in Hs1. subst a1.
    pose (t1' := trace_one (sys_union S1 S2) s1').
    exists (View.view R t1').
    split.
    * exists t1'. split. trivial. reflexivity.
    * unfold t1'.
      unfold View.view. unfold lift_trace. simpl proj1_sig.
      split.
      + intros [l Hl] Ht. simpl proj1_sig in *.
        destruct l as [| s l]; [destruct Hl |].
        destruct l as [| ? ?]; compute in Ht; [| exfalso; tauto ].
        exists (exist _ _ Hl). deep_splits.
        - transitivity s1. symmetry; assumption. tauto.
        - reflexivity.
      + intros [l Hl] Ht. simpl proj1_sig in *.
        destruct l as [| s l]; [destruct Hl |].
        destruct l as [| ? ?]; compute in Ht; [| exfalso; tauto ].
        exists (exist _ _ Hl). deep_splits.
        - transitivity s1'; tauto.
        - reflexivity.
  }
+ { compute in Hs1. subst a1. destruct Hl1 as [Hs1a Hl1].
    rename a into a1.
    pose proof (SP_make_trace R S1 S2 a1 s1 s1' l1 H1 H2 Hs1s1' Hs1a) as H.
    destruct H as [a1' [l1' [Htrace' [Ha1a1' Hstutterview]]]].
    specialize (IHl1 a1 a1' Ha1a1' _ Hl1 eq_refl).
    destruct IHl1 as [v' [[t' [Hv' Ht'a1']] Ha1l1t']]. subst v'.
    assert (is_trace (sys_union S1 S2) (s1' :: l1' ++ proj1_sig t'))
      as H.
    { rewrite app_comm_cons.
      destruct t' as [[|a' l'] Hl']; [destruct Hl'|].
      simpl proj1_sig in *.
      compute in Ht'a1'. subst.
      destruct l' as [| a' l'].
      - rewrite <- app_comm_cons. trivial.
      - destruct Hl'. apply is_trace_app; trivial. }
    pose (t := exist _ _ H).
    exists (View.view R t). split.
    - apply obs_from_self; trivial. reflexivity.
    - { pose (t0 := (exist (fun l : list A => is_trace (sys_union S1 S2) l)
                           (s1 :: a1 :: l1) (conj Hs1a Hl1))).
        fold t0.
        destruct t' as [[|a' l'] Hl']; [destruct Hl'|].
        compute in Ht'a1'. subst a1'. rename a' into a1'.
        simpl proj1_sig in *. split.
        * { intros [l0 Hl0] H0.
            Opaque View.same_view. compute in H0. Transparent View.same_view.
            destruct l0 as [|x0 l0]; [destruct H0|]. destruct H0 as [Hs1x0 H0].
            destruct l0 as [|x1 l0]; [destruct H0|]. destruct H0 as [Ha1x1 H0].
            destruct Hstutterview as [l'' [Hstutter'' [Hview'' Htrace'']]].
            (* need to use Ha1l1t' and some lemma to '++' traces *)
            (* need for commutation? *)
            admit.
          }
        * { intros [l0 Hl0] H0.
            Opaque View.same_view. Opaque app. compute in H0.
            Transparent app. Transparent View.same_view.
            destruct l0 as [|x0 l0]; [destruct H0|]. destruct H0 as [Hs1x0 H0].
            apply View.same_view_app_inv_left in H0.
            destruct H0 as [l1'' [l2'' [Heq'' [Hview1'' Hview2'']]]]. subst.
            destruct l2'' as [|a2' l2'']; [destruct Hview2''|].
            destruct Hview2'' as [Ha1'a2' Hview2''].
            (* need to use Ha1l1t' and some lemma to '++' traces *)
            (* need for commutation? *)
            admit.
          }
      }
  }
Qed.

(* Lemma A.1 *)
Lemma SP_sys_union {A} {R: relation A} {E: Equivalence R} :
  forall (S1 S2: sys A),
    SP S1 R ->
    SP S2 R ->
    SP (sys_union S1 S2) R.
Proof.
Require Import Classical.
intros S1 S2 H1 H2 s1 s1' Hs1s1'. simpl in *. split.
* apply SP_sys_union_included; trivial.
* apply SP_sys_union_included; trivial. symmetry; trivial.
Qed.

Theorem thm4_1 {A} (S: sys A) (RA: relation A) {E: Equivalence RA}:
  SP S RA ->
  is_robust S (is_attack RA) (full_class_included RA).
Proof.
intros HSP Attack HAttack.
unfold Ensembles.In in HAttack. unfold is_attack in HAttack.
pose proof (corollary_2_1 _ _ HAttack) as Heq.
pose proof (SP_compat_ER_equiv _ _ _ _ _ HSP Heq) as H1.
pose proof (SP_compat_ER_equiv _ _ _ _ _ HAttack Heq) as H2.
pose proof (SP_sys_union _ _ H1 H2) as H.
unfold SP in H.
transitivity (toER (obs_eq (sys_union S Attack) (obs_eq Attack RA))).
* intros s s'. simpl. intro Hss'.
  apply (obs_eq_compat_ER_equiv _ (obs_eq Attack RA) RA _ _ _ _ Hss').
  symmetry. assumption.
* transitivity (toER (obs_eq Attack RA)).
  + assumption.
  + transitivity (toER RA).
    - assumption.
    - apply prop_2_1.
Qed.

(* Monotonicity of obs_eq (Prop 4.2).
   It seems that a commutation property is needed! *)
Definition commute {A} (R1: relation A) (R2: relation A) :=
  forall (x y z : A),
    R1 x y ->
    R2 y z ->
    exists y', R2 x y' /\ R1 y' z.

Lemma set_included_view_subrel {A} (S: sys A)
  (R1: relation A) {E1: Equivalence R1}
  (R2: relation A) {E2: Equivalence R2}:
  forall t t' : trace S,
  (forall x y, R1 x y -> R2 x y) ->
  @commute (trace S) stutter (View.view R2) ->
  set_included stutter (View.view R1 t) (View.view R1 t') ->
  set_included stutter (View.view R1 t') (View.view R1 t) ->
  set_included stutter (View.view R2 t) (View.view R2 t').
Proof.
intros t t' H12 Hcomm H1 H1' t0 Htt0.
apply View.exploit_set_included_stutter_view in H1.
destruct H1 as [t1 [Ht't1 Htt1]].
symmetry in Htt1.
pose proof (Hcomm _ _ _ Htt1 Htt0) as [t0' [Ht1t0' Ht0't0]].
exists t0'. split.
- transitivity t1. apply (View.view_subrel R1 R2); auto. assumption.
- symmetry. assumption.
Qed.

Lemma set_equiv_view_subrel {A} (S: sys A)
  (R1: relation A) {E1: Equivalence R1}
  (R2: relation A) {E2: Equivalence R2}:
  forall t t' : trace S,
  (forall x y, R1 x y -> R2 x y) ->
  @commute (trace S) stutter (View.view R2) ->
  set_equiv stutter (View.view R1 t) (View.view R1 t') ->
  set_equiv stutter (View.view R2 t) (View.view R2 t').
Proof.
intros t t' H12 Hstutterview [H1 H1']. split.
apply (set_included_view_subrel _ R1 R2); auto.
apply (set_included_view_subrel _ R1 R2); auto.
Qed.

Lemma obs_included_monotone {A} {S: sys A}
      (R1: relation A) {E1: Equivalence R1}
      (R2: relation A) {E2: Equivalence R2} :
  leq (toER R1) (toER R2) ->
  @commute (trace S) stutter (View.view R1) ->
  forall s s',
    set_included (set_equiv stutter) (obs_from s S R2) (obs_from s' S R2) ->
    set_included (set_equiv stutter) (obs_from s S R1) (obs_from s' S R1).
Proof.
intros H Hcomm s s' H2 v [t [Hv Hts]]. subst v.
specialize (H2 (View.view R2 t)).
destruct H2 as [v' [[t' [Hv' Ht's']] Htt']].
apply obs_from_self; auto. subst v'.
exists (View.view R1 t'). split.
+ apply obs_from_self; auto.
+ apply (set_equiv_view_subrel _ R2 R1); trivial.
Qed.

Lemma obs_eq_monotone {A} {S: sys A}
      (R1: relation A) {E1: Equivalence R1}
      (R2: relation A) {E2: Equivalence R2} :
  leq (toER R1) (toER R2) ->
  @commute (trace S) stutter (View.view R1) ->
  leq (toER (obs_eq S R1)) (toER (obs_eq S R2)).
Proof.
intros H Hcomm.
intros s s' [H2 H2']. simpl in *.
split; apply (obs_included_monotone R1 R2); trivial.
Qed.

Lemma commute_characterization {A} {S: sys A}
      (R: relation A) {E: Equivalence R} :
  @commute (trace S) stutter (View.view R) <->
  forall s s', next S s s' -> R s s' -> s = s'.
Proof.
split; intro H.
* intros s s' Hnext HR. unfold commute in H.
  pose (ts   := trace_one S s).
  pose (tss  := trace_cons s (trace_one S s)  (next_refl _ _ _)).
  pose (tss' := trace_cons s (trace_one S s') Hnext).
  assert (stutter ts tss) as Hstutter.
  { apply stutter_right. reflexivity. }
  assert (View.view R tss tss') as Hview.
  { deep_splits; trivial. reflexivity. }
  specialize (H _ _ _ Hstutter Hview).
  destruct H as [[l0 H0] [Hview0 Hstutter0]].
  destruct l0 as [|a0 l0]; [destruct H0|].
  destruct Hview0 as [Hsa0 Hview0].
  destruct l0; [|destruct Hview0].
  simpl_stutter_ctx.
  assert (a0 = s).
  { apply stutter_equiv_cons_inv in Hstutter0. assumption. }
  assert (a0 = s').
  { assert (In s' (a0 :: nil)) as HIn.
    { symmetry in Hstutter0. apply (stutter_equiv_in _ _ Hstutter0).
      compute; tauto.
    }
    compute in HIn; tauto.
  }
  congruence.
* assert (forall n (l1 l2 l3: list A),
            length l1 + length l2 <= n ->
            is_trace S l1 ->
            is_trace S l2 ->
            is_trace S l3 ->
            stutter_equiv l1 l2 ->
            View.same_view R l2 l3 ->
            exists l2',
              is_trace S l2'
              /\ View.same_view R l1 l2'
              /\ stutter_equiv l2' l3)
    as Hstrong.
  { intro n; induction n; intros l1 l2 l3 Hn H1 H2 H3 Hstutter Hview.
    * exfalso. destruct l1; [destruct H1|]. auto.
    * destruct Hstutter.
      + exfalso. destruct H1.
      + destruct l3 as [|a3 l3]; [destruct H3|]. simpl in Hn.
        destruct Hview as [Haa3 Hview].
        destruct l1 as [|a1 l1]; destruct l2 as [|a2 l2].
        - destruct l3; [| destruct Hview].
          exists (a3 :: nil). deep_splits; auto.
        - exfalso. apply stutter_equiv_nil_left_inv in Hstutter.
          congruence.
        - exfalso. apply stutter_equiv_nil_right_inv in Hstutter.
          congruence.
        - destruct H1 as [Hnext1 H1]. destruct H2 as [Hnext2 H2].
          destruct l3 as [|a3' l3]; [destruct Hview|].
          destruct H3 as [Hnext3 H3].
          destruct (IHn (a1 :: l1) (a2 :: l2) (a3' :: l3))
            as [l2' [H2' [Hview2' Hstutter2']]]; auto.
          exists (a3 :: l2').
          { deep_splits; auto.
            destruct l2' as [|a2' l2']; [destruct Hview2'|].
            apply stutter_equiv_cons_inv in Hstutter2'. subst.
            split; trivial.
          }
      + destruct H1 as [Hnext1 H1]. simpl in Hn.
        destruct (IHn (a :: l1) l2 l3)
          as [l2' [H2' [Hview2' Hstutter2']]]; auto.
        destruct l2' as [|a2' l2']; [destruct H2'|].
        destruct Hview2' as [Haa2' Hview2'].
        destruct l3 as [|a3 l3]; [destruct H3|].
        assert (a2' = a3).
        { apply stutter_equiv_cons_inv in Hstutter2'. assumption. }
        subst.
        exists (a3 :: a3 :: l2'). deep_splits; auto.
      + destruct H2 as [Hnext2 H2]. simpl in Hn.
        destruct l3 as [|a3 l3]; [destruct H3|].
        destruct Hview as [Haa3 Hview].
        destruct l3 as [|a3' l3]; [destruct Hview|].
        destruct H3 as [Hnext3 H3].
        simpl in Hn.
        destruct (IHn l1 (a :: l2) (a3' :: l3))
          as [l2' [H2' [Hview2' Hstutter2']]]; auto.
        destruct l2' as [|a2' l2']; [destruct H2'|].
        assert (a2' = a3').
        { apply stutter_equiv_cons_inv in Hstutter2'. assumption. }
        subst.
        destruct l1 as [|a1 l1]; [destruct H1|].
        destruct Hview2' as [Ha1a3 Hview2'].
        assert (a3 = a3').
        { apply H; trivial.
          apply stutter_equiv_cons_inv in Hstutter. subst.
          transitivity a; trivial. symmetry; trivial. }
        subst.
        exists (a3' :: l2'). deep_splits; auto.
  }
  intros [l1 H1] [l2 H2] [l3 H3] H12 H23.
  specialize (Hstrong (length l1 + length l2) l1 l2 l3).
  destruct Hstrong as [l2' [H2' [Hview2' Hstutter2']]]; auto.
  exists (exist _ _ H2'). auto.
Qed.
