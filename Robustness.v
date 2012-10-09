(** printing fun #λ# *)
(** printing forall #∀# *)
(** printing exists #∃# *)
(** printing -> #→# *)
(** printing <- #←# *)
(** printing <-> #↔# *)
(** printing => #⇒# *)
(** printing <= #≤# *)
(** printing >= #≥# *)
(** printing /\ #∧# *)
(** printing ‌‌\/ #∨# *)
(** printing |- #⊢# *)
(** printing <> #≠# *)
(** printing ~ #¬# *)
(** printing * #×# *)

(** Verification of the article:

Robust Declassification
Steve Zdancewic, Andrew C. Myers

In Proc. of 14th IEEE Computer Security Foundations Workshop (CSFW),
pages 15-23, Cape Breton, Canada, June 2001.

http://www.cis.upenn.edu/~stevez/papers/ZM01b.pdf
*)

Require Import MyTactics.
Require Import Relations.
Require Import MyList.
Require Import RelationClasses.
Require Import Stutter.
Require Import EquivClass.
Require Import SetPredicates.
Require Import Classical.
Require Import Kleene.

(** * Systems. *)
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

(** * Traces. *)
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

(** A trace is a list that is a trace. *)
Definition trace {A} (S: sys A) := { l: list A | is_trace S l }.

Definition trace_one {A} (S: sys A) (x: A) : trace S.
Proof.
exists (x :: nil). simpl. trivial.
Defined.

(** The head of a trace. *)
Definition hd {A} {S: sys A} (tr : trace S) : A :=
match tr with
| exist nil H => match H with end
| exist (a :: _) _ => a
end.

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

(** Traces that start from a given state. *)
Definition is_trace_from {A} {S: sys A} (tr: trace S) (s : A) : Prop :=
  hd tr = s.

Ltac is_trace_from_reflexivity :=
  match goal with
    | |- is_trace_from _ _ => reflexivity
  end.
Hint Extern 3 => is_trace_from_reflexivity.

Lemma trace_cons_is_trace_from {A} {S: sys A}:
  forall (s : A) (t : trace S) (H: next S s (hd t)),
    is_trace_from (trace_cons s t H) s.
Proof.
intros s t H.
destruct t as [[| a l] Hl]; auto.
Qed.

(** * Lifting binary functions from lists to traces. *)
Definition lift_trace {A B} {S: sys A}
           (f: list A -> list A -> B) (t1 t2: trace S) : B :=
  f (proj1_sig t1) (proj1_sig t2).
Hint Unfold lift_trace.

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

(** The definition of view over traces. *)
Definition view {A} {S: sys A} (R: relation A) (t: trace S) :=
  map (class R) (proj1_sig t).
Hint Unfold view.

Lemma view_eq_subrel {A} (S: sys A)
      (R1: relation A) {E1: Equivalence R1}
      (R2: relation A) {E2: Equivalence R2}:
  forall (t t': trace S),
    view R1 t = view R1 t' ->
    inclusion _ R1 R2 ->
    view R2 t = view R2 t'.
Proof.
intros [l Hl] [l' Hl'] Heq H12.
unfold view in *; simpl in *. clear Hl Hl'.
generalize dependent l'. induction l; intros l' Heq.
* destruct l' ; simpl in *; [trivial | exfalso; congruence].
* destruct l' ; simpl in *; [exfalso; congruence|].
  inversion Heq; subst. f_equal; auto.
  apply (class_eq_included_rel R1 R2); eauto.
Qed.

(* Compatibility with equivalence of equivalence relations. *)
Require Import ERLattice.
Lemma view_compat_ER_equiv {A} (S: sys A):
  forall (R1 R2: relation A) {E1: Equivalence R1} {E2: Equivalence R2}
         (t t': trace S),
    equiv (toER R1) (toER R2) ->
    view R1 t = view R2 t.
Proof.
intros R1 R2 E1 E2 [l Hl] [l' Hl'] Heq.
unfold view; simpl.
apply map_ext. apply class_eq_rel; auto.
compute in Heq. compute.
tauto.
Qed.

(** * Observations. *)
(* Observation from a given state. *)
Definition obs_from {A} (s : A) (S: sys A) (R: relation A)
: (list (A -> Prop)) -> Prop :=
  fun tView =>
    exists (t : trace S), tView = view R t /\ is_trace_from t s.


(** ** Lemmas to exploit inclusions of observations. *)
Lemma exploit_obs_included {A} {S: sys A}
      {R: relation A} {E: Equivalence R}:
  forall (t : trace S) s1 s2,
    set_included stutter_equiv (obs_from s1 S R) (obs_from s2 S R) ->
    is_trace_from t s1 ->
    exists (t': trace S),
      is_trace_from t' s2
      /\ stutter_equiv (view R t) (view R t').
Proof.
intros t s1 s2 H Ht.
specialize (H (view R t)).
destruct H as [v [[t' [Hv Ht's2]] Htt']].
exists t. split; trivial.
subst v.
eauto.
Qed.

Lemma exploit_obs_included_one {A} {S: sys A}
      {R: relation A} {E: Equivalence R}:
  forall s1 s2,
    set_included stutter_equiv (obs_from s1 S R) (obs_from s2 S R) ->
      exists (t': trace S),
        is_trace_from t' s2
        /\ stutter_equiv (view R (trace_one S s1)) (view R t').
Proof.
intros s1 s2 H.
apply (exploit_obs_included _ s1); auto.
Qed.

(** ** Observational equivalence. *)
Definition obs_eq {A} (S: sys A) (R: relation A) : relation A :=
  fun s1 s2 =>
    set_equiv stutter_equiv (obs_from s1 S R) (obs_from s2 S R).

Instance obs_eq_Equivalence {A} (S: sys A) (R: relation A) {E: Equivalence R}
: Equivalence (obs_eq S R).
Proof.
unfold obs_eq.
constructor.
* intro s. reflexivity.
* intros s1 s2 H. symmetry. assumption.
* intros s1 s2 s3 H12 H23. transitivity (obs_from s2 S R); assumption.
Qed.

Definition obs_eq_ER {A} (S: sys A) (R: er A) : er A :=
  @toER _
        (obs_eq S (proj1_sig R))
        (@obs_eq_Equivalence A S (proj1_sig R) (proj2_sig R)).

Lemma obs_from_self {A} {S: sys A} (R: relation A) {E: Equivalence R}:
  forall s (t: trace S),
    is_trace_from t s ->
    obs_from s S R (view R t).
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
    exists (t': trace S),
      is_trace_from t' s2
      /\ stutter_equiv (view R t) (view R t').
Proof.
intros t s1 s2 [H _] Ht.
apply (exploit_obs_included _ s1); trivial.
Qed.

Lemma exploit_obs_eq_one {A} {S: sys A}
      {R: relation A} {E: Equivalence R}:
  forall s1 s2,
    obs_eq S R s1 s2 ->
      exists (t': trace S),
        is_trace_from t' s2
        /\ stutter_equiv (view R (trace_one S s1)) (view R t').
Proof.
intros s1 s2 H.
apply (exploit_obs_eq _ s1). trivial. reflexivity.
Qed.

Lemma obs_from_compat_ER_included {A} (S: sys A):
  forall (R1 R2: relation A) (E1: Equivalence R1) (E2: Equivalence R2) s,
    equiv (toER R1) (toER R2) ->
    set_included eq (obs_from s S R1) (obs_from s S R2).
Proof.
intros R1 R2 E1 E2 s Heq.
intros v [t [Hv Hts]]. subst v.
exists (view R2 t). split.
+ exists t. split; trivial.
+ eapply view_compat_ER_equiv; trivial.
Qed.

Lemma obs_from_compat_ER_equiv {A} (S: sys A):
  forall (R1 R2: relation A) (E1: Equivalence R1) (E2: Equivalence R2) s,
    equiv (toER R1) (toER R2) ->
    set_equiv eq (obs_from s S R1) (obs_from s S R2).
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
assert (forall x y : list (A -> Prop), eq x y -> stutter_equiv x y) as Haux.
{ intros x y Hxy. rewrite Hxy. reflexivity. }
split.
* transitivity (obs_from s S R1).
  + apply (set_included_subrel eq stutter_equiv); trivial.
    eapply obs_from_compat_ER_included; eauto. symmetry; trivial.
  + transitivity (obs_from s' S R1).
    - destruct HR1. assumption.
    - apply (set_included_subrel eq stutter_equiv); trivial.
      eapply obs_from_compat_ER_included; eauto.
* symmetry in Heq. symmetry in HR1. transitivity (obs_from s' S R1).
  + apply (set_included_subrel eq stutter_equiv); trivial.
    eapply obs_from_compat_ER_included; eauto.
  + transitivity (obs_from s S R1).
    - destruct HR1. assumption.
    - apply (set_included_subrel eq stutter_equiv); trivial.
      eapply obs_from_compat_ER_included; eauto. symmetry; trivial.
Qed.

Lemma obs_eq_R {A} {S: sys A} {R: relation A} {E: Equivalence R}:
  forall s s' : A,
    obs_eq S R s s' ->
    R s s'.
Proof.
intros s1 s2 H12.
apply exploit_obs_eq_one in H12.
destruct H12 as [t2 [Ht2s2 Hs1t2]].
destruct t2 as [[| s l2] Hl2]; [destruct Hl2 |].
compute in Ht2s2. subst s.
pose proof (stutter_equiv_cons_inv _ _ _ _ Hs1t2).
apply class_eq_inv; trivial.
Qed.

(** * The security property. *)
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
     set_equiv stutter_equiv (obs_from s1 S R) (obs_from s2 S R)).
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
         stutter_equiv (view R t1) (view R t2)).
Proof.
split; intro H.
* intros s1 s2 HR t1 Ht1.
  specialize (H s1 s2 HR). simpl in H.
  destruct H as [H _].
  specialize (H (view R t1) (obs_from_self _ _ _ Ht1)).
  destruct H as [v [Hvs2 Ht1v]].
  destruct Hvs2 as [t2 [Hv Ht2s2]].
  subst v.
  exists t2. auto.
* intros s1 s2 HR. simpl in *. split.
  + intros v1 [t1 [Hv1 Ht1s1]].
    subst v1.
    specialize (H s1 s2 HR t1 Ht1s1).
    destruct H as [t2 [Ht2s2 Ht1t2]].
    exists (view R t2). auto using obs_from_self.
  + intros v2 [t2 [Hv2 Ht2s2]].
    subst v2.
    symmetry in HR.
    specialize (H s2 s1 HR t2 Ht2s2).
    destruct H as [t1 [Ht1s1 Ht2t1]].
    exists (view R t1). auto using obs_from_self.
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

(** ** About the bottom equivalence relation. *)
(** Preliminary lemmas. *)
Module SP_bottom_aux.

Lemma view_bottom {A} {S: sys A}:
  forall (t1 t2: trace S),
    view (er_bottom_rel A) t1 = view (er_bottom_rel A) t2
    <-> length (proj1_sig t1) = length (proj1_sig t2).
Proof.
intros [l1 Hl1] [l2 Hl2].
unfold view. simpl. split.
* intros H.
  repeat rewrite <- (map_length (class (er_bottom_rel A))).
  congruence.
* intros H. clear Hl1 Hl2.
  generalize dependent l2. induction l1; intros l2 H; simpl in *.
  + destruct l2; simpl in *; trivial.
    exfalso; omega.
  + destruct l2 as [| a2 l2]; simpl in H.
    - exfalso. omega.
    - simpl. f_equal. auto.
Qed.

Lemma replicate_trace_bottom {A} {S: sys A} :
  forall a (t: trace S),
    stutter_equiv
      (view (er_bottom_rel A) (trace_one S a))
      (view (er_bottom_rel A) t).
Proof.
intros a [l Hl].
destruct l as [|a' l]; [destruct Hl|].
generalize dependent a.
generalize dependent a'.
induction l; intros a1 Hl a2.
* reflexivity.
* destruct Hl as [Ha1a Hl].
  specialize (IHl a Hl a2).
  apply stutter_right. assumption.
Qed.

Lemma set_included_obs_from_bottom {A} {S: sys A}:
  forall s1 s2,
    set_included stutter_equiv
                 (obs_from s1 S (er_bottom_rel A))
                 (obs_from s2 S (er_bottom_rel A)).
Proof.
intros s1 s2 v Hv.
destruct Hv as [t [Hv Hts1]]. subst v.
exists (view (er_bottom_rel A) (trace_one S s2)). split.
* apply obs_from_self; auto.
* symmetry. apply replicate_trace_bottom.
Qed.

Lemma obs_eq_bottom {A} {S: sys A}:
  forall s1 s2,
    obs_eq S (er_bottom_rel A) s1 s2.
Proof.
intros s1 s2. split; auto using set_included_obs_from_bottom.
Qed.

End SP_bottom_aux.

(** All systems are secure for the bottom equivalence relation. *)
Lemma SP_bottom {A} (S: sys A) :
  SP S (er_bottom_rel A).
Proof.
intros s1 s2 H. apply SP_bottom_aux.obs_eq_bottom.
Qed.

(** ** About the top equivalence relation. *)
(** All systems are secure for the top equivalence relation. *)
Lemma SP_top {A} (S: sys A) :
  SP S (proj1_sig (er_top A)).
Proof.
intros s1 s2 H. rewrite H.
reflexivity.
Qed.

(** TODO: Declassification set D, at the end of section 2.3 *)

(** * Attacks. *)
Definition is_attack {A} (RA: relation A) {E: Equivalence RA} (Attack: sys A):=
  SP Attack RA.

Definition attack_on {A} (S: sys A) (Attack: sys A) := sys_union S Attack.

Require Ensembles.
Definition robust {A} (S: sys A) (AttackClass: sys A -> Prop)
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

(** ** Preliminary lemmas for lemma A.1 *)

Lemma SP_one_make_trace {A} (R : relation A) {E : Equivalence R} (S : sys A):
  forall a s s' (l : list A),
    R s s' ->
    next S s a ->
    R s a ->
    exists (a' : A) (l' : list A)
           (Htrace: is_trace S (s' :: l' ++ a' :: nil))
           (Htrace_two: is_trace S (s :: a :: nil)),
      R a a'
      /\ stutter_equiv
           (view R (exist _ (s :: a :: nil) Htrace_two))
           (view R (exist _ (s' :: l' ++ a' :: nil) Htrace)).
Proof.
intros a s s' l HRss' Hnext HRsa.
exists s'. exists nil.
exists (@is_trace_repeat _ S s' 1).
assert (is_trace S (s :: a :: nil)) as Htrace_two. { split; auto. }
exists Htrace_two. split.
* transitivity s. symmetry; trivial. trivial.
* compute.
  replace (R s') with (R s).
  replace (R a) with (R s).
  reflexivity.
  apply class_eq_compat; trivial.
  apply class_eq_compat; trivial.
Qed.

Lemma SP_two_make_trace {A} (R : relation A) {E : Equivalence R}
      (S1 S2 : sys A):
  sys_included S1 S2 ->
  forall a s s' (l : list A),
    SP S1 R ->
    R s s' ->
    next S1 s a ->
    ~ R s a ->
    exists (a' : A) (l' : list A)
           (Htrace: is_trace S2 (s' :: l' ++ a' :: nil))
           (Htrace_two: is_trace S2 (s :: a :: nil)),
      R a a'
      /\ stutter_equiv
           (view R (exist _ (s :: a :: nil) Htrace_two))
           (view R (exist _ (s' :: l' ++ a' :: nil) Htrace)).
Proof.
intros Hincl a s s' l HSP HR Hnext HnR.
specialize (HSP _ _ HR). simpl in HSP.
assert (is_trace S1 (s :: a :: nil)) as Htrace0 by auto.
pose (t0 := exist _ _ Htrace0).
apply (exploit_obs_eq t0) in HSP; try reflexivity.
destruct HSP as [t0' [Ht0's' Ht0t0']].
exists (last (proj1_sig t0') a).
exists (removelast (proj1_sig t0')).
destruct t0' as [l0' Hl0']. destruct l0' as [|a0' l0']; [destruct Hl0'|].
compute in Ht0's'. subst a0'. simpl proj1_sig.
rewrite <- app_removelast_last; try congruence.
assert (is_trace S2 (s' :: s' :: l0')) as Htrace.
{ split. auto. eapply is_trace_map_included; eauto. }
exists Htrace.
assert (is_trace S2 (s :: a :: nil)) as Htrace_two. { split; auto. }
exists Htrace_two. split.
* apply class_eq_inv.
  transitivity (class R (last (s :: a :: nil) a)). reflexivity.
  repeat rewrite <- (last_map (class R)).
  apply stutter_equiv_last_inv; solve [trivial | simpl; congruence].
* apply stutter_right. assumption.
Qed.

Lemma SP_make_trace {A} (R : relation A) {E : Equivalence R} (S1 S2 : sys A):
  forall a s s' (l : list A),
    SP S1 R ->
    SP S2 R ->
    R s s' ->
    next (sys_union S1 S2) s a ->
    exists (a' : A) (l' : list A)
           (Htrace: is_trace (sys_union S1 S2) (s' :: l' ++ a' :: nil))
           (Htrace_two: is_trace (sys_union S1 S2) (s :: a :: nil)),
      R a a'
      /\ stutter_equiv
           (view R (exist _ (s :: a :: nil) Htrace_two))
           (view R (exist _ (s' :: l' ++ a' :: nil) Htrace)).
Proof.
intros a s s' l HSP1 HSP2 HR Hnext.
destruct (classic (R s a)) as [H | H].
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
    set_included stutter_equiv
      (obs_from s1 (sys_union S1 S2) R)
      (obs_from s1' (sys_union S1 S2) R).
Proof.
intros S1 S2 s1 s1' H1 H2 Hs1s1' v1 [t1 [Hv1 Ht1s1]]. subst v1.
destruct t1 as [l1 Hl1].
destruct l1 as [| a1 l1]; [destruct Hl1 |].
generalize dependent a1.
generalize dependent s1'. generalize dependent s1.
induction l1; intros s1 s1' Hs1s1' a1 Hl1 Hs1.
+ { compute in Hs1. subst a1.
    pose (t1' := trace_one (sys_union S1 S2) s1').
    exists (view R t1').
    split.
    * exists t1'. split. trivial. reflexivity.
    * unfold t1'. compute.
      replace (R s1) with (class R s1) by reflexivity.
      rewrite (class_eq_compat s1 s1'); trivial.
      auto.
  }
+ { compute in Hs1. subst a1. destruct Hl1 as [Hs1a Hl1].
    rename a into a1.
    pose proof (SP_make_trace R S1 S2 a1 s1 s1' l1 H1 H2 Hs1s1' Hs1a) as H.
    destruct H as [a1' [l1' [Htrace' [Htrace_two' [Ha1a1' Hstutterview]]]]].
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
    exists (view R t). split.
    - apply obs_from_self; trivial. reflexivity.
    - pose (t0 := (exist (fun l : list A => is_trace (sys_union S1 S2) l)
                         (s1 :: a1 :: l1) (conj Hs1a Hl1))).
      fold t0.
      destruct t' as [[|a' l'] Hl']; [destruct Hl'|].
      compute in Ht'a1'. subst a1'. rename a' into a1'.
      simpl proj1_sig in *.
      unfold view in *. simpl proj1_sig in *.
      transitivity (map (class R) ((s1 :: a1 :: nil) ++ a1 :: l1)).
      * simpl; apply stutter_same; apply stutter_right; reflexivity.
      * transitivity (map (class R) ((s1' :: l1' ++ a1' :: nil) ++ a1' :: l')).
        + repeat rewrite map_app. apply stutter_equiv_congruence; trivial.
        + rewrite app_comm_cons. rewrite app_comm_cons_cons.
          rewrite app_comm_cons.
          repeat rewrite map_app. simpl map.
          apply stutter_middle.
  }
Qed.

(** ** Lemma A.1 *)
Lemma SP_sys_union {A} {R: relation A} {E: Equivalence R} :
  forall (S1 S2: sys A),
    SP S1 R ->
    SP S2 R ->
    SP (sys_union S1 S2) R.
Proof.
intros S1 S2 H1 H2 s1 s1' Hs1s1'. simpl in *. split.
* apply SP_sys_union_included; trivial.
* apply SP_sys_union_included; trivial. symmetry; trivial.
Qed.

(** ** The robustness theorem (Theorem 4.1). *)
Theorem SP_robust {A} (S: sys A) (RA: relation A) {E: Equivalence RA}:
  SP S RA ->
  robust S (is_attack RA) (full_class_included RA).
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


(** * Monotonicity of obs_eq (Prop 4.2). *)
Lemma stutter_equiv_map_class_included {A}
      (R1 : relation A) {E1 : Equivalence R1}
      (R2 : relation A) {E2 : Equivalence R2} :
  (forall x y, R1 x y -> R2 x y) ->
  forall (l l': list A),
    stutter_equiv (map (class R1) l) (map (class R1) l') ->
    stutter_equiv (map (class R2) l) (map (class R2) l').
Proof.
intros Hincl l0 l0' H.
remember (map (class R1) l0) as l.
remember (map (class R1) l0') as l'.
generalize dependent l0'.
generalize dependent l0.
induction H; intros l0 Heq l0' Heq'.
* destruct l0; destruct l0'; simpl in *; try congruence. auto.
* destruct l0 as [|a0 l0]; simpl in *; try congruence.
  destruct l0' as [|a0' l0']; simpl in *; try congruence.
  inversion Heq; subst. inversion Heq'; subst. clear Heq Heq'.
  apply (class_eq_included_rel R1 R2 Hincl) in H1.
  rewrite H1. auto.
* destruct l0 as [|a0 l0]; simpl in *; try congruence.
  destruct l0 as [|a0' l0]; simpl in *; try congruence.
  inversion Heq; subst. clear Heq.
  pose proof (class_eq_included_rel R1 R2 Hincl _ _ H2) as H0.
  rewrite H0. apply stutter_left.
  transitivity (map (class R2) (a0' :: l0)). reflexivity.
  eapply IHstutter_equiv; auto. rewrite H2. reflexivity.
* destruct l0' as [|a0 l0']; simpl in *; try congruence.
  destruct l0' as [|a0' l0']; simpl in *; try congruence.
  inversion Heq'; subst. clear Heq'.
  pose proof (class_eq_included_rel R1 R2 Hincl _ _ H2) as H0.
  rewrite H0. apply stutter_right.
  transitivity (map (class R2) (a0' :: l0')).
  eapply IHstutter_equiv; auto. rewrite H2. reflexivity.
  reflexivity.
Qed.

Lemma obs_included_monotone {A} {S: sys A}
      (R1: relation A) {E1: Equivalence R1}
      (R2: relation A) {E2: Equivalence R2} :
  leq (toER R1) (toER R2) ->
  forall s s',
    set_included stutter_equiv (obs_from s S R2) (obs_from s' S R2) ->
    set_included stutter_equiv (obs_from s S R1) (obs_from s' S R1).
Proof.
intros H s s' H2 v [t [Hv Hts]]. subst v.
specialize (H2 (view R2 t)).
destruct H2 as [v' [[t' [Hv' Ht's']] Htt']].
apply obs_from_self; auto. subst v'.
exists (view R1 t'). split.
+ apply obs_from_self; auto.
+ apply (stutter_equiv_map_class_included R2 R1); auto.
Qed.

(** The monotonicity lemma (Prop 4.2). *)
Lemma obs_eq_monotone {A} {S: sys A}
      (R1: relation A) {E1: Equivalence R1}
      (R2: relation A) {E2: Equivalence R2} :
  leq (toER R1) (toER R2) ->
  leq (toER (obs_eq S R1)) (toER (obs_eq S R2)).
Proof.
intros H s s' [H2 H2']. simpl in *.
split; apply (obs_included_monotone R1 R2); trivial.
Qed.

Lemma obs_eq_monotone_ER {A} (S: sys A): monotone (obs_eq_ER S).
Proof.
intros [R1 E1] [R2 E2] H.
apply obs_eq_monotone. assumption.
Qed.

(** * Iterated observations. *)
Definition iter_obs_eq {A} (n: nat) (S: sys A) (R: er A) : er A :=
  n_iter (obs_eq_ER S) n R.

Definition omega_obs_eq {A} (S: sys A) (R: er A):
  er A :=
  FAMILY.big_union (fun n => iter_obs_eq n S R).

Instance omega_obs_eq_Equivalence {A} (S: sys A) (R: er A):
  Equivalence (proj1_sig (omega_obs_eq S R)).
Proof.
apply (proj2_sig (omega_obs_eq S R)).
Qed.
Hint Resolve omega_obs_eq_Equivalence.

Lemma obs_eq_continuous {A} (S: sys A): continuous (obs_eq_ER S).
Proof.
intros P sup Hdir Hsup.
assert (directed (im (obs_eq_ER S) P)) as HdirIm. (* TODO: that is an abstract result *)
{ destruct Hdir as [Hnonempty Hdir]. split.
  * destruct Hnonempty as [z Hz].
    exists (obs_eq_ER S z). exists z. split; auto. reflexivity.
  * intros x y [x0 [Hx0 Hx]] [y0 [Hy0 Hy]].
    destruct (Hdir x0 y0 Hx0 Hy0) as [z0 [Hz0 [Hx0z0 Hy0z0]]].
    exists (obs_eq_ER S z0). splits.
    + exists z0. split; auto. reflexivity.
    + rewrite Hx. apply obs_eq_monotone_ER. trivial.
    + rewrite Hy. apply obs_eq_monotone_ER. trivial.
}
destruct (complete_def _ HdirIm) as [sup2 Hsup2].
assert (leq sup sup2).
{ destruct Hsup as [_ HLUB]. apply HLUB.
  intros R HR. transitivity (obs_eq_ER S R).
  apply prop_2_1. destruct Hsup2 as [HUB2 _].
  apply HUB2. exists R. split. trivial. reflexivity.
}
exists sup2. split; trivial. split.
* destruct Hsup2 as [_ HLUB2]. apply HLUB2.
  intros R [R0 [HR0 HR]]. rewrite HR.
  apply obs_eq_monotone_ER. destruct Hsup as [HUB _]. auto.
* transitivity sup; trivial.
  pose (sup' := SET.big_union P).
  pose proof (SET.big_union_is_sup P) as Hsup'.
  assert (equiv sup sup') as Heq. { apply (is_sup_unique P); trivial. }
  transitivity (obs_eq_ER S sup').
  + apply obs_eq_monotone_ER. rewrite Heq. reflexivity.
  + transitivity sup'.
    - { intros s s' Hss'.
        unfold sup'. unfold SET.big_union. simpl.
        unfold sup' in Hss'. unfold SET.big_union in Hss'. simpl in Hss'.
        split.
        * intros v [t [Hv Hts]]. subst v.
          admit. (* I don't know how to prove that... *)
        * admit. (* symmetric case *)
      }
    - rewrite Heq. reflexivity.
Qed.

(** Proposition 4.1. *)
(** That is related to the continuity of obs_eq. *)
Lemma SP_omega {A} {S: sys A} {R: er A}:
  SP S (proj1_sig (omega_obs_eq S R)).
Proof.
Admitted.

(** Upper bound on information leaked (Theorem 4.2). *)
Lemma attack_leak_upper_bound {A} {S: sys A} {R: er A}:
  forall (Attack : sys A),
    @is_attack _ (proj1_sig R) (proj2_sig R) Attack ->
    SP Attack (proj1_sig (omega_obs_eq S R)) ->
    leq (obs_eq_ER (sys_union S Attack) R) (omega_obs_eq S R).
Proof.
intros Attack Hattack HSP.
transitivity (toER (obs_eq (sys_union S Attack) (proj1_sig (omega_obs_eq S R)))).
+ apply obs_eq_monotone.
  apply (FAMILY.big_union_upper_bound (fun n => iter_obs_eq n S R) 0).
+ transitivity (toER (proj1_sig (omega_obs_eq S R))).
  apply SP_sys_union; auto. apply SP_omega.
  unfold leq. unfold er_coarser. simpl. trivial.
Qed.
