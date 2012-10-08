Require Import MyTactics.
Require Export List.

Fixpoint repeat {A} (a: A) (n: nat) : list A :=
match n with
| O => nil
| S n => a :: repeat a n
end.

Lemma map_repeat {A B} (f: A -> B) (a: A) (n: nat) :
  map f (repeat a n) = repeat (f a) n.
Proof.
induction n.
* reflexivity.
* simpl. congruence.
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

Lemma last_nth {A} :
  forall (l: list A) (default: A),
    last l default = nth (length l - 1) l default.
Proof.
intros l default. induction l.
* reflexivity.
* destruct l as [|b l].
  + reflexivity.
  + transitivity (last (b :: l) default). reflexivity.
    rewrite IHl. simpl.
    replace (length l - 0) with (length l) by auto with arith.
    reflexivity.
Qed.

Lemma last_In {A} :
  forall (l: list A) (default: A),
    l <> nil -> In (last l default) l.
Proof.
intros l default H. destruct l as [|a l].
* exfalso. congruence.
* rewrite last_nth. apply nth_In. auto with arith.
Qed.

Lemma last_map {A B} (f: A -> B):
  forall (l: list A) (default: A),
    last (map f l) (f default) = f (last l default).
Proof.
intros l default. induction l.
* reflexivity.
* simpl map. destruct l as [|b l].
  + reflexivity.
  + transitivity (last (map f (b :: l)) (f default)). reflexivity.
    rewrite IHl. reflexivity.
Qed.

Lemma app_comm_cons_cons {A}:
  forall a1 a2 (l1 l2: list A),
    (l1 ++ a1 :: nil) ++ a2 :: l2 = l1 ++ a1 :: a2 :: l2.
Proof.
intros a1 a2 l1.
generalize dependent a2. generalize dependent a1.
induction l1; intros a1 a2 l2.
* reflexivity.
* simpl. f_equal. auto.
Qed.
