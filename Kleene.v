Require Import Lattice.
Require Import Tactics.
Require Import NatLattice.

Fixpoint n_iter {T} (f: T -> T) (n : nat) (zero : T) : T :=
match n with
| O => zero
| S n => n_iter f n (f zero)
end.

Lemma n_iter_correct {T} :
  forall (f : T -> T) n x, n_iter f (S n) x = f (n_iter f n x).
Proof.
intros f n. induction n; intros x.
reflexivity.
simpl. rewrite <- IHn. reflexivity.
Qed.

Lemma n_iter_monotone_zero {T} `{L: PreLattice T} :
  forall (f: T -> T), monotone f -> forall n, monotone (n_iter f n).
Proof.
intros f H n. induction n.
* unfold monotone; auto.
* intros x y Hxy. repeat rewrite n_iter_correct. auto.
Qed.

Lemma n_iter_ascending_1 {T} `{L: BottomPreLattice T} :
  forall (f: T -> T), monotone f ->
  forall n,
    leq (n_iter f n bottom) (n_iter f (S n) bottom).
Proof.
intros f Hf n.
simpl. apply n_iter_monotone_zero; trivial. apply bottom_minimum.
Qed.

Lemma n_iter_ascending_n {T} `{L: BottomPreLattice T} :
  forall (f: T -> T), monotone f ->
  forall n m, leq (n_iter f n bottom) (n_iter f (n + m) bottom).
Proof.
Require Omega.
intros f H n m. destruct m.
* replace (n + 0) with n by omega. reflexivity.
* induction m.
  - replace (n + 1) with (S n) by omega. apply n_iter_ascending_1; trivial.
  - transitivity (n_iter f (n + S m) bottom). trivial.
    replace (n + S (S m)) with (S (n + S m)) by omega.
    apply n_iter_ascending_1; trivial.
Qed.

Lemma n_iter_monotone {T} `{L: BottomPreLattice T} :
  forall (f: T -> T), monotone f -> monotone (fun n => n_iter f n bottom).
Proof.
intros f Hf n1 n2 H.
replace n2 with (n1 + (n2 - n1)).
apply n_iter_ascending_n; trivial.
auto with arith.
Qed.

Definition iteration_chain {T} `{BottomPreLattice T} (f: T -> T) :=
  fun x => exists n, equiv x (n_iter f n bottom).

Lemma iteration_chain_directed {T} `{BottomPreLattice T} :
  forall (f: T -> T), monotone f -> directed (iteration_chain f).
Proof.
intros f Hf. apply monotone_seq_directed.
apply n_iter_monotone. trivial.
Qed.

Lemma n_iter_upper_bound_f {T} `{L: BottomPreLattice T} :
  forall (f: T -> T), monotone f ->
  forall b, (forall n, leq (n_iter f n bottom) b) ->
  forall n, leq (n_iter f n bottom) (f b).
Proof.
intros f Hf b H n. induction n.
apply bottom_minimum.
rewrite n_iter_correct. auto.
Qed.

Lemma iteration_chain_upper_bound_f {T} `{L: BottomPreLattice T} :
  forall (f: T -> T), monotone f ->
  forall b, is_upper_bound (iteration_chain f) b ->
  is_upper_bound (iteration_chain f) (f b).
Proof.
intros f Hf b H x [n Hx]. rewrite Hx.
apply n_iter_upper_bound_f. trivial.
intro n'. apply H. exists n'. reflexivity.
Qed.

Lemma iteration_chain_upper_bound_im_f {T} `{L: BottomPreLattice T} :
  forall (f: T -> T), monotone f ->
  forall b, is_upper_bound (iteration_chain f) b ->
  is_upper_bound (im f (iteration_chain f)) b.
Proof.
intros f Hf b H. intros y [x [[n Hx] Heq]]. rewrite Heq.
apply H. exists (S n). rewrite n_iter_correct.
apply monotone_equiv_compat; auto.
Qed.

Definition is_fixed_point {T} `{L : Setoid T} (f : T -> T) (x : T) :=
  equiv (f x) x.

Lemma fixed_point_is_sup_chain {T} `{L : BottomPreLattice T} :
  forall (f: T -> T), monotone f ->
  forall x, is_fixed_point f x -> is_upper_bound (iteration_chain f) x.
Proof.
intros f Hf x Hx y [n Hy]. generalize dependent y. induction n; intros y Hy.
* rewrite Hy. apply bottom_minimum.
* rewrite Hy. rewrite n_iter_correct.
  unfold is_fixed_point in Hx. rewrite <- Hx.
  apply Hf. apply IHn. reflexivity.
Qed.

Theorem kleene_fixed_point {T order}
        `{L: CompletePreLattice T order} `{B: BottomPreLattice T order} :
  forall (f: T -> T), continuous f ->
  exists x, is_sup (iteration_chain f) x
         /\ is_fixed_point f x
         /\ (forall y, is_fixed_point f y -> leq x y).
Proof.
intros f Hf_continuous.
assert (monotone f) as Hf_monotone by (apply continuous_monotone; trivial).
pose (chain := iteration_chain f).
pose (HchainDirected := iteration_chain_directed f Hf_monotone).
destruct (complete_def chain HchainDirected) as [sup Hsup].
destruct (Hf_continuous chain sup HchainDirected Hsup)
  as [sup2 [Hsup2IsSup Hsup2Eq]].
exists sup. split; trivial. split.
* split.
  - destruct Hsup2IsSup as [_ Hsup2L].
    rewrite <- Hsup2Eq. apply Hsup2L. destruct Hsup as [HsupUB _].
    apply iteration_chain_upper_bound_im_f; auto.
  - destruct Hsup as [HsupUB HsupL]. apply HsupL.
    apply iteration_chain_upper_bound_f; auto.
* intros y Hy. destruct Hsup as [HsupUB HsupL]. apply HsupL; trivial.
  apply fixed_point_is_sup_chain; trivial.
Qed.
