Require Import MyTactics.
Require Export Lattice.
Require Export NatLattice.

Fixpoint n_iter {T} (f: T -> T) (n : nat) (zero : T) : T :=
match n with
| O => zero
| S n => n_iter f n (f zero)
end.

Lemma n_iter_correct {T} :
  forall (f : T -> T) n zero, n_iter f (S n) zero = f (n_iter f n zero).
Proof.
intros f n. induction n; intros x.
reflexivity.
simpl. rewrite <- IHn. reflexivity.
Qed.

Lemma f_n_iter {T} :
  forall (f: T -> T) n zero,
    f (n_iter f n zero) = n_iter f n (f zero).
Proof.
intros f n zero. destruct n.
* reflexivity.
* transitivity (f (n_iter f n (f zero))). reflexivity.
  rewrite n_iter_correct. reflexivity.
Qed.

Lemma n_iter_monotone_zero {T leq} `{L: PreOrder T leq} :
  forall (f: T -> T), monotone f -> forall n, monotone (n_iter f n).
Proof.
intros f Hf n. induction n.
* unfold monotone; auto.
* intros x y Hxy. repeat rewrite n_iter_correct. auto.
Qed.

Lemma n_iter_ascending_1 {T leq} `{L: PreOrder T leq} :
  forall zero (f: T -> T),
    monotone f ->
    leq zero (f zero) ->
    forall n,
      leq (n_iter f n zero) (n_iter f (S n) zero).
Proof.
intros zero f Hf Hzero n.
simpl. apply n_iter_monotone_zero; trivial.
Qed.

Lemma n_iter_ascending_n_plus_m {T leq} `{L: PreOrder T leq} :
  forall zero (f: T -> T), monotone f -> leq zero (f zero) ->
  forall n m, leq (n_iter f n zero) (n_iter f (n + m) zero).
Proof.
Require Omega.
intros zero f Hf Hzero n m. destruct m.
* replace (n + 0) with n by omega. reflexivity.
* induction m.
  - replace (n + 1) with (S n) by omega. apply n_iter_ascending_1; trivial.
  - transitivity (n_iter f (n + S m) zero). trivial.
    replace (n + S (S m)) with (S (n + S m)) by omega.
    apply n_iter_ascending_1; trivial.
Qed.

Lemma n_iter_monotone {T leq} `{L: PreOrder T leq} :
  forall zero (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
    monotone (fun n => n_iter f n zero).
Proof.
intros zero f Hzero Hf n1 n2 Hn.
replace n2 with (n1 + (n2 - n1)) by auto with arith.
apply n_iter_ascending_n_plus_m; trivial.
Qed.

Definition iteration_chain {T leq} `{PreOrder T leq} (zero: T) (f: T -> T) :=
  fun x => exists n, equiv x (n_iter f n zero).

Lemma iteration_chain_sup_directed {T leq} `{PreOrder T leq} :
  forall (zero: T) (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
    sup_directed (iteration_chain zero f).
Proof.
intros zero f Hzero Hf. apply (monotone_seq_sup_directed 0).
apply n_iter_monotone; trivial.
Qed.

Lemma n_iter_upper_bound_f {T leq} `{L: PreOrder T leq} :
  forall zero (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
    forall b,
      leq zero (f b) ->
      (forall n, leq (n_iter f n zero) b) ->
      forall n, leq (n_iter f n zero) (f b).
Proof.
intros zero f Hzero Hf b Hb H n. induction n.
assumption.
rewrite n_iter_correct. auto.
Qed.

Lemma iteration_chain_upper_bound_f {T leq} `{L: PreOrder T leq} :
  forall zero (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
  forall b,
    leq zero b ->
    is_upper_bound (iteration_chain zero f) b ->
    is_upper_bound (iteration_chain zero f) (f b).
Proof.
intros zero f Hzero Hf b Hb HUB x [n Hx]. rewrite Hx.
apply n_iter_upper_bound_f; trivial.
* transitivity (f zero); trivial. apply Hf. trivial.
* intro n'. apply HUB. exists n'. reflexivity.
Qed.

Lemma iteration_chain_upper_bound_im_f {T leq} `{L: PreOrder T leq} :
  forall zero (f: T -> T),
    monotone f ->
    forall b,
      is_upper_bound (iteration_chain zero f) b ->
      is_upper_bound (im f (iteration_chain zero f)) b.
Proof.
intros zero f Hf b H. intros y [x [[n Hx] Heq]]. rewrite Heq.
apply H. exists (S n). rewrite n_iter_correct.
apply monotone_equiv_compat; auto.
Qed.

Lemma fixed_point_is_upper_bound_chain {T leq} `{L : PreOrder T leq} :
  forall zero (f: T -> T),
    monotone f ->
    forall x,
      leq zero x ->
      is_fixed_point f x ->
      is_upper_bound (iteration_chain zero f) x.
Proof.
intros zero f Hf x Hzerox Hx y [n Hy].
generalize dependent y. induction n; intros y Hy.
* rewrite Hy. assumption.
* rewrite Hy. rewrite n_iter_correct.
  unfold is_fixed_point in Hx. rewrite <- Hx.
  apply Hf. apply IHn. reflexivity.
Qed.

Lemma fixed_point_above_n_iter {T leq} `{L : PreOrder T leq} :
  forall zero (f: T -> T),
    monotone f ->
    forall x,
      leq zero x ->
      is_fixed_point f x ->
      forall n,
      leq (n_iter f n zero) x.
Proof.
intros zero f Hf x Hzerox Hx n.
apply (fixed_point_is_upper_bound_chain zero f Hf x Hzerox Hx).
exists n. reflexivity.
Qed.
