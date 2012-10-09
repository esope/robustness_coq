Require Import MyTactics.
Require Export Lattice.
Require Export NatLattice.

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

Lemma n_iter_ascending_1 {T} `{L: PreLattice T} :
  forall zero (f: T -> T),
    monotone f ->
    leq zero (f zero) ->
    forall n,
      leq (n_iter f n zero) (n_iter f (S n) zero).
Proof.
intros zero f Hf Hzero n.
simpl. apply n_iter_monotone_zero; trivial.
Qed.

Lemma n_iter_ascending_n_plus_m {T} `{L: PreLattice T} :
  forall zero (f: T -> T), monotone f -> leq zero (f zero) ->
  forall n m, leq (n_iter f n zero) (n_iter f (n + m) zero).
Proof.
Require Omega.
intros zero f H Hzero n m. destruct m.
* replace (n + 0) with n by omega. reflexivity.
* induction m.
  - replace (n + 1) with (S n) by omega. apply n_iter_ascending_1; trivial.
  - transitivity (n_iter f (n + S m) zero). trivial.
    replace (n + S (S m)) with (S (n + S m)) by omega.
    apply n_iter_ascending_1; trivial.
Qed.

Lemma n_iter_monotone {T} `{L: PreLattice T} :
  forall zero (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
    monotone (fun n => n_iter f n zero).
Proof.
intros zero f Hzero Hf n1 n2 H.
replace n2 with (n1 + (n2 - n1)) by auto with arith.
apply n_iter_ascending_n_plus_m; trivial.
Qed.

Definition iteration_chain {T} `{PreLattice T} (zero: T) (f: T -> T) :=
  fun x => exists n, equiv x (n_iter f n zero).

Lemma iteration_chain_directed {T} `{PreLattice T} :
  forall (zero: T) (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
    directed (iteration_chain zero f).
Proof.
intros zero f Hzero Hf. apply (monotone_seq_directed 0).
apply n_iter_monotone; trivial.
Qed.

Lemma n_iter_upper_bound_f {T} `{L: PreLattice T} :
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

Lemma iteration_chain_upper_bound_f {T} `{L: PreLattice T} :
  forall zero (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
  forall b,
    leq zero b ->
    is_upper_bound (iteration_chain zero f) b ->
    is_upper_bound (iteration_chain zero f) (f b).
Proof.
intros zero f Hzero Hf b Hb H x [n Hx]. rewrite Hx.
apply n_iter_upper_bound_f; trivial.
* transitivity (f zero); trivial. apply Hf. trivial.
* intro n'. apply H. exists n'. reflexivity.
Qed.

Lemma iteration_chain_upper_bound_im_f {T} `{L: PreLattice T} :
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

Definition is_fixed_point {T} `{L : Setoid T} (f : T -> T) (x : T) :=
  equiv (f x) x.

Lemma fixed_point_is_sup_chain {T} `{L : PreLattice T} :
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

(** Kleene least fixed point theorem, generalized to an arbitraty starting point. *)
Theorem generalized_kleene_fixed_point {T order}
        `{L: CompletePreLattice T order} :
  forall zero (f: T -> T),
    leq zero (f zero) ->
    continuous f ->
    exists sup,
      is_sup (iteration_chain zero f) sup
      /\ is_fixed_point f sup
      /\ (forall y, leq zero y -> is_fixed_point f y -> leq sup y).
Proof.
intros zero f Hzero Hf_continuous.
assert (monotone f) as Hf_monotone by (apply continuous_monotone; trivial).
pose (chain := iteration_chain zero f).
pose (HchainDirected := iteration_chain_directed zero f Hzero Hf_monotone).
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
    apply HsupUB. exists 0. reflexivity.
* intros y Hzeroy Hy. destruct Hsup as [HsupUB HsupL]. apply HsupL; trivial.
  apply fixed_point_is_sup_chain; trivial.
Qed.

Lemma iterated_fun_continuous {T order} {L: PreLattice T order}:
  forall (zero: T) (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
    continuous (fun (n: nat) => n_iter f n zero).
Proof.
intros zero f Hzero Hf P nsup Hdir Hsup.
pose (g := fun (n: nat) => n_iter f n zero).
fold g. exists (g nsup). split.
* split.
  + intros R' HR'.
    destruct HR' as [n0 [HPn0 [Hn0R' HR'n0]]].
    transitivity (g n0); trivial.
    destruct Hsup as [HUB HLUB].
    specialize (HUB n0 HPn0).
    unfold g.
    apply (n_iter_monotone zero f Hzero Hf n0 nsup HUB).
  + intros R' HR'. apply HR'.
    exists nsup. split.
    - apply not_empty_is_sup_in; trivial. destruct Hdir; assumption.
    - reflexivity.
* reflexivity.
Qed.

(** * Specialization of the above function to <<zero = bottom>>. *)
Module Bottom.

Lemma n_iter_monotone {T} `{L: BottomPreLattice T} :
  forall (f: T -> T),
    monotone f ->
    monotone (fun n => n_iter f n bottom).
Proof.
intros f H. apply n_iter_monotone; trivial.
apply bottom_minimum.
Qed.

Lemma iteration_chain_directed {T} `{L: BottomPreLattice T} :
  forall (f: T -> T),
    monotone f ->
    directed (iteration_chain bottom f).
Proof.
intros f H. apply iteration_chain_directed; trivial.
apply bottom_minimum.
Qed.

Lemma n_iter_upper_bound_f {T} `{L: BottomPreLattice T} :
  forall (f: T -> T),
    monotone f ->
    forall b,
      (forall n, leq (n_iter f n bottom) b) ->
      forall n, leq (n_iter f n bottom) (f b).
Proof.
intros f H b H0 n.
apply n_iter_upper_bound_f; auto using bottom_minimum.
Qed.

Lemma iteration_chain_upper_bound_f {T} `{L: BottomPreLattice T} :
  forall (f: T -> T),
    monotone f ->
    forall b,
      is_upper_bound (iteration_chain bottom f) b ->
      is_upper_bound (iteration_chain bottom f) (f b).
Proof.
intros f H b H0. apply iteration_chain_upper_bound_f; auto using bottom_minimum.
Qed.

Lemma iteration_chain_upper_bound_im_f {T} `{L: BottomPreLattice T} :
  forall (f: T -> T),
    monotone f ->
    forall b,
      is_upper_bound (iteration_chain bottom f) b ->
      is_upper_bound (im f (iteration_chain bottom f)) b.
Proof.
intros f H b H0.
apply iteration_chain_upper_bound_im_f; auto using bottom_minimum.
Qed.

Lemma fixed_point_is_sup_chain {T} `{L : BottomPreLattice T} :
  forall (f: T -> T),
    monotone f ->
    forall x,
      is_fixed_point f x ->
      is_upper_bound (iteration_chain bottom f) x.
Proof.
intros f H x H0.
apply fixed_point_is_sup_chain; auto using bottom_minimum.
Qed.

(** Kleene least fixed point theorem. *)
Theorem kleene_fixed_point {T order}
        `{L: CompletePreLattice T order} `{B: BottomPreLattice T order}:
  forall (f: T -> T),
    continuous f ->
    exists sup,
      is_sup (iteration_chain bottom f) sup
      /\ is_fixed_point f sup
      /\ (forall y, is_fixed_point f y -> leq sup y).
Proof.
intros f H.
pose proof
     (generalized_kleene_fixed_point bottom f (bottom_minimum (f bottom)) H)
  as HKleene.
destruct HKleene as [sup [Hsup [Hfp Hlfp]]].
exists sup. splits; auto.
* intros y Hy. apply Hlfp; trivial. apply bottom_minimum.
Qed.

Lemma iterated_fun_continuous {T order} {L: BottomPreLattice T order}:
  forall (f: T -> T),
    monotone f ->
    continuous (fun (n: nat) => n_iter f n bottom).
Proof.
intros f H.
apply iterated_fun_continuous; auto using bottom_minimum.
Qed.

End Bottom.
