Require Import MyTactics.
Require Export Lattice.
Require Export NatLattice.

(** * Iteration of a function over natural numbers. *)
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

Definition iteration_chain {T leq} `{PreOrder T leq} (zero: T) (f: T -> T) :=
  fun x => exists n, x = n_iter f n zero.

(** * Ascending chains. *)
Module Ascending.

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
intros zero f Hf Hzero n m. destruct m.
* replace (n + 0) with n by omega. reflexivity.
* induction m.
  - replace (n + 1) with (S n) by omega. apply n_iter_ascending_1; trivial.
  - transitivity (n_iter f (n + S m) zero); trivial.
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
congruence.
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

Lemma iterated_fun_sup_continuous {T leq} {L: PreOrder leq}:
  forall (zero: T) (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
    sup_continuous (fun (n: nat) => n_iter f n zero).
Proof.
intros zero f Hzero Hf P nsup Hdir Hsup.
pose (g := fun (n: nat) => n_iter f n zero).
fold g. exists (g nsup). split.
* split.
  + intros R' HR'.
    destruct HR' as [n0 [HPn0 Heq]]. subst.
    transitivity (g n0). reflexivity.
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

(** ** Specialization of the above function to [zero = bottom]. *)
Module Bottom.

Lemma n_iter_monotone {T leq} `{L: PreOrder T leq} `{HasBottom T leq}:
  forall (f: T -> T),
    monotone f ->
    monotone (fun n => n_iter f n bottom).
Proof.
intros f Hf. apply n_iter_monotone; trivial.
apply bottom_minimum.
Qed.

Lemma iteration_chain_sup_directed {T leq} `{L: PreOrder T leq} `{HasBottom T leq} :
  forall (f: T -> T),
    monotone f ->
    sup_directed (iteration_chain bottom f).
Proof.
intros f Hf. apply iteration_chain_sup_directed; trivial.
apply bottom_minimum.
Qed.

Lemma n_iter_upper_bound_f {T leq} `{L: PreOrder T leq} `{HasBottom T leq} :
  forall (f: T -> T),
    monotone f ->
    forall b,
      (forall n, leq (n_iter f n bottom) b) ->
      forall n, leq (n_iter f n bottom) (f b).
Proof.
intros f Hf b H0 n.
apply n_iter_upper_bound_f; auto; apply bottom_minimum.
Qed.

Lemma iteration_chain_upper_bound_f {T leq} `{L: PreOrder T leq} `{HasBottom T leq} :
  forall (f: T -> T),
    monotone f ->
    forall b,
      is_upper_bound (iteration_chain bottom f) b ->
      is_upper_bound (iteration_chain bottom f) (f b).
Proof.
intros f Hf b H0.
apply iteration_chain_upper_bound_f; auto; apply bottom_minimum.
Qed.

Lemma iteration_chain_upper_bound_im_f {T leq} `{L: PreOrder T leq} `{HasBottom T leq} :
  forall (f: T -> T),
    monotone f ->
    forall b,
      is_upper_bound (iteration_chain bottom f) b ->
      is_upper_bound (im f (iteration_chain bottom f)) b.
Proof.
intros f Hf b H0.
apply iteration_chain_upper_bound_im_f; auto using bottom_minimum.
Qed.

Lemma fixed_point_is_upper_bound_chain {T leq} `{L: PreOrder T leq} `{HasBottom T leq} :
  forall (f: T -> T),
    monotone f ->
    forall x,
      is_fixed_point f x ->
      is_upper_bound (iteration_chain bottom f) x.
Proof.
intros f Hf x H0.
apply fixed_point_is_upper_bound_chain; auto; apply bottom_minimum.
Qed.

Lemma iterated_fun_sup_continuous {T leq} {L: PreOrder leq}
      `{HasBottom T leq} :
  forall (f: T -> T),
    monotone f ->
    sup_continuous (fun (n: nat) => n_iter f n bottom).
Proof.
intros f Hf.
apply iterated_fun_sup_continuous; auto; apply bottom_minimum.
Qed.

End Bottom.

End Ascending.

(** * Descending chains. *)
Module Descending.

Lemma n_iter_descending_1 {T leq} `{L: PreOrder T leq} :
  forall zero (f: T -> T),
    monotone f ->
    leq (f zero) zero ->
    forall n,
      leq (n_iter f (S n) zero) (n_iter f n zero).
Proof.
intros zero f Hf Hzero n.
simpl. apply n_iter_monotone_zero; trivial.
Qed.

Lemma n_iter_descending_n_plus_m {T leq} `{L: PreOrder T leq} :
  forall zero (f: T -> T), monotone f -> leq (f zero) zero ->
  forall n m, leq (n_iter f (n + m) zero) (n_iter f n zero).
Proof.
intros zero f Hf Hzero n m. destruct m.
* replace (n + 0) with n by omega. reflexivity.
* induction m.
  - replace (n + 1) with (S n) by omega. apply n_iter_descending_1; trivial.
  - transitivity (n_iter f (n + S m) zero); trivial.
    replace (n + S (S m)) with (S (n + S m)) by omega.
    apply n_iter_descending_1; trivial.
Qed.

Lemma n_iter_anti_monotone {T leq} `{L: PreOrder T leq} :
  forall zero (f: T -> T),
    leq (f zero) zero ->
    monotone f ->
    anti_monotone (fun n => n_iter f n zero).
Proof.
intros zero f Hzero Hf n2 n1 Hn.
replace n2 with (n1 + (n2 - n1)) by auto with arith.
apply n_iter_descending_n_plus_m; trivial.
Qed.

Lemma iteration_chain_inf_directed {T leq} `{PreOrder T leq} :
  forall (zero: T) (f: T -> T),
    leq (f zero) zero ->
    monotone f ->
    inf_directed (iteration_chain zero f).
Proof.
intros zero f Hzero Hf. split.
* exists zero. exists 0. reflexivity.
* intros x y [n Hn] [m Hm]. subst. exists (n_iter f (max n m) zero).
  splits.
  + exists (max n m). reflexivity.
  + apply n_iter_anti_monotone; unfold flip; auto with arith.
  + apply n_iter_anti_monotone; unfold flip; auto with arith.
Qed.

Lemma n_iter_lower_bound_f {T leq} `{L: PreOrder T leq} :
  forall zero (f: T -> T),
    leq (f zero) zero ->
    monotone f ->
    forall b,
      leq (f b) zero ->
      (forall n, leq b (n_iter f n zero)) ->
      forall n, leq (f b) (n_iter f n zero).
Proof.
intros zero f Hzero Hf b Hb H n. induction n.
assumption.
rewrite n_iter_correct. auto.
Qed.

Lemma iteration_chain_lower_bound_f {T leq} `{L: PreOrder T leq} :
  forall zero (f: T -> T),
    leq (f zero) zero ->
    monotone f ->
  forall b,
    leq b zero ->
    is_lower_bound (iteration_chain zero f) b ->
    is_lower_bound (iteration_chain zero f) (f b).
Proof.
intros zero f Hzero Hf b Hb HLB x [n Hx]. rewrite Hx.
apply n_iter_lower_bound_f; trivial.
* transitivity (f zero); trivial. apply Hf. trivial.
* intro n'. apply HLB. exists n'. reflexivity.
Qed.

Lemma iteration_chain_lower_bound_im_f {T leq} `{L: PreOrder T leq} :
  forall zero (f: T -> T),
    monotone f ->
    forall b,
      is_lower_bound (iteration_chain zero f) b ->
      is_lower_bound (im f (iteration_chain zero f)) b.
Proof.
intros zero f Hf b H. intros y [x [[n Hx] Heq]]. rewrite Heq.
apply H. exists (S n). rewrite n_iter_correct.
congruence.
Qed.

Lemma fixed_point_is_lower_bound_chain {T leq} `{L : PreOrder T leq} :
  forall zero (f: T -> T),
    monotone f ->
    forall x,
      leq x zero ->
      is_fixed_point f x ->
      is_lower_bound (iteration_chain zero f) x.
Proof.
intros zero f Hf x Hzerox Hx y [n Hy].
generalize dependent y. induction n; intros y Hy.
* rewrite Hy. assumption.
* rewrite Hy. rewrite n_iter_correct.
  unfold is_fixed_point in Hx. rewrite <- Hx.
  apply Hf. apply IHn. reflexivity.
Qed.

Lemma fixed_point_below_n_iter {T leq} `{L : PreOrder T leq} :
  forall zero (f: T -> T),
    monotone f ->
    forall x,
      leq x zero ->
      is_fixed_point f x ->
      forall n,
      leq x (n_iter f n zero).
Proof.
intros zero f Hf x Hzerox Hx n.
apply (fixed_point_is_lower_bound_chain zero f Hf x Hzerox Hx).
exists n. reflexivity.
Qed.

(** ** Specialization of the above function to [zero = top]. *)
Module Top.

Lemma n_iter_anti_monotone {T leq} `{L: PreOrder T leq} `{HasTop T leq}:
  forall (f: T -> T),
    monotone f ->
    anti_monotone (fun n => n_iter f n top).
Proof.
intros f Hf. apply n_iter_anti_monotone; trivial.
apply top_maximum.
Qed.

Lemma iteration_chain_inf_directed {T leq} `{L: PreOrder T leq} `{HasTop T leq} :
  forall (f: T -> T),
    monotone f ->
    inf_directed (iteration_chain top f).
Proof.
intros f Hf. apply iteration_chain_inf_directed; trivial.
apply top_maximum.
Qed.

Lemma n_iter_lower_bound_f {T leq} `{L: PreOrder T leq} `{HasTop T leq} :
  forall (f: T -> T),
    monotone f ->
    forall b,
      (forall n, leq b (n_iter f n top)) ->
      forall n, leq (f b) (n_iter f n top).
Proof.
intros f Hf b H0 n.
apply n_iter_lower_bound_f; auto; apply top_maximum.
Qed.

Lemma iteration_chain_lower_bound_f {T leq} `{L: PreOrder T leq} `{HasTop T leq} :
  forall (f: T -> T),
    monotone f ->
    forall b,
      is_lower_bound (iteration_chain top f) b ->
      is_lower_bound (iteration_chain top f) (f b).
Proof.
intros f Hf b H0.
apply iteration_chain_lower_bound_f; auto; apply top_maximum.
Qed.

Lemma iteration_chain_lower_bound_im_f {T leq} `{L: PreOrder T leq} `{HasTop T leq} :
  forall (f: T -> T),
    monotone f ->
    forall b,
      is_lower_bound (iteration_chain top f) b ->
      is_lower_bound (im f (iteration_chain top f)) b.
Proof.
intros f Hf b H0.
apply iteration_chain_lower_bound_im_f; auto using top_maximum.
Qed.

Lemma fixed_point_is_lower_bound_chain {T leq} `{L: PreOrder T leq} `{HasTop T leq} :
  forall (f: T -> T),
    monotone f ->
    forall x,
      is_fixed_point f x ->
      is_lower_bound (iteration_chain top f) x.
Proof.
intros f Hf x H0.
apply fixed_point_is_lower_bound_chain; auto; apply top_maximum.
Qed.

End Top.

End Descending.
