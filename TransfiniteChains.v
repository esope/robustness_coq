Require Import MyTactics.
Require Export Lattice.
Require Export Ordinals.

(* Transfinite iteration of a function. *)
Fixpoint trans_iter {T leq} `{JoinCompletePreLattice T leq}
         (f: T -> T) (o: Ord) (zero : T) : T :=
  match o with
    | O_Ord => zero
    | S_Ord o' => f (trans_iter f o' zero)
    | lim_Ord os =>
      let (sup, _) :=
          (join_complete (fun t : T => exists n, t = trans_iter f (os n) zero))
      in sup
  end.

Lemma trans_iter_monotone_zero {T leq} `{JoinCompletePreLattice T leq}
      (f: T -> T) (o: Ord):
  monotone f ->
  monotone (trans_iter f o).
Proof.
intros Hf x y Hxy. induction o.
* assumption.
* simpl. apply Hf. assumption.
* simpl.
  destruct
    (join_complete
       (fun t : T => exists n : nat, t = trans_iter f (o n) x))
    as [xsup [HxUB HxLUB]].
  destruct
    (join_complete
       (fun t : T => exists n : nat, t = trans_iter f (o n) y))
    as [ysup [HyUB HyLUB]].
  apply HxLUB.
  intros t [n Heq]. subst t.
  transitivity (trans_iter f (o n) y); trivial.
  apply HyUB. eauto.
Qed.

Lemma trans_iter_ascending_S {T leq} `{JoinCompletePreLattice T leq} :
  forall zero (f: T -> T),
    monotone f ->
    leq zero (f zero) ->
    forall o,
      leq (trans_iter f o zero) (trans_iter f (S_Ord o) zero).
Proof.
intros zero f Hf Hzero o. induction o; simpl; auto.
* destruct
    (join_complete
       (fun t : T => exists n : nat, t = trans_iter f (o n) zero))
    as [sup [HUB HLUB]].
  apply HLUB. intros t [n Heq]; subst t.
  transitivity (trans_iter f (S_Ord (o n)) zero); trivial.
  simpl. apply Hf. apply HUB. eauto.
Qed.

Lemma trans_iter_lower_bound {T leq} `{JoinCompletePreLattice T leq}:
  forall zero (f: T -> T) (o: Ord),
    leq zero (f zero) ->
    monotone f ->
    leq zero (trans_iter f o zero).
Proof.
intros zero f o Hzero Hf. induction o; simpl in *.
* reflexivity.
* transitivity (trans_iter f o zero); trivial.
  apply trans_iter_ascending_S; auto.
* destruct
    (join_complete
       (fun t : T => exists n : nat, t = trans_iter f (o n) zero))
    as [sup [HUB HLUB]].
  transitivity (trans_iter f (o 0) zero); trivial.
  apply HUB. eauto.
Qed.

Lemma trans_iter_S_pred {T leq} `{JoinCompletePreLattice T leq} :
  forall zero (f : T -> T),
    leq zero (f zero) ->
    monotone f ->
    forall o t,
      leq (trans_iter f (S_Ord (ord_pred o t)) zero) (trans_iter f o zero).
Proof.
induction o; simpl in *.
- destruct t.
- destruct t as [t | t]. reflexivity.
  transitivity (trans_iter f o zero). trivial.
  apply trans_iter_ascending_S; auto.
- destruct t as [n Hn].
  destruct
    (join_complete
       (fun t0 : T => exists n : nat, t0 = trans_iter f (o n) zero))
    as [sup [HUB HLUB]].
  transitivity (trans_iter f (o n) zero); trivial.
  apply HUB. eauto.
Qed.

Lemma trans_iter_monotone {T leq} `{JoinCompletePreLattice T leq}:
  forall zero (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
    monotone (fun o => trans_iter f o zero).
Proof.
intros zero f Hzero Hf o1. induction o1; intros o2 Hord; simpl in *.
* apply trans_iter_lower_bound; auto.
* destruct Hord as [t Hord].
  transitivity (trans_iter f (S_Ord (ord_pred o2 t)) zero).
  + simpl. apply Hf. auto.
  + apply trans_iter_S_pred; auto.
* destruct
    (join_complete
       (fun t0 : T => exists n : nat, t0 = trans_iter f (o n) zero))
    as [sup [HUB HLUB]].
  apply HLUB. intros t [n Heq]; subst t. auto.
Qed.

Definition trans_iteration_chain {T leq} `{JoinCompletePreLattice T leq}
           (zero: T) (f: T -> T) :=
  fun x => exists o, equiv x (trans_iter f o zero).

Lemma trans_iter_upper_bound_f {T leq} `{JoinCompletePreLattice T leq} :
  forall zero (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
    forall b,
      leq zero (f b) ->
      (forall o, leq (trans_iter f o zero) b) ->
      forall o, leq (trans_iter f o zero) (f b).
Proof.
intros zero f Hzero Hf b Hb Hleq o. induction o.
* assumption.
* simpl. auto.
* simpl.
  destruct
    (join_complete
       (fun t : T => exists n : nat, t = trans_iter f (o n) zero))
    as [sup [HUB HLUB]].
  apply HLUB. intros t [n Heq]; subst t. auto.
Qed.

Lemma trans_iteration_chain_upper_bound_f {T leq}
      `{JoinCompletePreLattice T leq} :
  forall zero (f: T -> T),
    leq zero (f zero) ->
    monotone f ->
  forall b,
    leq zero b ->
    is_upper_bound (trans_iteration_chain zero f) b ->
    is_upper_bound (trans_iteration_chain zero f) (f b).
Proof.
intros zero f Hzero Hf b Hb HUB x [o Hx]. rewrite Hx.
apply trans_iter_upper_bound_f; trivial.
* transitivity (f zero); trivial. apply Hf. trivial.
* intro o'. apply HUB. exists o'. reflexivity.
Qed.

Lemma trans_iteration_chain_upper_bound_im_f {T leq}
      `{JoinCompletePreLattice T leq} :
  forall zero (f: T -> T),
    monotone f ->
    forall b,
      is_upper_bound (trans_iteration_chain zero f) b ->
      is_upper_bound (im f (trans_iteration_chain zero f)) b.
Proof.
intros zero f Hf b HUB. intros y [x [[o Hx] Heq]]. rewrite Heq.
apply HUB. exists (S_Ord o).
transitivity (f (trans_iter f o zero)).
apply monotone_equiv_compat; auto.
reflexivity.
Qed.

Lemma fixed_point_is_upper_bound_chain {T leq} `{JoinCompletePreLattice T leq} :
  forall zero (f: T -> T),
    monotone f ->
    forall x,
      leq zero x ->
      is_fixed_point f x ->
      is_upper_bound (trans_iteration_chain zero f) x.
Proof.
intros zero f Hf x Hzerox Hx y [o Hy].
generalize dependent y. induction o; intros y Hy.
* rewrite Hy. assumption.
* rewrite Hy. simpl.
  unfold is_fixed_point in Hx. rewrite <- Hx.
  apply Hf. apply IHo. reflexivity.
* rewrite Hy. simpl.
  destruct
    (join_complete
       (fun t : T => exists n : nat, t = trans_iter f (o n) zero))
    as [sup [HUB HLUB]].
  apply HLUB. intros t [n Heq]; subst t.
  apply (H1 n). reflexivity.
Qed.

Lemma fixed_point_above_trans_iter {T leq} `{JoinCompletePreLattice T leq} :
  forall zero (f: T -> T),
    monotone f ->
    forall x,
      leq zero x ->
      is_fixed_point f x ->
      forall o,
      leq (trans_iter f o zero) x.
Proof.
intros zero f Hf x Hzerox Hx o.
apply (fixed_point_is_upper_bound_chain zero f Hf x Hzerox Hx).
exists o. reflexivity.
Qed.
