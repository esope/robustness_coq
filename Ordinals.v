(** Some results on countable ordinals. Inspired from notes of Peter Hancock.

(Ordinal-theoretic) Proof Theory. Course notes from Midlands Graduate School, 2008.

http://personal.cis.strath.ac.uk/~ph/

http://events.cs.bham.ac.uk/mgs2008/notes/proofTheory.pdf

Also inspired by Martijn Vermaat's Coq development.

http://martijn.vermaat.name/master-project/
*)

Require Import RelationClasses.
Require Import FunctionalExtensionality.

(** * Countable ordinals, also known as Brouwer ordinals. *)
Inductive Ord : Type :=
 | O_Ord : Ord
 | S_Ord : Ord -> Ord
 | lim_Ord : (nat -> Ord) -> Ord.

Fixpoint nat_to_ord (n: nat) : Ord :=
  match n with
    | O => O_Ord
    | S n => S_Ord (nat_to_ord n)
  end.

Definition ord_omega : Ord := lim_Ord nat_to_ord.

(** * Ordering on countable ordinals. *)

(** Predecessor. *)
Fixpoint ord_pred_type (b: Ord) : Type :=
  match b with
    | O_Ord => False
    | S_Ord b' => (unit + ord_pred_type b')%type
    | lim_Ord bs => { n: nat & ord_pred_type (bs n) }
  end.

Fixpoint ord_pred (b: Ord) (T: ord_pred_type b) : Ord :=
  match b, T with
    | O_Ord, _ => match T with end
    | S_Ord b', inl _ => b'
    | S_Ord b', inr T' => ord_pred b' T'
    | lim_Ord bs, existT n T' => ord_pred (bs n) T'
  end.

(** Ordering. *)
Fixpoint ord_leq (a b: Ord) : Prop :=
  match a with
    | O_Ord => True
    | S_Ord a' => exists t : ord_pred_type b, ord_leq a' (ord_pred b t)
    | lim_Ord as' => forall n, ord_leq (as' n) b
  end.

(** Strict ordering. *)
Definition ord_eq a b := ord_leq a b /\ ord_leq b a.

Definition ord_le (a b: Ord) : Prop := exists t, ord_leq a (ord_pred b t).

(** ** Preorder. *)

Lemma ord_leq_pred_r :
  forall a b t,
    ord_leq a (ord_pred b t) ->
    ord_leq a b.
Proof.
intros a; induction a; intros b t Hleq; simpl in *; trivial.
* destruct Hleq as [t' Hleq]. eauto.
* intro n. eauto.
Qed.

Lemma ord_leq_lim_r :
  forall a f n,
    ord_leq a (f n) ->
    ord_leq a (lim_Ord f).
Proof.
intros a f n H. induction a; simpl in *; auto.
* destruct H as [t Hleq]. exists (existT _ n t). auto.
Qed.

Instance ord_leq_PreOrder : PreOrder ord_leq.
Proof.
constructor.
* intro a; induction a; simpl; auto.
  + exists (inl _ tt). assumption.
  + intro n. eapply ord_leq_lim_r; eauto.
* intros a. induction a; intros b c Hab Hbc.
  + simpl. trivial.
  + simpl. destruct Hab as [t Hab].
    generalize dependent c. induction b; intros c Hbc; simpl in *.
    - destruct t.
    - destruct Hbc as [t' Hbc].
      destruct t. eauto.
      apply ord_leq_pred_r in Hbc. eauto.
    - destruct t as [n Hn]. eauto.
  + simpl. intro n. eauto.
Qed.

Instance ord_le_Transitive : Transitive ord_le.
Proof.
intros a b c [tb Hab] [tc Hac].
exists tc. transitivity b; trivial.
eapply ord_leq_pred_r; eassumption.
Qed.

(** ** Other results on [ord_leq]. *)
Lemma ord_leq_O_r :
  forall a b,
    ord_leq a O_Ord ->
    ord_leq a b.
Proof.
intros a; induction a; intros b Hleq; simpl in *; trivial.
* destruct Hleq as [[] _].
* intro n. auto.
Qed.

Lemma ord_leq_pred_l :
  forall a b t,
    ord_leq a b ->
    ord_leq (ord_pred a t) b.
Proof.
intros a; induction a; intros b t Hleq; simpl in *; trivial.
* destruct t.
* destruct Hleq as [t' Hleq]. destruct t.
  + eapply ord_leq_pred_r; eassumption.
  + apply IHa. eapply ord_leq_pred_r; eassumption.
* destruct t as [n Hn]. auto.
Qed.

Lemma ord_leq_S_l :
  forall a b,
    ord_leq (S_Ord a) b ->
    ord_leq a b.
Proof.
intros a; induction a; intros b Hleq; simpl in *; trivial.
* destruct Hleq as [t Hleq]. eauto.
* destruct Hleq as [t Hleq]. eauto.
Qed.

Lemma ord_leq_S_r :
  forall a b,
    ord_leq a b ->
    ord_leq a (S_Ord b).
Proof.
intros a; induction a; intros b Hleq; simpl in *; trivial.
* destruct Hleq as [t Hleq].
  exists (inr _ t). trivial.
* auto.
Qed.

Lemma ord_leq_SS_inv :
  forall a b,
    ord_leq (S_Ord a) (S_Ord b) ->
    ord_leq a b.
Proof.
intro a; induction a; intros b Hleq; simpl in *; trivial.
* destruct Hleq as [t Hleq]. destruct t as [t | t].
  + assumption.
  + exists t. destruct Hleq as [t' Hleq].
    apply IHa. exists (inr _ t'). assumption.
* intro n. apply H. destruct Hleq as [t Hleq].
  exists t. auto.
Qed.

Lemma ord_leq_SS :
  forall a b,
    ord_leq a b ->
    ord_leq (S_Ord a) (S_Ord b).
Proof.
intro a; induction a; intros b Hleq; simpl in *.
* exists (inl _ tt). trivial.
* destruct Hleq as [t Hleq].
  destruct (IHa _ Hleq) as [t' Hleq'].
  destruct t' as [t' | t'].
  + exists (inl _ tt). eauto.
  + exists (inr _ t). eauto.
* exists (inl _ tt). trivial.
Qed.

Lemma ord_leq_lim_l :
  forall a f n,
    ord_leq (lim_Ord f) a ->
    ord_leq (f n) a.
Proof.
intros a f n H. simpl in H. trivial.
Qed.

Lemma ord_leq_S_pred :
  forall o t,
    ord_leq (S_Ord (ord_pred o t)) o.
Proof.
intros o t.
induction o; simpl in *.
* destruct t.
* destruct t as [t | t].
  + exists (inl _ t). reflexivity.
  + destruct (IHo t) as [t' H].
    exists (inr _ t'). assumption.
* destruct t as [n Hn].
  destruct (H n Hn) as [t' H'].
  exists (existT _ n t'). assumption.
Qed.

(** * Arithmetic on countable ordinals. *)
(** ** Addition. *)
Fixpoint ord_plus (a b: Ord) : Ord :=
  match b with
    | O_Ord => a
    | S_Ord b' => S_Ord (ord_plus a b')
    | lim_Ord bs => lim_Ord (fun n => ord_plus a (bs n))
  end.

(** ** Multiplication. *)
Fixpoint ord_mult (a b: Ord) : Ord :=
  match b with
    | O_Ord => O_Ord
    | S_Ord b' => ord_plus (ord_mult a b') a
    | lim_Ord bs => lim_Ord (fun n => ord_mult a (bs n))
  end.

(** ** Exponentiation. *)
Fixpoint ord_exp (a b: Ord) : Ord :=
  match b with
    | O_Ord => S_Ord O_Ord
    | S_Ord b' => ord_mult (ord_exp a b') a
    | lim_Ord bs => lim_Ord (fun n => ord_exp a (bs n))
  end.

(** ** Some lemmas on ordinal arithmetic. *)
(** *** Laws on addition. *)

Lemma ord_plus_O_r : forall a, ord_plus a O_Ord = a.
Proof.
intro a. reflexivity.
Qed.

Lemma ord_plus_O_l : forall a, ord_plus O_Ord a = a.
Proof.
intro a. induction a; simpl; trivial.
* congruence.
* f_equal. extensionality n. trivial.
Qed.

Lemma ord_plus_S_r : forall a b, ord_plus a (S_Ord b) = S_Ord (ord_plus a b).
Proof.
intros a b. reflexivity.
Qed.

Lemma ord_plus_assoc :
  forall a b c, ord_plus a (ord_plus b c) = ord_plus (ord_plus a b) c.
Proof.
intros a b c.
generalize dependent b. generalize dependent a.
induction c; simpl in *; intros a b; trivial.
* congruence.
* f_equal. extensionality n. trivial.
Qed.
