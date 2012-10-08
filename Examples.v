(** * Examples. *)
(** ** Example 1 from Section 3. *)
Require Import Bool.

Record state :=
{ time : bool
; high : bool
; password : bool
; query : bool
; result : bool
}.

(** The step function of the system *)
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

(** The relation that describes the execution of the system. *)
Definition exec : relation state :=
  fun s1 s2 => s2 = s1 \/ s2 = step s1.

Lemma exec_refl : forall s, exec s s.
Proof.
intro s. left. reflexivity.
Qed.

Definition password_checker : sys state :=
  {| next := exec; next_refl := exec_refl |}.

(** The observation that the observer is interested in. *)
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

(** For the following lemma, it is crucial that password and query
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

(** The traces of password_checker are of two possible kinds. *)
Lemma stutter_password_checker (R: relation state) {E: Equivalence R}:
  forall t : trace password_checker,
    stutter_equiv
      (view R t)
      (view R (trace_one password_checker (hd t)))
    \/ stutter_equiv
         (view R t)
         (view R (trace_step (hd t))).
Proof.
intros [l Hl]. induction l.
* destruct Hl.
* destruct l as [| b l].
  - clear IHl. left. reflexivity.
  - simpl. unfold hd in IHl. destruct Hl as [Hab Hbl].
    specialize (IHl Hbl). destruct IHl as [IHl | IHl].
    + { unfold view in IHl. simpl in IHl. destruct Hab as [Hab | Hab]; subst b.
        * left. apply stutter_left. assumption.
        * right. apply stutter_same. assumption.
      }
    + {  unfold view in IHl. simpl in IHl. destruct Hab as [Hab | Hab]; subst b.
        * right. apply stutter_left. assumption.
        * right. apply stutter_same.
          transitivity (view R (trace_step (step a))).
          + assumption.
          + unfold trace_step. unfold view. simpl. rewrite <- step_projection.
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
  specialize (Hss' (view R t)).
  destruct Hss' as [v' [[t0' [Hv' Ht0's']] Htt0']].
  { exists t. split; reflexivity. }
  subst v'.
  assert (In (step s') (proj1_sig t0')).
  { destruct (stutter_password_checker R t0') as [H | H].
    * exfalso.
      eapply (time_false_not_R_step s); trivial.
      assert (forall a, In a (proj1_sig t) -> R a (hd t0')) as Haux.
      { intros a Ha.
        assert (In (R a) (view R t)). { apply in_map. assumption. }
        assert (In (R a) (view R (trace_one password_checker (hd t0')))) as HR.
        { apply (stutter_equiv_in (view R t)); trivial.
          transitivity (view R t0'); trivial. }
        destruct HR as [HR | HR].
        + rewrite <- HR. apply class_refl.
        + exfalso. simpl in HR. assumption.
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
    destruct (included_view_R _ _ _ Ht0't _ H) as [s1 [Hs1 Hs's1]].
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
  compute in Hts. subst a. simpl_ctx.
  apply stutter_one_stutter_view; trivial.
- destruct t as [[| a l] Hl]; [destruct Hl |].
  compute in Hts. subst a. simpl_ctx.
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
      exists (view R t'). split.
      + exists t'. split; reflexivity.
      + split.
        - intros t0 Ht0. exists t0.
          { split.
            * transitivity (exist _ _ Hl); trivial.
              symmetry.
              unfold t'. simpl_view. split; trivial.
              inversion Heq; subst.
              apply repeat_two_same_view; trivial.
            * reflexivity.
          }
        - intros t0 Ht0. exists t0.
          { split.
            * transitivity t'; trivial.
              unfold t'. simpl_view. split; trivial.
              inversion Heq; subst.
              apply repeat_two_same_view; trivial.
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

Lemma password_checker_obs_eq_iff :
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

(** TODO: rest of the examples. *)
