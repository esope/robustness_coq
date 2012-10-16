Require Import RelationClasses.

(** * Iterated splits. *)
(** Version that does not unfold definitions. *)
Ltac splits :=
  match goal with
    | |- _ /\ _ => split; splits
    | _ => idtac
  end.

(** Version that does unfold definitions. *)
Ltac deep_splits :=
  match goal with
    | _ => split; deep_splits
    | _ => idtac
  end.

Module TestTactics.

Definition AND P Q := P /\ Q.

(* Testing splits *)
Goal forall (P:Prop), P -> (P /\ P) /\ (P /\ P).
intros P p.
splits. (* 4 goals *)
* trivial.
* trivial.
* trivial.
* trivial.
Qed.

Goal forall (P Q: Prop), P -> Q -> (AND P Q) /\ (P /\ Q).
intros P Q p q.
splits. (* 3 goals *)
* split; trivial.
* trivial.
* trivial.
Qed.

(* Testing deep_splits *)
Goal forall (P:Prop), P -> (P /\ P) /\ (P /\ P).
intros P p.
deep_splits; [trivial|trivial|trivial|trivial].
Qed.

Goal forall (P Q: Prop), P -> Q -> (AND P Q) /\ (P /\ Q).
intros P Q p q.
deep_splits. (* 4 goals *)
* trivial.
* trivial.
* trivial.
* trivial.
Qed.

End TestTactics.

(** * Useful Hints when dealing with [omega]. *)
Require Export Omega.
Hint Extern 3 (_ <= _) => first [omega | simpl; omega].
Hint Extern 3 (_ = _) => first [omega | simpl; omega].
Hint Extern 3 => exfalso; first [omega | simpl in *|-; omega].

(** Useful hints when dealing with equivalence relations. *)
Ltac equivalence_reflexivity :=
  match goal with
    | E: Equivalence ?R |- ?R _ _ => reflexivity
  end.
Hint Extern 3 => equivalence_reflexivity.
Hint Extern 3 (_ = _) => reflexivity.
