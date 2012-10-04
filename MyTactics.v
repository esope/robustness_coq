Ltac splits :=
  match goal with
    | |- _ /\ _ => split; splits
    | _ => idtac
  end.

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
