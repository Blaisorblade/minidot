Require Import tactics.
Require Export SfLib.

Definition id := nat.

Fixpoint indexr {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (beq_nat n (length l')) then Some a else indexr n l'
  end.

Hint Unfold indexr.
Hint Unfold length.

Ltac beq_nat :=
  match goal with
  | H : (?a =? ?b) = true |- _ => try eapply beq_nat_true in H
  | H : (?a =? ?b) = false |- _ => try eapply beq_nat_false in H
  end.

Lemma indexr_max : forall X vs i (T: X),
                       indexr i vs = Some T ->
                       i < length vs.
Proof.
  induction vs; intros * H; inverse H; simpl; repeat case_match;
    beq_nat; subst;
      try assert (i < length vs) by eauto 2; eauto.
Qed.
Hint Resolve indexr_max.
