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

(* Without this lemma, proof search fails to complete the proof of indexr_max.
   Not intended to be used by hand. Reconsider using Hint Extern if this ever becomes a problem. *)
Lemma _lt_suc_proof_search_help: forall i j, i < j -> i < S j.
Proof. intros; omega. Qed.
Hint Resolve _lt_suc_proof_search_help.

Lemma indexr_max : forall X vs i (T: X),
                       indexr i vs = Some T ->
                       i < length vs.
Proof.
  induction vs; intros * H; inverse H; simpl; repeat case_match;
    beq_nat; subst; eauto 3.
Qed.
Hint Resolve indexr_max.

Lemma indexr_extend : forall X vs n x (T: X),
                       indexr n vs = Some T ->
                       indexr n (x::vs) = Some T.
Proof.
  intros * H; assert (n < length vs) by eauto;
    unfold indexr in *; rewrite H;
    assert (beq_nat n (length vs) = false) as -> by eauto with eq;
    reflexivity.
Qed.
