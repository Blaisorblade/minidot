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

Lemma indexr_succ_wk: forall {X} i (G G': list X) r, indexr i G = Some r -> indexr (i + length G') (G ++ G') = Some r.
Proof.
  intros; induction G; simpl in *; try discriminate;
  rewrite app_length; repeat better_case_match_ex; eauto; omega.
Qed.

(** Simplifies next proof. *)
Lemma indexr_fail_eq: forall {X} i (G: list X), (indexr i G = None) <-> (i >= length G).
Proof.
  intros.
  split; intros; gen i; induction G; simpl; intros; eauto.
  - better_case_match_ex; assert (i >= length G) by eauto; omega.
  - better_case_match_ex; eauto 2; omega.
Qed.

Lemma indexr_fail_wk: forall {X} i (G G': list X), indexr i G = None -> indexr (i + length G') (G ++ G') = None.
Proof.
  (* Really manual proof: *)
  intros * H.
  (** Translate the problem to an inequality on lengths. *)
  eapply indexr_fail_eq; eapply indexr_fail_eq in H.
  (** Then solve it. *)
  rewrite app_length; omega.
Qed.

Lemma indexr_wk: forall {X} i (G G': list X) r, indexr i G = r -> indexr (i + length G') (G ++ G') = r.
  destruct r; eauto using indexr_succ_wk, indexr_fail_wk. Qed.
Hint Resolve indexr_wk.

Lemma indexr_wk_eq: forall {X} i (G G': list X), indexr i G = indexr (i + length G') (G ++ G').
  intros; erewrite indexr_wk; eauto.
Qed.
