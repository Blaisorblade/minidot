Require Export Omega.
Require Export Program.
Require Export LibTactics.
Require Export SfLib.

Global Unset Transparent Obligations.
Remove Hints Bool.trans_eq_bool.

Ltac inverse H := (inversion H; subst).

Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.


(* From coq_stdpp *)
Ltac case_match :=
  match goal with
  | H : context [ match ?x with _ => _ end ] |- _ =>
    destruct x eqn:?
  |  |- context [ match ?x with _ => _ end ] =>
    destruct x eqn:?
  end.

(* Avoid case distinctions when we know the right case from the hypotheses.
   Otherwise, we end up with branches where the context says that ?x = A and ?x
   = B, with A and B incompatible, and must use discriminate to remove those
   branches. *)
Ltac better_case_match :=
  match goal with
  | H : context [ match ?x with _ => _ end ] , H1 : ?y = ?x |- _ =>
    rewrite <- H1 in H
  | H : context [ match ?x with _ => _ end ] , H1 : ?x = ?y |- _ =>
    rewrite H1 in H
  | H : context [ match ?x with _ => _ end ] |- _ =>
    destruct x eqn:?

  | H1 : ?y = ?x |- context [ match ?x with _ => _ end ] =>
    rewrite <- H1
  | H1 : ?x = ?y |- context [ match ?x with _ => _ end ] =>
    rewrite H1
  | |- context [ match ?x with _ => _ end ] =>
    destruct x eqn:?
  end.

(* Homegrown variants. *)
Ltac match_case_analysis :=
  repeat
    match goal with
    | H : context f [match ?x with _ => _ end] |- _ =>
      destruct x; try solve [inverse H]
    end.

Ltac match_case_analysis_eauto :=
  repeat
    match goal with
    | H : context f [match ?x with _ => _ end] |- _ =>
      destruct x; try solve [inverse H; eauto]
    end.

Ltac match_case_analysis_goal :=
  repeat
    match goal with
    | |- context f [match ?x with _ => _ end] =>
      destruct x
    end.

(* XXX stop defaulting to repeat above! *)
Ltac norepeat_match_case_analysis :=
  match goal with
  | H : context f [match ?x with _ => _ end] |- _ =>
    destruct x
  end.

Ltac norepeat_match_case_analysis_goal :=
    match goal with
    | |- context f [match ?x with _ => _ end] =>
      destruct x
    end.

Ltac match_case_analysis_remember :=
  match goal with
  | H : context f [match ?x with _ => _ end] |- _ =>
    let L := fresh
    in remember x as L; destruct L
  end.

(* Safer version of split; for use in automation. *)
Ltac split_conj :=
  repeat match goal with
  | |- _ /\ _ => split
  end.
(* stdpp name. *)
Ltac split_and := split_conj.


(* From Chlipala's tactics. *)
Ltac cinject H := injection H; clear H; intros; subst.

(* Apply automatically injection on hypotheses of form ?c args1 = ?c args2; if c
   is a constructor this will produce equalities args1_i = args2_i for all i.
   Since this tactic uses injection, it is more reliable than attempts based on
   inversion. *)
Ltac injectHyp :=
  match goal with
  | H : ?c _ _ _ _ _ _ = ?c _ _ _ _ _ _ |- _ => cinject H
  | H : ?c _ _ _ _ _ = ?c _ _ _ _ _ |- _ => cinject H
  | H : ?c _ _ _ _ = ?c _ _ _ _ |- _ => cinject H
  | H : ?c _ _ _ = ?c _ _ _ |- _ => cinject H
  | H : ?c _ _ = ?c _ _ |- _ => cinject H
  | H : ?c _ = ?c _ |- _ => cinject H
  | H : ?c = ?c |- _ => cinject H
  end.
Ltac injectHyps := repeat injectHyp.

Ltac optFuncs_det :=
  match goal with
  | H1 : ?t = ?x1, H2 : ?t = ?x2 |- _ =>
    let H := fresh "H" in
    rewrite H1 in H2; injectHyps
  end.

(* To use with repeat fequalSafe in automation.
   Unlike f_equal, won't try to prove a = b = c + d by a = c and b = d --- such
   equaities are omega's job. *)
Ltac fequalSafe :=
  match goal with
  | [ |- Some _ = Some _ ] => f_equal
  | [ |- (_, _) = (_, _) ] => f_equal
  end.

Hint Constructors option.
Hint Constructors list.

Hint Resolve ex_intro.

(* Hint Extern 1 (tsize_flat (open_rec _ _ _)) => autorewrite with core. *)
Ltac ineq_solver := autorewrite with core; simpl in *; omega.
Hint Unfold gt. (* Using gt or lt other shouldn't affect proof search! *)
Hint Unfold ge. (* Ditto *)
Hint Extern 5 (_ > _) => ineq_solver.
Hint Extern 5 (_ >= _) => ineq_solver.
Hint Extern 5 (_ < _) => ineq_solver.
Hint Extern 5 (_ <= _) => ineq_solver.
(* Hint Extern 5 (_ <> _) => ineq_solver. *)
Hint Extern 5 (_ <> _ :> nat) => ineq_solver.

Lemma inj_S: forall n, (n = S n) -> False.
  intros * H; induction n; discriminate || injection H; auto.
Qed.

Hint Resolve inj_S: eq.

Hint Resolve beq_nat_false: eq.
Hint Resolve false_beq_nat: eq.
Hint Resolve beq_nat_true: eq.

(** Support writing external hints for lemmas that must not be applied twice for a goal. *)
(* The usedLemma and un_usedLemma marker is taken from Crush.v (where they were called done and un_done). *)

(** Devious marker predicate to use for encoding state within proof goals *)
Definition usedLemma {T : Type} (x : T) := True.

(** After a round of application with the above, we will have a lot of junk [usedLemma] markers to clean up; hence this tactic. *)
Ltac un_usedLemma :=
  repeat match goal with
           | [ H : usedLemma _ |- _ ] => clear H
         end.
Ltac markUsed H := assert (usedLemma H) by constructor.
(* Ltac try_once lm := *)
(*     match goal with *)
(*     | H : usedLemma lm |- _ => fail 1 *)
(*     | _ => markUsed lm; eapply lm; eauto *)
(*     end; un_usedLemma. *)

Ltac try_once lm :=
    match goal with
    | H : usedLemma lm |- _ => fail 1
    | _ => markUsed lm; eapply lm
    end.
