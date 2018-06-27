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
  | H1 : ?t = Some ?x1, H2 : ?t = Some ?x2 |- _ =>
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
