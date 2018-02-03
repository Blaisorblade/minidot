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