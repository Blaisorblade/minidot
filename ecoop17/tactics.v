Require Export Omega.
Require Export Program.
Unset Transparent Obligations.

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

(* (* Try automatic inversion on hypotheses matching Some to Some, in a few variants. *)
(*  * I use these variants depending on the scenario; they are needed because no *)
(*  * inversion tactic is too robust. *)
(*  *) *)
(* Ltac inverse_some := *)
(*   (* Below, using inversion instead of inversion_clear reduces the *)
(*   danger of destroying information and producing false goals, but *)
(*   means that repeat inverse_some will loop! *) *)
(*   match goal with *)
(*   | H : Some ?x = Some ?y |- _ => inversion_clear H; subst *)
(*   end. *)
(* Ltac inverts_some := *)
(*   match goal with *)
(*   | H : Some ?x = Some ?y |- _ => inversion H; subst; clear H *)
(*   end. *)
(* Ltac inversions_some := *)
(*   match goal with *)
(*   | H : Some ?x = Some ?y |- _ => inversion H; subst *)
(*   end. *)

(* From Chlipala's tactics. *)
Ltac inject H := injection H; clear H; intros; try subst.

(* More reliable (?) variant of inversions_some. *)
Ltac injections_some :=
  match goal with
    [H : Some ?a = Some ?b |- _ ] => inject H
  end.

(* To use with repeat fequalSafe in automation.
   Unlike f_equal, won't try to prove a = b = c + d by a = c and b = d --- such
   equaities are omega's job. *)
Ltac fequalSafe :=
  match goal with
  | [ |- Some _ = Some _ ] => f_equal
  | [ |- (_, _) = (_, _) ] => f_equal
  end.