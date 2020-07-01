Require Import tactics.

Ltac failer P :=
  match P with
  | forall x, ?Q => idtac "univ"; idtac Q; failer Q
  | _ -> ?Q => idtac "impl"
                  (* idtac Q; failer Q *)
  (* | exists _, _ => idtac "exist" ;idtac P *)
  (* | True => idtac "true" *)
  | _ => idtac "failed"
  end.
(* Examples from stlc_sound.v *)
failer (forall x: nat, x >= 0 -> True).
failer (exists v, vtp T1 v).
failer (forall v, vtp T1 v -> exists v2, vtp T2 v2).
repeat match goal with | H: forall x, ?P |- _ =>  idtac P; failer P end.
(* Ltac ev2 := *)
(* ev. *)