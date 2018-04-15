Require Import tactics.
Require Import dot_wfrel.
Require Import dot_base.

Lemma vtp_unfold : forall T n v env,
    vtp T n v env =
    match T with
    | TAll T1 T2 =>
      closed_ty 0 (length env) T1 /\ closed_ty 1 (length env) T2 /\
      interpTAll n
                 (fun n p => vtp T1 n)
                 (fun n p => vtp (open (varF (length env)) T2) n)
                 n (le_n _) v env
    | TMem T1 T2 =>
      closed_ty 0 (length env) T1 /\ closed_ty 0 (length env) T2 /\
      interpTMem n
                 (fun n p => vtp T1 n)
                 (fun n p => vtp T2 n)
                 (fun T j p => vtp T j)
                 n (le_n _) v env
    | TTop => True
    | TSel x =>
      interpTSel n x (fun T j p => vtp T j)
                n (le_n _) v env
    | TAnd T1 T2 =>
      interpTAnd n
                 (fun n p => vtp T1 n)
                 (fun n p => vtp T2 n)
                 n (le_n _) v env
    | TBind T1 =>
      closed_ty 1 (length env) T1 /\
      vtp (open (varF (length env)) T1) n v (v::env)
    | _ =>
      False
    end.
Proof.
  intros;
    rewrite vtp_to_val_type;
    rewrite val_type_unfold;
    reflexivity.
Qed.

(* Split it here *)
Example ex0 : forall n v, vtp TTop n v [].
Proof.
  intros. rewrite vtp_unfold. auto.
Qed.

(* Example ex1: forall env T n, exists dd, forall v, vtp T n v env <-> dd v. *)
(* Proof. *)
(*   intros. remember (fun v => vtp T n v env) as V. *)

(*   simpl. *)
(*   exists V. *)
(*   exists (fun v => vtp T n v env). intros. *)
(*   split; intros; assumption. *)
(* Qed. *)

Example ex3: forall env T n, vtp (TMem TBot TTop) n (vty env T) [].
Proof.
  intros. rewrite vtp_unfold.
  repeat split_and. constructor. constructor.
  induction n.
  - intros j Hj. inversion Hj.
  - 
    intros. split. intros. rewrite vtp_unfold in H. destruct vy; inversion H.
    intros. rewrite vtp_unfold. destruct vy; trivial.

  Restart.
  intros. rewrite vtp_unfold.
  split_and. constructor.
  split_and. constructor.
  unfold interpTMem.
  intros.
  rewrite (vtp_unfold TBot);
  rewrite (vtp_unfold TTop).
  split_and;
  tauto.
  Restart.

  intros; rewrite vtp_unfold;
  repeat split_and; try constructor;
  try rewrite (vtp_unfold TBot);
  try rewrite (vtp_unfold TTop); tauto.
  Restart.

  Ltac simpl_vtp :=
    match goal with
    | H : context [ vtp ?T _ _ _ ] |- _ =>
      tryif is_var T then fail else rewrite (vtp_unfold T) in H
    | |- context [ vtp ?T _ _ _ ] =>
      tryif is_var T then fail else rewrite (vtp_unfold T)
    end.
    (* (is_var T; idtac T; idtac H) || rewrite (vtp_unfold T) *)
    (* tryif is_var T then idtac else *)
    (* (is_var T; idtac T) *)
    (* || *)
    (* rewrite (vtp_unfold T) *)

  intros; rewrite vtp_unfold;
    repeat split_and; try constructor; repeat simpl_vtp; tauto.
Qed.
  (* match goal with *)
  (* | H : context [ vtp ?T ] |- _ => is_var T;  rewrite (vtp_unfold T) *)

  (* - omega. *)
  (* - *)
  (*   rewrite vtp_unfold. *)
  (*   intros. rewrite vtp_unfold in H0. destruct vy; inversion H0. *)
  (*   intros. rewrite vtp_unfold. destruct vy; trivial. *)
