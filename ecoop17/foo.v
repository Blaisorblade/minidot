(* Require Import Fin. *)
(* Require Import Program. *)
(* Lemma fineq_eq: forall n (a b: Fin.t n), Fin.FS a = Fin.FS b -> a = b. *)
(*   intros; induction n. *)
(*   - dependent destruction a. *)
(*   - dependent destruction a; dependent destruction b; inversion H; eauto. *)
(*     dependent destruction H1. *)
(*     auto. *)
(* Qed. *)
(* Lemma fin_neq: forall n (a b: Fin.t n), a <> b -> Fin.FS a <> Fin.FS b. *)
(* eauto using fineq_eq. Qed. *)

Inductive Tp := B : Tp | Arr : Tp -> Tp -> Tp.
Lemma nofix_Tp: forall a b, a <> Arr a b.
Proof. induction a; intuition congruence. Qed.

Require Import Program.
Set Program Mode.

Definition empty_type: Type := { x: bool |  False }.
Definition e: empty_type. Admitted.

Definition T: Type := { v: bool | e = true }.
Next Obligation. cbn; intros.
(* v: bool |- False *)
