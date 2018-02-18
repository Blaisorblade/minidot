Require Import mathcomp.ssreflect.all_ssreflect.
(*         ssrfun ssrbool eqtype ssrnat div seq. *)
(* Require Import path choice fintype tuple finfun finset. *)
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Unset Printing Implicit Defensive.

(* Lemma subnK : forall m n, n <= m -> m - n + n = m. *)
(* Proof. *)
(*   elim => [|m IHm] n le_n_m. *)
  
(*   move => m n lenm. *)
(*   (* move: m lenm => p lenp. *) *)
(*   (* move: p lenp. *) *)
(*   (* elim: n. *) *)

(*   elim: n m lenm => [m |n IHn m lt_n_m]. *)


Fixpoint f n := if n is n'.+1 then (f n').+2 else 0.
Lemma foo: forall n, f (2 * n) = f n + f n.
Proof.
  elim => [|n ihn].
    by rewrite muln0 //.
    rewrite !addnS !addSn -/f.
    rewrite mulnS.
    by rewrite -ihn //.
Qed.
