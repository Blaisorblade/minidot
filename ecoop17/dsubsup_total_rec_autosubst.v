Require Import Autosubst.Autosubst.

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Export Omega.

(* ### Syntax ### *)

Inductive tm : Type :=
(* x -- free variable, matching concrete environment *)
| tvar : var -> tm
(* { Type = T } *)
| ttyp : ty -> tm
(* lambda x:T.t *)
| tabs : ty -> ({bind tm})-> tm
(* t t *)
| tapp : tm -> tm -> tm
(* unpack(e) { x => ... } *)
| tunpack : tm -> tm -> tm                       
with ty : Type :=
| TTop : ty
| TBot : ty
(* (z: T) -> T^z *)
| TAll : ty -> ty -> ty
(* x.Type *)
| TSel : var -> ty
(* { Type: S..U } *)
| TMem : ty(*S*) -> ty(*U*) -> ty
| TBind  (t : {bind tm in ty}) : ty (* Recursive binder: { z => T^z },
                         where z is locally bound in T *)
| TAnd : ty -> ty -> ty (* Intersection Type: T1 /\ T2 *)
.

Inductive vl : Type :=
(* a closure for a lambda abstraction *)
| vabs : list vl (*H*) -> ty -> tm -> vl
(* a closure for a first-class type *)
| vty : list vl (*H*) -> ty -> vl
.

(* Print ty. *)

Instance Ids_tm : Ids tm. derive. Defined.
Instance Rename_tm : Rename tm. derive. Defined.
Instance Subst_tm : Subst tm. derive. Defined.
Instance SubstLemmas_tm : SubstLemmas tm. derive. Qed.

Instance Rename_ty : Rename ty. derive. Defined.
Instance Subst_ty : Subst ty. derive. Defined.
Instance Ids_ty : Ids ty. derive. Defined.
Instance SubstLemmas_ty : SubstLemmas ty. derive. Qed.

Definition tenv := list ty. (* Gamma environment: static *)
Definition venv := list vl. (* H environment: run-time *)

Print Subst_ty.
Print Subst_tm.

Instance HSubst_vl_tm: HSubst tm ty. derive. Qed.
Print HSubst_vl_tm.
