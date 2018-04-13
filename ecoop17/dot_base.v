(* Only syntax basics, no logical relations. *)
(*
 DSub (D<:) + Bot + /\ + { z => ... }
 T ::= Top | Bot | x.Type | { Type: S..U } | (z: T) -> T^z | T1 /\ T2 | { z => T^z }
 t ::= x | { Type = T } | lambda x:T.t | t t | unpack(t) { x => t }
 *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Export Omega.
Require Import tactics.

(* ### Syntax ### *)

Definition id := nat.

(* term variables occurring in types *)
Inductive var : Type :=
| varF : id -> var (* free *)
| varB : id -> var (* locally-bound variable *)
.

Parameter typ_label: Set.
Parameter trm_label: Set.

(** *** Term and type members
        Type member labels ([A], [B], [C]) and term (field) member labels ([a], [b], [c]).  *)
Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

Inductive ty : Set :=
| TTop : ty
| TBot : ty
(* (z: T) -> T^z *)
| TAll : ty -> ty -> ty
(* x.Type *)
| TSel : var -> ty
(* | TSel : var -> typ_label -> ty *)
| TMem : ty(*S*) -> ty(*U*) -> ty
| TBind  : ty -> ty (* Recursive binder: { z => T^z },
                       where z is locally bound in T *)
| TAnd : ty -> ty -> ty (* Intersection Type: T1 /\ T2 *)
(* | TOr : ty -> ty -> ty (* Union Type: T1 \/ T2 *) *)
(*                                  . *)
(* | TRcd : dec -> ty (* { d } *) *)
(* with dec : Set :=  *)
(* | dec_typ : typ_label -> ty (* S *) -> ty (* U *) -> dec *)
(* | dec_trm : trm_label -> ty -> dec *)
(* (* (* { Type: S..U } *) *) *)
(* (* | TMem : ty(*S*) -> ty(*U*) -> ty *) *)
.

Inductive tm : Set :=
(* x -- free variable, matching concrete environment *)
| tvar : id -> tm
(* { Type = T } *)
| ttyp : ty -> tm
(* lambda x:T.t *)
| tabs : ty -> tm -> tm
(* t t *)
| tapp : tm -> tm -> tm
(* we can keep it in, but still have typing lemmas for TVarUnpack not just TUnpack. *)
(* unpack(e) { x => ... } *)
| tunpack : tm -> tm -> tm
.
Inductive vl : Set :=
(* a closure for a lambda abstraction *)
| vabs : list vl (*H*) -> ty -> tm -> vl
(* a closure for a first-class type *)
| vty : list vl (*H*) -> ty -> vl
.
Inductive ovl : Set :=
| cvl : vl -> ovl
| varVl : var -> ovl
.

Inductive ovl_ty : Set :=
| VTTop : ovl_ty
| VTBot : ovl_ty
(* (z: T) -> T^z *)
| VTAll : ovl_ty -> ovl_ty -> ovl_ty
(* x.Type *)
| VTSel : ovl -> ovl_ty
(* | VTSel : var -> typ_label -> ovl_ty *)
| VTMem : ovl_ty(*S*) -> ovl_ty(*U*) -> ovl_ty
| VTBind  : ovl_ty -> ovl_ty (* Recursive binder: { z => T^z },
                       where z is locally bound in T *)
| VTAnd : ovl_ty -> ovl_ty -> ovl_ty (* Intersection Type: T1 /\ T2 *)
(* | VTOr : ovl_ty -> ovl_ty -> ovl_ty (* Union Type: T1 \/ T2 *) *)
(*                                  . *)
(* | VTRcd : dec -> ovl_ty (* { d } *) *)
(* with dec : Set :=  *)
(* | dec_typ : typ_label -> ovl_ty (* S *) -> ovl_ty (* U *) -> dec *)
(* | dec_trm : trm_label -> ovl_ty -> dec *)
(* (* (* { Type: S..U } *) *) *)
(* (* | VTMem : ovl_ty(*S*) -> ovl_ty(*U*) -> ovl_ty *) *)
.

(* Scheme ty_mut  := Induction for ty  Sort Prop. *)
(* Scheme tm_mut  := Induction for tm Sort Prop *)
(* with   vl_mut  := Induction for vl Sort Prop *)
(* with   ovl_mut  := Induction for ovl  Sort Prop. *)
(* Combined Scheme tm_mutind from tm_mut, vl_mut, ovl_mut. *)

Definition tenv := list ty. (* Gamma environment: static *)
Definition venv := list vl. (* H environment: run-time *)


(* ### Representation of Bindings ### *)

(* An environment is a list of values, indexed by decrementing ids. *)

Fixpoint indexr {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (beq_nat n (length l')) then Some a else indexr n l'
  end.

Hint Unfold indexr.
Hint Unfold length.

Inductive closed_var: nat(*B*) -> nat(*F*) -> var -> Prop :=
| closed_varB : forall i j x,
    j > x -> closed_var i j (varF x)
| closed_varF : forall i j x,
    i > x -> closed_var i j (varB x).

Inductive closed_ty: nat(*B*) -> nat(*F*) -> ty -> Prop :=
| cl_top: forall i j,
    closed_ty i j TTop
| cl_bot: forall i j,
    closed_ty i j TBot
| cl_all: forall i j T1 T2,
    closed_ty i j T1 ->
    closed_ty (S i) j T2 ->
    closed_ty i j (TAll T1 T2)
| cl_sel: forall i j x,
    closed_var i j x ->
    closed_ty i j (TSel x)
    (* closed_ty i j (TSel (varVl x)) *)
| cl_mem: forall i j T1 T2,
    closed_ty i j T1 ->
    closed_ty i j T2 ->
    closed_ty i j (TMem T1 T2)
| cl_bind: forall i j T,
    closed_ty (S i) j T ->
    closed_ty i j (TBind T)
| cl_and: forall i j T1 T2,
    closed_ty i j T1 ->
    closed_ty i j T2 ->
    closed_ty i j (TAnd T1 T2)
.
Inductive closed_tm : nat -> nat -> tm -> Prop :=
| cl_tvar : forall i j x,
    i > x ->
    closed_tm i j (tvar x)
.

Inductive closed_vl i j : vl -> Prop :=
| cl_vabs : forall H T t,
    closed_listvl i j H ->
    closed_ty i j T ->
    (* closed_tm (S i) j t -> *)
    closed_vl i j (vabs H T t)
| cl_vty : forall H T,
    closed_ty i j T ->
    closed_listvl i j H ->
    closed_vl i j (vty H T)
with
closed_listvl i j : list vl -> Prop :=
| closed_vnil :
    closed_listvl i j nil
| closed_vcons : forall v vs,
    closed_vl i j v ->
    closed_listvl i j vs ->
    closed_listvl i j (cons v vs)
.

Inductive closed_ovl i (*B*) j (*F*): ovl -> Prop :=
| cl_varVl : forall x,
    closed_var i j x ->
    closed_ovl i j (varVl x)
| cl_cvl : forall v,
    (* closed_vl i j v -> *) (*XXX*)
    closed_ovl i j (cvl v)
.

Inductive closed_ovl_ty: nat(*B*) -> nat(*F*) -> ovl_ty -> Prop :=
| cl_vtop: forall i j,
    closed_ovl_ty i j VTTop
| cl_vbot: forall i j,
    closed_ovl_ty i j VTBot
| cl_vall: forall i j T1 T2,
    closed_ovl_ty i j T1 ->
    closed_ovl_ty (S i) j T2 ->
    closed_ovl_ty i j (VTAll T1 T2)
| cl_vsel: forall i j x,
    closed_ovl i j x ->
    closed_ovl_ty i j (VTSel x)
    (* closed_ovl_ty i j (TSel (varVl x)) *)
| cl_vmem: forall i j T1 T2,
    closed_ovl_ty i j T1 ->
    closed_ovl_ty i j T2 ->
    closed_ovl_ty i j (VTMem T1 T2)
| cl_vbind: forall i j T,
    closed_ovl_ty (S i) j T ->
    closed_ovl_ty i j (VTBind T)
| cl_vand: forall i j T1 T2,
    closed_ovl_ty i j T1 ->
    closed_ovl_ty i j T2 ->
    closed_ovl_ty i j (VTAnd T1 T2)
.

(* open define a locally-nameless encoding wrt to varB type variables. *)
(* substitute var u for all occurrences of (varB k) *)
Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TBot        => TBot
    | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TSel (varF x) => TSel (varF x)
    | TSel (varB i) => if beq_nat k i then TSel u else TSel (varB i)
    | TMem T1 T2  => TMem (open_rec k u T1) (open_rec k u T2)
    | TBind T => TBind (open_rec (S k) u T)
    | TAnd T1 T2 => TAnd (open_rec k u T1) (open_rec k u T2)
  end.

Notation open := (open_rec 0).

(* Definition open u T := open_rec 0 u T. *)
(* Hint Unfold open. *)

(* Locally-nameless encoding with respect to varF variables. *)
Fixpoint subst (U : var) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TAll T1 T2   => TAll (subst U T1) (subst U T2)
    | TSel (varB i) => TSel (varB i)
    | TSel (varF i) => if beq_nat i 0 then TSel U else TSel (varF (i-1))
    | TMem T1 T2     => TMem (subst U T1) (subst U T2)
    | TBind T       => TBind (subst U T)
    | TAnd T1 T2    => TAnd (subst U T1)(subst U T2)
  end.

(* Fixpoint nosubst (T : ty) {struct T} : Prop := *)
(*   match T with *)
(*     | TTop         => True *)
(*     | TBot         => True *)
(*     | TAll T1 T2   => nosubst T1 /\ nosubst T2 *)
(*     | TSel (varB i) => True *)
(*     | TSel (varF i) => i <> 0 *)
(*     | TMem T1 T2    => nosubst T1 /\ nosubst T2 *)
(*     | TBind T       => nosubst T *)
(*     | TAnd T1 T2    => nosubst T1 /\ nosubst T2 *)
(*   end. *)

Fixpoint tsize_flat(T: ty) :=
  match T with
    | TTop => 1
    | TBot => 1
    | TAll T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TSel _ => 1
    | TMem T1 T2 => S (tsize_flat T1 + tsize_flat T2)	
    | TBind T => S (tsize_flat T)
    | TAnd T1 T2 => S (tsize_flat T1 + tsize_flat T2)
  end.



Lemma open_preserves_size': forall T x j,
  tsize_flat (open_rec j (varF x) T) =
  tsize_flat T.
Proof.
  induction T; intros; simpl; repeat case_match; eauto.
Qed.

Hint Rewrite open_preserves_size'.

(* Lemma open_preserves_size: forall T x j, *)
(*   tsize_flat T = *)
(*   tsize_flat (open_rec j (varF x) T). *)
(* Proof. *)
(*   intros; autorewrite with core; trivial. *)
(* Qed. *)
(* Ltac inv_mem := match goal with *)
(*                   | H: closed 0 (length ?GH) (length ?G) (TMem ?T1 ?T2) |- *)
(*                     closed 0 (length ?GH) (length ?G) ?T2 => inversion H; subst; eauto *)
(*                   | H: closed 0 (length ?GH) (length ?G) (TMem ?T1 ?T2) |- *)
(*                     closed 0 (length ?GH) (length ?G) ?T1 => inversion H; subst; eauto *)
(*                 end. *)


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.

Hint Constructors closed_ty.

Hint Constructors option.
Hint Constructors list.

Hint Resolve ex_intro.

