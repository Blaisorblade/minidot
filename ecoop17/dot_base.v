(* Only syntax basics, no logical relations. *)
(*
 DSub (D<:) + Bot + /\ + { z => ... }
 T ::= Top | Bot | x.Type | { Type: S..U } | (z: T) -> T^z | T1 /\ T2 | { z => T^z }
 t ::= x | { Type = T } | lambda x:T.t | t t | unpack(t) { x => t }
 *)

Require Import tactics.
Require Export dot_infrastructure_lemmas.

Require Export Arith.EqNat.
Require Export Arith.Le.

(* ### Syntax ### *)

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
| TOr : ty -> ty -> ty (* Union Type: T1 \/ T2 *)
(*                                  . *)
(* | TRcd : dec -> ty (* { d } *) *)
(* with dec : Set :=  *)
(* | dec_typ : typ_label -> ty (* S *) -> ty (* U *) -> dec *)
(* | dec_trm : trm_label -> ty -> dec *)
(* (* (* { Type: S..U } *) *) *)
(* (* | TMem : ty(*S*) -> ty(*U*) -> ty *) *)
| TLater : ty -> ty
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

(* Scheme ty_mut  := Induction for ty  Sort Prop. *)
(* Scheme tm_mut  := Induction for tm Sort Prop *)
(* with   vl_mut  := Induction for vl Sort Prop *)
(* with   ovl_mut  := Induction for ovl  Sort Prop. *)
(* Combined Scheme tm_mutind from tm_mut, vl_mut, ovl_mut. *)

Definition tenv := list ty. (* Gamma environment: static *)
Definition venv := list vl. (* H environment: run-time *)


(* ### Representation of Bindings ### *)

(* An environment is a list of values, indexed by decrementing ids. *)

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
| cl_or: forall i j T1 T2,
    closed_ty i j T1 ->
    closed_ty i j T2 ->
    closed_ty i j (TOr T1 T2)
| cl_and: forall i j T1 T2,
    closed_ty i j T1 ->
    closed_ty i j T2 ->
    closed_ty i j (TAnd T1 T2)
| cl_later: forall i j T,
    closed_ty i j T ->
    closed_ty i j (TLater T)
.

(* open define a locally-nameless encoding wrt to varB type variables. *)
(* substitute var u for all occurrences of (varB k) *)
Definition open_rec_var (k: nat) (u: var) (v: var) : var :=
  match v with
  | varF x => varF x
  | varB i => if beq_nat k i then u else (varB i)
  end.

Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TBot        => TBot
    | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TSel v => TSel (open_rec_var k u v)
    | TMem T1 T2  => TMem (open_rec k u T1) (open_rec k u T2)
    | TBind T => TBind (open_rec (S k) u T)
    | TAnd T1 T2 => TAnd (open_rec k u T1) (open_rec k u T2)
    | TOr T1 T2 => TOr (open_rec k u T1) (open_rec k u T2)
    | TLater T => TLater (open_rec k u T)
  end.

Notation open := (open_rec 0).

(* Definition open u T := open_rec 0 u T. *)
(* Hint Unfold open. *)

(* Locally-nameless encoding with respect to varF variables. *)
Definition subst_var (u: var) (v: var) : var :=
  match v with
  | varB i => varB i
  | varF i => if beq_nat i 0 then u else varF (i - 1)
  end.

Fixpoint subst (U : var) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TAll T1 T2   => TAll (subst U T1) (subst U T2)
    | TSel v => TSel (subst_var U v)
    | TMem T1 T2     => TMem (subst U T1) (subst U T2)
    | TBind T       => TBind (subst U T)
    | TAnd T1 T2    => TAnd (subst U T1)(subst U T2)
    | TOr T1 T2    => TOr (subst U T1)(subst U T2)
    | TLater T     => TLater (subst U T)
  end.

Fixpoint tsize_flat(T: ty) :=
  match T with
    | TTop => 1
    | TBot => 1
    | TAll T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TSel _ => 1
    | TMem T1 T2 => S (tsize_flat T1 + tsize_flat T2)	
    | TBind T => S (tsize_flat T)
    | TAnd T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TOr T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TLater T => S (tsize_flat T)
  end.

Lemma open_preserves_size: forall T x j,
  tsize_flat (open_rec j (varF x) T) =
  tsize_flat T.
Proof.
  induction T; intros; simpl; repeat case_match; eauto.
Qed.

Hint Rewrite open_preserves_size.

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

Hint Constructors closed_var.
Hint Constructors closed_ty.
