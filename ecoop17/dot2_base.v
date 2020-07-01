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

(** *** Term and type members
        Type member labels ([A], [B], [C]) and term (field) member labels ([a], [b], [c]).  *)

Parameter typ_label: Set.
Parameter trm_label: Set.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

(* term variables occurring in types *)
Inductive var : Type :=
| varF : id -> var (* free *)
| varB : id -> var (* locally-bound variable *)
.

Inductive ovl : Set :=
| cvl : vl -> ovl
| varVl : var -> ovl
with ty : Set :=
| TTop : ty
| TBot : ty
(* (z: S) -> T^z *)
| TAll : ty -> ty -> ty
(* x.A :: { L .. U } *)
| TSel : ovl -> typ_label (* A *) -> ty (* L *) -> ty (* U *) -> ty
| TBind  : ty -> ty (* Recursive binder: { z => T^z },
                       where z is locally bound in T *)
| TAnd : ty -> ty -> ty (* Intersection Type: T1 /\ T2 *)
| TOr : ty -> ty -> ty (* Union Type: T1 \/ T2 *)
| TLater : ty -> ty
| TRcd : dec -> ty (* { d } *)
with dec : Set :=
| dec_typ : typ_label -> ty (* L *) -> ty (* U *) -> dec
| dec_trm : trm_label -> ty -> dec
with tm : Set :=
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
| tnew : ty -> defs -> tm
with def : Set :=
| def_typ  : typ_label -> ty -> def
| def_trm  : trm_label -> tm -> def
with defs : Set :=
| defs_nil : defs
| defs_cons : defs -> def -> defs
with vl : Set :=
(* a closure for a lambda abstraction *)
| vabs : list vl (*H*) -> ty -> tm -> vl
(* (* a closure for a first-class type *) *)
(* | vty : list vl (*H*) -> ty -> vl *)
| vnew: list vl (* H *) -> ty -> vl_defs -> vl
with vl_def : Set :=
| vl_def_typ  : typ_label -> ty -> vl_def
| vl_def_trm  : trm_label -> vl -> vl_def
with vl_defs : Set :=
| vl_defs_nil : vl_defs
| vl_defs_cons : vl_defs -> vl_def -> vl_defs.

Scheme ovl_mut     := Induction for ovl     Sort Prop
with   ty_mut      := Induction for ty      Sort Prop
with   dec_mut     := Induction for dec     Sort Prop
with   tm_mut      := Induction for tm      Sort Prop
with   def_mut     := Induction for def     Sort Prop
with   defs_mut    := Induction for defs    Sort Prop
with   vl_mut      := Induction for vl      Sort Prop
with   vl_def_mut  := Induction for vl_def  Sort Prop
with   vl_defs_mut := Induction for vl_defs Sort Prop.
(* Combined Scheme tm_mutind from ovl_mut. *)
Combined Scheme tm_mutind from ovl_mut, ty_mut, dec_mut, tm_mut, def_mut, defs_mut, vl_mut, vl_def_mut, vl_defs_mut.

(* Inductive ovl_ty : Set := *)
(* | VTTop : ovl_ty *)
(* | VTBot : ovl_ty *)
(* (* (z: T) -> T^z *) *)
(* | VTAll : ovl_ty -> ovl_ty -> ovl_ty *)
(* (* x.A :: { L .. U } *) *)
(* | VTSel : ovl -> typ_label (* A *) -> ovl_ty (* L *) -> ovl_ty (* U *) -> ty *)
(* (* | VTSel : var -> typ_label -> ovl_ty *) *)
(* | VTMem : ovl_ty(*S*) -> ovl_ty(*U*) -> ovl_ty *)
(* | VTBind  : ovl_ty -> ovl_ty (* Recursive binder: { z => T^z }, *)
(*                        where z is locally bound in T *) *)
(* | VTAnd : ovl_ty -> ovl_ty -> ovl_ty (* Intersection Type: T1 /\ T2 *) *)
(* | VTOr : ovl_ty -> ovl_ty -> ovl_ty (* Union Type: T1 \/ T2 *) *)
(* (* | VTRcd : dec -> ovl_ty (* { d } *) *) *)
(* (* with dec : Set :=  *) *)
(* (* | dec_typ : typ_label -> ovl_ty (* S *) -> ovl_ty (* U *) -> dec *) *)
(* (* | dec_trm : trm_label -> ovl_ty -> dec *) *)
(* (* (* (* { Type: S..U } *) *) *) *)
(* (* (* | VTMem : ovl_ty(*S*) -> ovl_ty(*U*) -> ovl_ty *) *) *)
(* | VTLater : ovl_ty -> ovl_ty *)
(* . *)

(* Inductive ty : Set := *)
(* (* | TSel : var -> typ_label -> ty *) *)
(* | TMem : ty (* L *) -> ty (* U *) -> ty *)
(* | TBind  : ty -> ty (* Recursive binder: { z => T^z }, *)
(*                        where z is locally bound in T *) *)
(* | TAnd : ty -> ty -> ty (* Intersection Type: T1 /\ T2 *) *)
(* | TOr : ty -> ty -> ty (* Union Type: T1 \/ T2 *) *)
(* | TLater : ty -> ty *)
(* | TRcd : dec -> ty (* { d } *) *)
(* with dec : Set := *)
(* | dec_typ : typ_label -> ty (* S *) -> ty (* U *) -> dec *)
(* | dec_trm : trm_label -> ty -> dec *)
(* . *)

Definition tenv := list ty. (* Gamma environment: static *)
Definition venv := list vl. (* H environment: run-time *)


(* ### Representation of Bindings ### *)

(* An environment is a list of values, indexed by decrementing ids. *)

Inductive closed_var: nat(*B*) -> nat(*F*) -> var -> Prop :=
| closed_varB : forall i j x,
    j > x -> closed_var i j (varF x)
| closed_varF : forall i j x,
    i > x -> closed_var i j (varB x).

Inductive closed_ovl: nat(*B*) -> nat(*F*) -> ovl -> Prop :=
| cl_varVl : forall i j x,
    closed_var i j x ->
    closed_ovl i j (varVl x)
| cl_cvl : forall i j v,
    closed_vl i j v ->
    closed_ovl i j (cvl v)
with closed_ty: nat(*B*) -> nat(*F*) -> ty -> Prop :=
| cl_top: forall i j,
    closed_ty i j TTop
| cl_bot: forall i j,
    closed_ty i j TBot
| cl_all: forall i j T1 T2,
    closed_ty i j T1 ->
    closed_ty (S i) j T2 ->
    closed_ty i j (TAll T1 T2)
| cl_sel: forall i j x A L U,
    closed_ovl i j x ->
    closed_ty i j L ->
    closed_ty i j U ->
    closed_ty i j (TSel x A L U)
| cl_bind: forall i j T,
    closed_ty (S i) j T ->
    closed_ty i j (TBind T)
| cl_and: forall i j T1 T2,
    closed_ty i j T1 ->
    closed_ty i j T2 ->
    closed_ty i j (TAnd T1 T2)
| cl_or: forall i j T1 T2,
    closed_ty i j T1 ->
    closed_ty i j T2 ->
    closed_ty i j (TOr T1 T2)
| cl_later: forall i j T,
    closed_ty i j T ->
    closed_ty i j (TLater T)
| cl_reord : forall i j d,
    (* closed_dec i j d -> *)
    closed_ty i j (TRcd d)
(* | cl_mem: forall i j T1 T2, *)
(*     closed_ty i j T1 -> *)
(*     closed_ty i j T2 -> *)
(*     closed_ty i j (TMem T1 T2) *)
with closed_dec : nat -> nat -> dec -> Prop :=
| cl_dec_typ : forall i j A L U,
    closed_ty i j L ->
    closed_ty i j U ->
    closed_dec i j (dec_typ A L U)
| cl_dec_trm : forall i j A T,
    closed_ty i j T ->
    closed_dec i j (dec_trm A T)
with closed_tm : nat -> nat -> tm -> Prop :=
| cl_tvar : forall i j x,
    i > x ->
    closed_tm i j (tvar x)
(* | cl_ttyp : forall i j x, *)
with closed_vl : nat -> nat -> vl -> Prop :=
| cl_vabs : forall i j H T t,
    closed_listvl i j H ->
    closed_ty i j T ->
    (* closed_tm (S i) j t -> *)
    closed_vl i j (vabs H T t)
(* | cl_vty : forall  i j H T, *)
(*     closed_ty i j T -> *)
(*     closed_listvl i j H -> *)
(*     closed_vl i j (vty H T) *)
with
closed_listvl : nat -> nat -> list vl -> Prop :=
| closed_vnil : forall i j,
    closed_listvl i j nil
| closed_vcons : forall i j v vs,
    closed_vl i j v ->
    closed_listvl i j vs ->
    closed_listvl i j (cons v vs)
.

(* Inductive closed_ovl_ty: nat(*B*) -> nat(*F*) -> ovl_ty -> Prop := *)
(* | cl_vtop: forall i j, *)
(*     closed_ovl_ty i j VTTop *)
(* | cl_vbot: forall i j, *)
(*     closed_ovl_ty i j VTBot *)
(* | cl_vall: forall i j T1 T2, *)
(*     closed_ovl_ty i j T1 -> *)
(*     closed_ovl_ty (S i) j T2 -> *)
(*     closed_ovl_ty i j (VTAll T1 T2) *)
(* | cl_vsel: forall i j x, *)
(*     closed_ovl i j x -> *)
(*     closed_ovl_ty i j (VTSel x) *)
(*     (* closed_ovl_ty i j (TSel (varVl x)) *) *)
(* | cl_vmem: forall i j T1 T2, *)
(*     closed_ovl_ty i j T1 -> *)
(*     closed_ovl_ty i j T2 -> *)
(*     closed_ovl_ty i j (VTMem T1 T2) *)
(* | cl_vbind: forall i j T, *)
(*     closed_ovl_ty (S i) j T -> *)
(*     closed_ovl_ty i j (VTBind T) *)
(* | cl_vand: forall i j T1 T2, *)
(*     closed_ovl_ty i j T1 -> *)
(*     closed_ovl_ty i j T2 -> *)
(*     closed_ovl_ty i j (VTAnd T1 T2) *)
(* | cl_vor: forall i j T1 T2, *)
(*     closed_ovl_ty i j T1 -> *)
(*     closed_ovl_ty i j T2 -> *)
(*     closed_ovl_ty i j (VTOr T1 T2) *)
(* | cl_vlater: forall i j T, *)
(*     closed_ovl_ty i j T -> *)
(*     closed_ovl_ty i j (VTLater T) *)
(* . *)

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
    | TSel v A L U  => TSel (open_rec_var k u v) A (open_rec k u L) (open_rec k u U)
    (* | TMem T1 T2  => TMem (open_rec k u T1) (open_rec k u T2) *)
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

Fixpoint subst (u : var) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TAll T1 T2   => TAll (subst u T1) (subst u T2)
    | TSel v L U   => TSel (subst_var u v) (subst u L) (subst u U)
    | TMem T1 T2   => TMem (subst u T1) (subst u T2)
    | TBind T      => TBind (subst u T)
    | TAnd T1 T2   => TAnd (subst u T1)(subst u T2)
    | TOr T1 T2    => TOr (subst u T1)(subst u T2)
    | TLater T     => TLater (subst u T)
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
(*     | TOr T1 T2    => nosubst T1 /\ nosubst T2 *)
(*   end. *)

Fixpoint tsize_flat(T: ty) :=
  match T with
    | TTop => 1
    | TBot => 1
    | TAll T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TSel _ L U => 1 + tsize_flat L + tsize_flat U
    | TMem T1 T2 => S (tsize_flat T1 + tsize_flat T2)	
    | TBind T => S (tsize_flat T)
    | TAnd T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TOr T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TLater T => S (tsize_flat T)
  end.

Fixpoint tsize_flat_ovl_ty (T: ovl_ty) :=
  match T with
    | VTTop => 1
    | VTBot => 1
    | VTAll T1 T2 => S (tsize_flat_ovl_ty T1 + tsize_flat_ovl_ty T2)
    | VTSel _ => 1
    | VTMem T1 T2 => S (tsize_flat_ovl_ty T1 + tsize_flat_ovl_ty T2)
    | VTBind T => S (tsize_flat_ovl_ty T)
    | VTAnd T1 T2 => S (tsize_flat_ovl_ty T1 + tsize_flat_ovl_ty T2)
    | VTOr T1 T2 => S (tsize_flat_ovl_ty T1 + tsize_flat_ovl_ty T2)
    | VTLater T => S (tsize_flat_ovl_ty T)
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
