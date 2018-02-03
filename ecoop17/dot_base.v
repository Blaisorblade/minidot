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

Inductive tm : Type :=
(* x -- free variable, matching concrete environment *)
| tvar : id -> tm
(* { Type = T } *)
| ttyp : ty -> tm
(* lambda x:T.t *)
| tabs : ty -> tm -> tm
(* t t *)
| tapp : tm -> tm -> tm
(* unpack(e) { x => ... } *)
| tunpack : tm -> tm -> tm                       
.

Inductive vl : Type :=
(* a closure for a lambda abstraction *)
| vabs : list vl (*H*) -> ty -> tm -> vl
(* a closure for a first-class type *)
| vty : list vl (*H*) -> ty -> vl
.

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

Inductive closed: nat(*B*) -> nat(*F*) -> ty -> Prop :=
| cl_top: forall i j,
    closed i j TTop
| cl_bot: forall i j,
    closed i j TBot
| cl_all: forall i j T1 T2,
    closed i j T1 ->
    closed (S i) j T2 ->
    closed i j (TAll T1 T2)
| cl_sel: forall i j x,
    j > x ->
    closed i j (TSel (varF x))
| cl_selb: forall i j x,
    i > x ->
    closed i j (TSel (varB x))
| cl_mem: forall i j T1 T2,
    closed i j T1 ->
    closed i j T2 ->
    closed i j (TMem T1 T2)
| cl_bind: forall i j T,
    closed (S i) j T ->
    closed i j (TBind T)
| cl_and: forall i j T1 T2,
    closed i j T1 ->
    closed i j T2 ->
    closed i j (TAnd T1 T2)
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

Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop         => True
    | TBot         => True
    | TAll T1 T2   => nosubst T1 /\ nosubst T2
    | TSel (varB i) => True
    | TSel (varF i) => i <> 0
    | TMem T1 T2    => nosubst T1 /\ nosubst T2
    | TBind T       => nosubst T
    | TAnd T1 T2    => nosubst T1 /\ nosubst T2
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
Ltac inv_mem := match goal with
                  | H: closed 0 (length ?GH) (length ?G) (TMem ?T1 ?T2) |-
                    closed 0 (length ?GH) (length ?G) ?T2 => inversion H; subst; eauto
                  | H: closed 0 (length ?GH) (length ?G) (TMem ?T1 ?T2) |-
                    closed 0 (length ?GH) (length ?G) ?T1 => inversion H; subst; eauto
                end.


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.

Hint Constructors closed.

Hint Constructors option.
Hint Constructors list.

Hint Resolve ex_intro.


(* ### Evaluation (Big-Step Semantics) ### *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
Could use do-notation to clean up syntax.
*)

(* TODO: Step-index this semantics. *)
Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | tvar x       => Some (indexr x env)
        | ttyp T       => Some (Some (vty env T))
        | tabs T y     => Some (Some (vabs env T y))
        | tapp ef ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vty _ _)) => Some None
                | Some (Some (vabs env2 _ ey)) =>
                  teval n (vx::env2) ey
              end
          end
        | tunpack ex ey =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              teval n (vx::env) ey 
          end
      end
  end.


Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).

