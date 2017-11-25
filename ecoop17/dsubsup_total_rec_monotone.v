(* Termination for D<:> with intersection types and recursive self types *)
(* this version includes a proof of totality  *)

(*
 DSub (D<:) + Bot + /\ + { z => ... }
 T ::= Top | Bot | x.Type | { Type: S..U } | (z: T) -> T^z | T1 /\ T2 | { z => T^z }
 t ::= x | { Type = T } | lambda x:T.t | t t | unpack(t) { x => t }
 *)

Require Export dsubsup_total_rec_base.
Require Import Arith.Wf_nat.
Require Import Program.
Import WfExtensionality.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.

(* ### Semantic Interpretation of Types (Logical Relations) ### *)

(* NEW NEW DESIGN IDEA:

I'm changing definitions a lot to make val_type monotone.
*)

Definition val_type_measure T (k : nat) := (existT (fun _ => nat) k (tsize_flat T)).

Hint Unfold val_type_measure.

Definition vset := vl -> Prop.
Hint Unfold vset.
Definition nvset := nat -> vset.
Hint Unfold nvset.

Definition mon_nvset := { phi : nvset | forall m n v, m < n -> phi n v -> phi m v }.
Hint Unfold mon_nvset.

Definition termRel := lexprod nat (fun _ => nat) lt (fun _ => lt).
Hint Unfold termRel.

Lemma wf_termRel : well_founded termRel.
Proof.
 apply wf_lexprod; try intro; apply lt_wf.
Defined.

Hint Resolve wf_termRel.

Ltac smaller_n :=
  Tactics.program_simpl;
  autounfold; apply left_lex; omega.

Ltac smaller_types :=
  Tactics.program_simpl;
  autounfold; apply right_lex;
  unfold open; try rewrite <- open_preserves_size; simpl; omega.
(* Show that different branches are disjoint. *)
Ltac discriminatePlus := repeat split; intros; let Habs := fresh "Habs" in intro Habs; destruct Habs; discriminate.

Ltac valTypeObligations := smaller_n || smaller_types || discriminatePlus.

(* Program Fixpoint val_type (env: list vseta) (GH:list vseta) (T:ty) n (dd: vset n) (v:vl) {measure (tsize_flat T)}: Prop := *)

(*
Again:
The first env (env, or G1) is for looking up varF variables.
The first env matches the concrete runtime environment, and is
extended during type assignment, so never here.
The second env (GH) is for looking up varH variables.
The second env matches the abstract runtime environment, and is
extended during subtyping and here.
 *)
Program Fixpoint val_type (env: list vl) (GH: list vl) (T:ty) (n: nat) (v:vl)
        {measure (val_type_measure T n) (termRel)}: Prop :=
  match v,T with
    | vabs env1 T0 y, TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall vx j (Hj : j < n),
        val_type env GH T1 j vx ->
        exists v, tevaln (vx::env1) y v /\ val_type env (v::GH) (open (varH (length GH)) T2) j v

    | vty env1 TX, TMem T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2 /\
      forall j (Hj : j < n),
        forall vy,
          (val_type env GH T1 j vy -> val_type env1 GH TX j vy) /\
          (val_type env1 GH TX j vy -> val_type env GH T2 j vy)
    | _, TSel (varF x) =>
      match indexr x env with
        | Some (vty env1 TX) => forall j (Hk : j < n), val_type env1 GH TX j v
        | _ => False
      end
    | _, TSel (varH x) =>
      match indexr x GH with
        | Some (vty env1 TX) => forall j (Hk : j < n), val_type env1 GH TX j v
        | _ => False
      end

    | _, TAnd T1 T2 =>
      val_type env GH T1 n v /\ val_type env GH T2 n v
        
    | _, TBind T1 =>
      closed 1 (length GH) (length env) T1 /\
      val_type env (v::GH) (open (varH (length GH)) T1) n v
                                  
    | _, TTop =>
      True
    | _,_ =>
      False
  end.

(* Next Obligation. *)

Solve Obligations with valTypeObligations.
                                  
(* 
   The expansion of val_type, val_type_func is incomprehensible. 
   We cannot (easily) unfold and reason about it. Therefore, we prove unfolding of
   val_type to its body as a lemma.
   (Note that the unfold_sub tactic relies on 
   functional extensionality)
*)


(* this is just to accelerate Coq -- val_type in the goal is slooow *)
Inductive vtp: list vl -> list vl -> ty -> forall n, vl -> Prop :=
| vv: forall G H T n v, val_type G H T n v -> vtp G H T n v.

Lemma unvv: forall G H T n v,
  vtp G H T n v -> val_type G H T n v.
Proof.
  intros * H0. destruct H0. assumption.
Qed.

Axiom prop_extensionality:
  forall (P Q: Prop), (P <-> Q) -> P = Q.
Lemma vtp_unfold: forall G H T n v,
  vtp G H T n v = val_type G H T n v.
Proof.
  intros.
  apply prop_extensionality.
  split; intros.
  apply unvv. assumption.
  constructor. assumption.
Qed.

Lemma val_type_unfold' : forall n env GH T v, val_type env GH T n v =
  match v,T with
    | vabs env1 T0 y, TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall vx j (Hj : j < n),
        val_type env GH T1 j vx ->
        exists v, tevaln (vx::env1) y v /\ val_type env (v::GH) (open (varH (length GH)) T2) j v

    | vty env1 TX, TMem T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2 /\
      forall j (Hj : j < n),
        forall vy,
          (val_type env GH T1 j vy -> val_type env1 GH TX j vy) /\
          (val_type env1 GH TX j vy -> val_type env GH T2 j vy)
    | _, TSel (varF x) =>
      match indexr x env with
        | Some (vty env1 TX) => forall j (Hk : j < n), val_type env1 GH TX j v
        | _ => False
      end
    | _, TSel (varH x) =>
      match indexr x GH with
        | Some (vty env1 TX) => forall j (Hk : j < n), val_type env1 GH TX j v
        | _ => False
      end

    | _, TAnd T1 T2 =>
      val_type env GH T1 n v /\ val_type env GH T2 n v

    | _, TBind T1 =>
      closed 1 (length GH) (length env) T1 /\
      val_type env (v::GH) (open (varH (length GH)) T1) n v

    | _, TTop =>
      True
    | _,_ =>
      False
  end.

(*   This proof is slow, and the right-hand side of val_type_unfold has been copied and pasted *)
(*   literally from val_type, so there is no question about the  *)
(*   validity of the lemma, and we often admit it for performance reasons. *)


Proof.
  intros. unfold val_type at 1. unfold val_type_func.
  unfold_sub val_type (val_type env GH T n v).

  program_simplify.

  destruct v; simpl.

  - destruct T; try reflexivity; destruct v.
    + destruct (indexr i env); try destruct v; reflexivity.
    + destruct (indexr i GH); try destruct v; reflexivity.
    + reflexivity.
  - destruct T; try reflexivity; destruct v.
    + destruct (indexr i env); try destruct v; reflexivity.
    + destruct (indexr i GH); try destruct v; reflexivity.
    + reflexivity.
Qed.
