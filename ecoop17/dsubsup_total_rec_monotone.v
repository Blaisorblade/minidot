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

(* Infrastructure for well-founded induction for properties of vtp. *)
Definition argPair := (ty * nat)%type.

Definition argMeasure (p: argPair) := let '(T, n) := p in val_type_measure T n.
Definition val_type_termRel := MR termRel argMeasure.

Lemma wf_val_type_termRel : well_founded val_type_termRel.
Proof.
  apply measure_wf. apply wf_termRel.
Qed.
Hint Resolve wf_val_type_termRel.

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
      forall vx j (Hj : j <= n),
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

(* Show that different branches are disjoint. *)
Ltac discriminatePlus := repeat split; intros; let Habs := fresh "Habs" in intro Habs; destruct Habs; discriminate.

Ltac simple_ineq :=
  (* simpl; omega. *)
  simpl; auto using le_n_S, le_plus_l, le_plus_r.

Lemma termRelShow: forall j n T1 T2,
  j <= n -> tsize_flat T2 < tsize_flat T1 ->
  val_type_termRel (T2, j) (T1, n).
Proof.
  intros * Hj Ht.
  unfold val_type_termRel, MR, termRel, argMeasure, val_type_measure.
  (* If we only know that Hj: j <= n, we must case-split on it, and use
   smaller_types when j = n and smaller_n when j < n.
 A lternatively, we could allow *)
  destruct Hj; try assert (j < S m) by simple_ineq; auto using left_lex, right_lex.
Qed.
  (* - apply right_lex. assumption. *)
  (* - apply left_lex. omega. *)


Lemma termRelShowOpen: forall j n x T1 T2,
  j <= n -> tsize_flat T2 < tsize_flat T1 ->
  val_type_termRel (open (varH x) T2, j) (T1, n).
Proof.
  intros * Hj Ht.
  unfold val_type_termRel, MR, termRel, argMeasure, val_type_measure.
  destruct Hj; try assert (j < S m) by simple_ineq; auto using left_lex, right_lex.
  unfold open; try rewrite <- open_preserves_size.
  auto using left_lex, right_lex.
Qed.

Lemma termRelShowLt: forall j n T1 T2,
  j < n ->
  val_type_termRel (T2, j) (T1, n).
Proof.
  intros * Hj.
  unfold val_type_termRel, MR, termRel, argMeasure, val_type_measure.
  auto using left_lex, right_lex.
Qed.

Ltac applyNSimpleIneq l := apply l; simple_ineq.

(* Solve obligations from valType using ssreflect-based ideas, that is, reusing lemmas for the various cases. *)
Ltac valTypeObligationsSSReflection :=
  program_simpl;
  solve [applyNSimpleIneq termRelShowOpen | applyNSimpleIneq termRelShow | applyNSimpleIneq termRelShowLt | discriminatePlus].
Solve Obligations with valTypeObligationsSSReflection.

Print val_type_func_obligation_1.
Check val_type_func_obligation_1.
Check val_type_func_obligation_2.
Check val_type_func_obligation_3.
Check val_type_func_obligation_4.
Print val_type_func_obligation_2.
Print val_type_func_obligation_3.
Print val_type_func_obligation_4.
Print val_type_func_obligation_5.
Print val_type_func_obligation_6.
Print val_type_func_obligation_7.
(* Print val_type_func_obligation_8. *)
(* Print val_type_func_obligation_9. *)
Print val_type_func_obligation_10.
(* Print val_type_func_obligation_11. *)
(* Print val_type_func_obligation_12. *)
Print val_type_func_obligation_13.
Print val_type_func_obligation_14.
Print val_type_func_obligation_15.
(* Print val_type_func_obligation_16. *)
(* Print val_type_func_obligation_17. *)
(* Print val_type_func_obligation_18. *)
(* Print val_type_func_obligation_19. *)
(* Print val_type_func_obligation_20. *)
(* Print val_type_func_obligation_21. *)
(* Print val_type_func_obligation_22. *)

(* (* Solve Obligations with *) *)
(* (*     program_simpl; *) *)
(* (*   unfold val_type_termRel, MR, termRel, argMeasure, val_type_measure; *) *)
(* (*   auto using termRelShowLt, termRelShowOpen, termRelShow, le_n_S, le_plus_l, le_plus_r. *) *)

(* (* Next Obligation. *) *)
(* (*   program_simpl. *) *)
(* (*   (apply termRelShowOpen; simple_ineq) || solve [apply termRelShow; simple_ineq] || (apply termRelShowLt; simple_ineq). *) *)
(* (*   simple_ineq. *) *)
(* (*   (apply termRelShowOpen; simple_ineq) || (apply termRelShow; simple_ineq) || (apply termRelShowLt; simple_ineq). *) *)
(* (*   apply termRelShowLt; simple_ineq. *) *)
(* (*   simple_ineq. *) *)

(* (*   program_simpl; *) *)
(* (*   (apply termRelShow; simple_ineq || apply termRelShowOpen; simple_ineq || apply termRelShowOpen; simple_ineq).   *) *)

(* (*   using termRelShowLt, termRelShowOpen, termRelShow, le_n_S, le_plus_l, le_plus_r. *) *)
(* (*     apply termRelShow. *) *)
(* (*     auto using termRelShowLt, termRelShowOpen, termRelShow, le_n_S, le_plus_l, le_plus_r. *) *)
(* (*   apply termRelShow; simple_ineq. Qed. *) *)
(* (* Next Obligation. apply termRelShowOpen; simple_ineq. Qed.   *) *)
(* (* Next Obligation. apply termRelShowLt; simple_ineq. Qed.   *) *)
(* (* Next Obligation. apply termRelShowLt; simple_ineq. Qed.   *) *)
(* (* Next Obligation. apply termRelShowLt; simple_ineq. Qed.   *) *)
(* (* Next Obligation. apply termRelShowLt; simple_ineq. Qed.   *) *)
(* (* Next Obligation. apply termRelShowLt; simple_ineq. Qed.   *) *)
(* (* Next Obligation. apply termRelShowLt; simple_ineq. Qed.   *) *)
(* (* Next Obligation. apply termRelShow; simple_ineq. Qed.   *) *)
(* (* Next Obligation. apply termRelShow; simple_ineq. Qed.   *) *)
(* (* Next Obligation. apply termRelShowOpen; simple_ineq. Qed.   *) *)
(* (* Solve Obligations with discriminatePlus. *) *)
(* (*   auto using termRelShowLt, termRelShowOpen, termRelShow. *) *)

(* (* Solve Obligations with discriminatePlus. *) *)

Ltac smaller_n :=
  Tactics.program_simpl;
  autounfold; apply left_lex; simple_ineq.

Ltac smaller_types :=
  Tactics.program_simpl;
  autounfold; apply right_lex;
  unfold open; try rewrite <- open_preserves_size; simpl; omega.

(* Ltac valTypeObligations Hj := *)
(*   Tactics.program_simpl; *)
(*   smaller_n || smaller_types || discriminatePlus || (try destruct Hj; [ smaller_types | smaller_n ]). *)

(* Solve Obligations with valTypeObligations Hj. *)
(* Ltac valTypeObligationsReflect := *)
(*   Tactics.program_simpl; *)
(*   (((apply termRelShowOpen || apply termRelShow); simple_ineq || omega) ||  *)
(*   discriminatePlus). *)

(* Solve Obligations with valTypeObligationsReflect. *)
(* Next Obligation. *)
(*   smaller_n. *)

Ltac valTypeObligations :=
  Tactics.program_simpl;
  smaller_n || smaller_types || discriminatePlus ||
            (* (apply termRelShowOpen || apply termRelShow); auto; *)
  (* unfold open; try rewrite <- open_preserves_size; *)
  (* simple_ineq. *)
  simpl; omega.

(* Solve Obligations with valTypeObligations. *)

(* Next Obligation. *)
(*   apply termRelShowOpen. *)
(*   simple_ineq. simple_ineq. *)
(* Ltac valTypeObligations' := *)
(*   Tactics.program_simpl; *)
(*   smaller_n || smaller_types || discriminatePlus || *)

(*             (apply termRelShowOpen || apply termRelShow); auto; *)
(*   (* unfold open; try rewrite <- open_preserves_size; *) *)
(*   simple_ineq. *)
(*   (* simpl; omega. *) *)

(* Solve Obligations with valTypeObligations'. *)

(* (* Check eq_ind. *) *)
(* (* Print eq_ind. *) *)
(* (* eq_ind =  *) *)
(* (* fun (A : Type) (x : A) (P : A -> Prop) => eq_rect x P *) *)
(* (*      : forall (A : Type) (x : A) (P : A -> Prop), P x -> forall y : A, x = y -> P y *) *)
(* (* Argument A is implicit *) *)
(* (* Argument scopes are [type_scope _ function_scope _ _ _] *) *)
(* Print termRelShowOpen. *)
(* (* Solve Obligations with valTypeObligations'. *) *)
(* Solve Obligations with  *)
(*   Tactics.program_simpl; *)
(*   apply termRelShowOpen; *)
(*   auto; simpl; omega. *)
(* Print val_type_func_obligation_2. *)
(* Next Obligation. *)
(*   apply termRelShow; *)
(*   auto; simpl; omega. *)
(* Qed. *)
(* Print val_type_func_obligation_3. *)
(* Solve Obligations with  *)
(*   Tactics.program_simpl; *)
(*   apply termRelShow; *)
(*   auto; simpl; omega. *)
(* Solve Obligations with smaller_n. *)
(* Solve Obligations with discriminatePlus. *)
(*   apply termRelShow; auto; simpl; omega. *)


(*   Solve Obligations with valTypeObligations Hj. *)


(* 
   The expansion of val_type, val_type_func is incomprehensible. 
   We cannot (easily) unfold and reason about it. Therefore, we prove unfolding of
   val_type to its body as a lemma.
   (Note that the unfold_sub tactic relies on 
   functional extensionality)
*)

Lemma val_type_unfold' : forall n env GH T v, val_type env GH T n v =
  match v,T with
    | vabs env1 T0 y, TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall vx j (Hj : j <= n),
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

(* Admitted. *)
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
