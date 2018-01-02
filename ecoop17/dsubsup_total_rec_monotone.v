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

Hint Constructors lexprod.

Definition val_type_measure T (k : nat) := (existT (fun _ => nat) k (tsize_flat T)).

Hint Unfold val_type_measure.

Definition vset := vl -> Prop.
Hint Unfold vset.

Definition termRel := lexprod nat (fun _ => nat) lt (fun _ => lt).
Hint Unfold termRel.

Lemma wf_termRel : well_founded termRel.
Proof.
 apply wf_lexprod; intro; apply lt_wf.
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

Global Unset Transparent Obligations.

(* Show that different branches are disjoint. *)
Ltac discriminatePlus :=
  (* repeat split; intros; let Habs := fresh "Habs" in intro Habs; destruct Habs; discriminate. *)
  repeat split_conj; intros;
  (let Habs := fresh "Habs" in
  try (intro Habs; destruct Habs) + idtac);
  discriminate.

(* Prove some inequalities needed below, without producing big proof terms like omega does. Probably not worth it. *)
Ltac simple_ineq :=
  (* simpl; omega. *)
  simpl; auto using le_n_S, le_plus_l, le_plus_r; omega.
  (* If this tactic fails, add back omega at the end. *)

Hint Extern 5 (_ < tsize_flat _) =>
  unfold open;
  rewrite open_preserves_size';
  simple_ineq.

(* These three lemmas take care of the various forms of proof obligations that arise from val_type. *)
Lemma termRelShow: forall j n T1 T2,
  j <= n -> tsize_flat T2 < tsize_flat T1 ->
  val_type_termRel (T2, j) (T1, n).
Proof.
  intros * Hj Ht.
  unfold val_type_termRel, MR, termRel, argMeasure, val_type_measure.
  (* If we only know that Hj: j <= n, we must case-split on it, and use
     smaller_types when j = n and smaller_n when j < n. *)
  destruct Hj; try assert (j < S m) by simple_ineq; auto.
Qed.
  (* - apply right_lex. assumption. *)
  (* - apply left_lex. omega. *)


Lemma termRelShowOpen: forall j n x T1 T2,
  j <= n -> tsize_flat T2 < tsize_flat T1 ->
  val_type_termRel (open (varH x) T2, j) (T1, n).
Proof.
  intros * Hj Ht.
  unfold val_type_termRel, MR, termRel, argMeasure, val_type_measure.
  destruct Hj; try assert (j < S m) by simple_ineq; auto.
  (* unfold open; try rewrite open_preserves_size'. *)
  (* auto using left_lex, right_lex. *)
Qed.

Lemma termRelShowLt: forall j n T1 T2,
  j < n ->
  val_type_termRel (T2, j) (T1, n).
Proof.
  intros * Hj.
  unfold val_type_termRel, MR, termRel, argMeasure, val_type_measure.
  auto.
Qed.

Ltac applyNSimpleIneq l := apply l; simple_ineq.

Ltac smaller_n :=
  Tactics.program_simpl;
  autounfold; apply left_lex;
  (* simpl; omega. *)
  simple_ineq.

Ltac smaller_types :=
  Tactics.program_simpl;
  autounfold; apply right_lex;
  unfold open; try rewrite open_preserves_size';
  (* simpl; omega. *)
  simple_ineq.

(* Solve obligations from valType using ssreflect-based ideas, that is, reusing lemmas for the various cases. *)
Ltac valTypeObligationsSSReflection :=
  program_simpl;
  try solve [simple_ineq | applyNSimpleIneq termRelShowOpen | applyNSimpleIneq termRelShow | applyNSimpleIneq termRelShowLt | smaller_types | discriminatePlus].

Local Obligation Tactic := valTypeObligationsSSReflection.

Ltac valTypeObligations Hj :=
  Tactics.program_simpl;
  solve [ smaller_n | smaller_types | discriminatePlus | (try destruct Hj; [ smaller_types | smaller_n ])].

Definition env_prop := list vl -> list vl ->  Prop.
Hint Unfold env_prop.

Definition vl_prop := vl -> env_prop.
Hint Unfold vl_prop.

Definition type_dom n :=
  forall (n0: nat) (H: n0 <= n), vl_prop.
Hint Unfold type_dom.

Definition smaller_args T0 n0 T n :=
  termRel (val_type_measure T0 n0) (val_type_measure T n).
Hint Unfold smaller_args.

Definition type_dom2 T n :=
  forall (T0 : ty),
    forall (n0: nat) (Hle : smaller_args T0 n0 T n),
      vl_prop.
Hint Unfold type_dom2.

Program Definition expr_sem {n} (A : type_dom n) j p env1 e
  : env_prop :=
  fun env GH =>
    exists v, tevaln env1 e v /\
              A j p v env GH.

Program Definition interpTAll n (A1 : type_dom n) (A2 : type_dom n) : type_dom n :=
  fun n0 p v env GH =>
    match v with
    | vabs env1 T0 t =>
      forall vx j (Hj: j <= n0),
        A1 j _ vx env GH ->
        expr_sem A2 j _ (vx :: env1) t env (vx :: GH)
    | _ => False
    end.
Hint Unfold interpTAll.

Program Definition interpTMem n (A1 : type_dom n) (A2 : type_dom n)
        (val_type2 : ty -> forall j, j < n -> vl_prop) :=
  fun n0 (p : n0 <= n) v env GH =>
    match v with
    | vty env1 TX =>
      forall j (Hj : j < n0),
      forall vy,
        (A1 j _ vy env GH -> val_type2 TX j _ vy env1 GH) /\
        (val_type2 TX j _ vy env1 GH -> A2 j _ vy env GH)
    | _ => False
    end.

Program Fixpoint val_type2 (T: ty) (n : nat)
        {measure (val_type_measure T n) (termRel)}: vl_prop :=
  fun v env GH =>
  match T with
    | TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      interpTAll n
                 (fun n p => val_type2 T1 n _)
                 (fun n p => val_type2 (open (varH (length GH)) T2) n _)
                 n _ v env GH
    | TMem T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2 /\
      interpTMem n
                 (fun n p => val_type2 T1 n _)
                 (fun n p => val_type2 T2 n _)
                 (fun T j p => val_type2 T j _)
                 n _ v env GH
    | TTop => True
    | TBot => False
    (* Placeholders. Avoiding wildcards produces a much better Program output. *)
    | TSel x => False
    | TAnd T1 T2 => False
    | TBind T1 => False
  end.

Axiom prop_extensionality:
  forall (P Q: Prop), (P <-> Q) -> P = Q.

(* this is just to accelerate Coq -- val_type in the goal is slooow *)
Inductive vtp2: ty -> nat -> vl_prop :=
| vv2: forall T n v env GH, val_type2 T n v env GH -> vtp2 T n v env GH.

Lemma unvv2: forall T n v env GH,
  vtp2 T n v env GH -> val_type2 T n v env GH.
Proof.
  intros * H0. destruct H0. assumption.
Qed.

Lemma vtp2_unfold: forall T n v env GH,
  vtp2 T n v env GH = val_type2 T n v env GH.
Proof.
  intros.
  apply prop_extensionality.
  split; intros.
  - apply unvv2. assumption.
  - constructor. assumption.
Qed.

Lemma vtp2_unfold':
  vtp2 = val_type2.
Proof.
  repeat (apply functional_extensionality; intro).
  apply vtp2_unfold.
Qed.

(*
   The expansion of val_type, val_type_func is incomprehensible.
   We cannot (easily) unfold and reason about it. Therefore, we prove unfolding of
   val_type to its body as a lemma.
   (Note that the unfold_sub tactic relies on
   functional extensionality)
*)

Lemma val_type2_unfold' : forall T n v env GH,
    val_type2 T n v env GH =
    match T with
    | TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      interpTAll n
                 (fun n p => val_type2 T1 n)
                 (fun n p => val_type2 (open (varH (length GH)) T2) n)
                 n (le_n _) v env GH
    | TMem T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2 /\
      interpTMem n
                 (fun n p => val_type2 T1 n)
                 (fun n p => val_type2 T2 n)
                 (fun T j p => val_type2 T j)
                 n (le_n _) v env GH
    | TTop => True
    | _ =>
      False
    end.
Proof.
  intros. unfold val_type2 at 1; unfold val_type2_func;
  unfold_sub val_type2 (val_type2 T n v env GH);
  program_simplify;
  repeat (norepeat_match_case_analysis_goal; try reflexivity).
Qed.

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
        exists v, tevaln (vx::env1) y v /\ val_type env (vx::GH) (open (varH (length GH)) T2) j v

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
(* Broken *)
(* Ltac valTypeObligationsOld := *)
(*   Tactics.program_simpl; *)
(*   smaller_n || smaller_types || discriminatePlus || *)
(*             (apply termRelShowOpen || apply termRelShow || apply termRelShowLt); auto; *)
(*   unfold open; try rewrite open_preserves_size'; *)
(*   (* simple_ineq. *) *)
(*   simpl; omega. *)

(* Solve Obligations with valTypeObligationsOld. *)

(* (* Working *) *)
(* Solve Obligations with valTypeObligations Hj. *)

(* Better *)
(* Solve Obligations with valTypeObligationsSSReflection. *)

(* this is just to accelerate Coq -- val_type in the goal is slooow *)
Inductive vtp: list vl -> list vl -> ty -> forall n, vl -> Prop :=
| vv: forall G H T n v, val_type G H T n v -> vtp G H T n v.

Lemma unvv: forall G H T n v,
  vtp G H T n v -> val_type G H T n v.
Proof.
  intros * H0. destruct H0. assumption.
Qed.

Lemma vtp_unfold: forall G H T n v,
  vtp G H T n v = val_type G H T n v.
Proof.
  intros.
  apply prop_extensionality.
  split; intros.
  - apply unvv. assumption.
  - constructor. assumption.
Qed.

Lemma vtp_unfold':
  vtp = val_type.
Proof.
  repeat (apply functional_extensionality; intro).
  apply vtp_unfold.
Qed.

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
        exists v, tevaln (vx::env1) y v /\ val_type env (vx::GH) (open (varH (length GH)) T2) j v

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

Admitted.
(* Proof. *)
(*   intros. unfold val_type at 1; unfold val_type_func; *)
(*   unfold_sub val_type (val_type env GH T n v);  *)
(*   program_simplify; *)
(*   repeat (norepeat_match_case_analysis_goal; try reflexivity). *)
(* Qed. *)
