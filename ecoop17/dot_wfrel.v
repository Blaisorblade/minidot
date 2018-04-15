Require Import tactics.

(* Require Import Arith.Wf_nat. *)
(* Require Import Program. *)
(* Import WfExtensionality. *)
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import dot_base.

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
  rewrite open_preserves_size;
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
  val_type_termRel (open (varF x) T2, j) (T1, n).
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
  unfold open; try rewrite open_preserves_size;
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

Definition env_prop := list vl ->  Prop.
Hint Unfold env_prop.

Definition vl_prop := vl -> env_prop.
Hint Unfold vl_prop.

Definition smaller_args T0 n0 T n :=
  termRel (val_type_measure T0 n0) (val_type_measure T n).
Hint Unfold smaller_args.

Require Import dot_eval.

Definition type_dom n :=
  forall (n0: nat) (H: n0 <= n), vl_prop.
Hint Unfold type_dom.

Program Definition expr_sem {n} (A : type_dom n) k (p : k <= n) env1 e
  : env_prop :=
  fun env =>
    exists v j, tevalSn env1 e v j /\
              A (k - j) _ v env.

(* Definition type_dom2 T n := *)
(*   forall (T0 : ty), *)
(*     forall (n0: nat) (Hle : smaller_args T0 n0 T n), *)
(*       vl_prop. *)
(* Hint Unfold type_dom2. *)

Program Definition interpTAll n (A1 : type_dom n) (A2 : type_dom n) : type_dom n :=
  fun n0 p v env =>
    match v with
    | vabs env1 T0 t =>
      forall vx k (Hj: k <= n0),
        A1 k _ vx env ->
        expr_sem A2 k _ (vx :: env1) t (vx :: env)
    | _ => False
    end.

Program Definition interpTMem n (A1 : type_dom n) (A2 : type_dom n)
        (val_type : ty -> forall j, j < n -> vl_prop) :=
  fun n0 (p : n0 <= n) v env =>
    match v with
    | vty env1 TX =>
      forall j (Hj : j < n0),
      forall vy,
        (A1 j _ vy env -> val_type TX j _ vy env1) /\
        (val_type TX j _ vy env1 -> A2 j _ vy env)
    | _ => False
    end.

Program Definition interpTSel0 n i (env0: list vl)
        (val_type : ty -> forall j, j < n -> vl_prop): type_dom n :=
  fun n0 (p : n0 <= n) v env =>
    match indexr i env0 with
    | Some (vty env1 TX) =>
      forall j (Hk : j < n0), val_type TX j _ v env1
    | _ => False
    end.

Program Definition interpTSel n x
        (val_type : ty -> forall j, j < n -> vl_prop) :=
  fun n0 (p : n0 <= n) v env =>
    match x with
    | varF i => interpTSel0 n i env val_type n0 p v env
    | varB _ => False
     end.

Program Definition interpTAnd n (A1 : type_dom n) (A2 : type_dom n) : type_dom n :=
  fun n0 p v env =>
    A1 n0 _ v env /\
    A2 n0 _ v env.

Program Fixpoint val_type (T: ty) (n : nat)
        {measure (val_type_measure T n) (termRel)}: vl_prop :=
  fun v env =>
  match T with
    | TAll T1 T2 =>
      closed_ty 0 (length env) T1 /\ closed_ty 1 (length env) T2 /\
      interpTAll n
                 (fun n p => val_type T1 n _)
                 (fun n p => val_type (open (varF (length env)) T2) n _)
                 n _ v env
    | TMem T1 T2 =>
      closed_ty 0 (length env) T1 /\ closed_ty 0 (length env) T2 /\
      interpTMem n
                 (fun n p => val_type T1 n _)
                 (fun n p => val_type T2 n _)
                 (fun T j p => val_type T j _)
                 n _ v env
    | TTop => True
    | TBot => False
    | TSel x =>
      interpTSel n x (fun T j p => val_type T j _)
                n _ v env
    | TAnd T1 T2 =>
      interpTAnd n
                 (fun n p => val_type T1 n _)
                 (fun n p => val_type T2 n _)
                 n _ v env
    (* Placeholders. Avoiding wildcards produces a much better Program output. *)
    | TBind T1 =>
      closed_ty 1 (length env) T1 /\
      @val_type (open (varF (length env)) T1) n _ v (v::env)
  end.

Axiom prop_extensionality:
  forall (P Q: Prop), (P <-> Q) -> P = Q.

(* this is just to accelerate Coq -- val_type in the goal is slooow *)
Inductive vtp: ty -> nat -> vl_prop :=
| vv: forall T n v env, val_type T n v env -> vtp T n v env.

Lemma unvv: forall T n v env,
  vtp T n v env -> val_type T n v env.
Proof.
  intros * H0. destruct H0. assumption.
Qed.

Lemma vtp_to_val_type_base: forall T n v env,
  vtp T n v env = val_type T n v env.
Proof.
  intros.
  apply prop_extensionality.
  split; intros.
  - apply unvv. assumption.
  - constructor. assumption.
Qed.

Lemma vtp_to_val_type:
  vtp = val_type.
Proof.
  repeat (apply functional_extensionality; intro).
  apply vtp_to_val_type_base.
Qed.

(*
   The expansion of val_type, val_type_func is incomprehensible.
   We cannot (easily) unfold and reason about it. Therefore, we prove unfolding of
   val_type to its body as a lemma.
   (Note that the unfold_sub tactic relies on
   functional extensionality)
*)

Lemma val_type_unfold : forall T n v env,
    val_type T n v env =
    match T with
    | TAll T1 T2 =>
      closed_ty 0 (length env) T1 /\ closed_ty 1 (length env) T2 /\
      interpTAll n
                 (fun n p => val_type T1 n)
                 (fun n p => val_type (open (varF (length env)) T2) n)
                 n (le_n _) v env
    | TMem T1 T2 =>
      closed_ty 0 (length env) T1 /\ closed_ty 0 (length env) T2 /\
      interpTMem n
                 (fun n p => val_type T1 n)
                 (fun n p => val_type T2 n)
                 (fun T j p => val_type T j)
                 n (le_n _) v env
    | TTop => True
    | TSel x =>
      interpTSel n x (fun T j p => val_type T j)
                n (le_n _) v env
    | TAnd T1 T2 =>
      interpTAnd n
                 (fun n p => val_type T1 n)
                 (fun n p => val_type T2 n)
                 n (le_n _) v env
    | TBind T1 =>
      closed_ty 1 (length env) T1 /\
      val_type (open (varF (length env)) T1) n v (v::env)
    | _ =>
      False
    end.
Proof.
  Import WfExtensionality.
  intros;
  unfold val_type at 1; unfold val_type_func;
  unfold_sub val_type (val_type T n v env);
  program_simplify;
  repeat (case_match; try reflexivity).
Qed.