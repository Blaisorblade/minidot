Require Import dot_storeless_tidy.
Require Import Omega.
Require Import tactics.

(* Require Import dot_monads. *)

Definition tsize_flat := tsize.

Definition val_type_measure T (k : nat) := (existT (fun _ => nat) k (tsize_flat T)).
Hint Unfold val_type_measure.

Definition vl := tm.
Definition vset := vl -> Prop.
Hint Unfold vset.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.
Hint Constructors lexprod.

Set Implicit Arguments.
Check lexprod.
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

Hint Extern 5 (_ < tsize_flat _) =>
  unfold open;
  rewrite <- open_preserves_size;
  simple_ineq.


Lemma termRelShowOpen: forall j n x T1 T2,
  j <= n -> tsize_flat T2 < tsize_flat T1 ->
  val_type_termRel (open 0 (VarF x) T2, j) (T1, n).
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
  unfold open; try rewrite <- open_preserves_size;
  (* simpl; omega. *)
  simple_ineq.

(* Solve obligations from valType using ssreflect-based ideas, that is, reusing lemmas for the various cases. *)
Ltac valTypeObligationsSSReflection :=
  program_simpl;
  try solve [simple_ineq | applyNSimpleIneq termRelShowOpen | applyNSimpleIneq termRelShow | applyNSimpleIneq termRelShowLt | smaller_types | discriminatePlus].

Ltac valTypeObligations Hj :=
  Tactics.program_simpl;
  solve [ smaller_n | smaller_types | discriminatePlus | (try destruct Hj; [ smaller_types | smaller_n ])].

(* Definition env_prop := list vl ->  Prop. *)
(* Hint Unfold env_prop. *)

Definition vl_prop := vl -> Prop.
Hint Unfold vl_prop.

Definition smaller_args T0 n0 T n :=
  termRel (val_type_measure T0 n0) (val_type_measure T n).
Hint Unfold smaller_args.

Definition pretype_dom n :=
  forall (n0: nat) (H: n0 <= n), vl_prop.
Hint Unfold pretype_dom.

Definition closed_ty i j T := closed j i T.
Definition wf {A} (G : list A) T := closed_ty 0 (length G) T.

Check dot_storeless_tidy.step.
Inductive steps t0 : tm -> nat -> Prop :=
| Step0 : steps t0 t0 0
| StepS : forall t1 t2 i, step t0 t1 -> steps t1 t2 i -> steps t0 t2 (S i).

Definition irred t0 := not (exists t1, step t0 t1).


Print lexprod.
From Equations Require Import Equations.
Print lexprod.

Equations expr_sem {n} (T : ty) (A : pretype_dom n) k (p : k <= n) (t : tm) : Prop :=
  expr_sem T A k p t :=
  (* If evaluation terminates in at most k steps without running out of fuel, *)
  closed_ty 0 0 T /\
  forall v j,
    steps t v j ->
    irred v ->
    j <= k ->
    (* then evaluation did not get stuck and the result satisfies A. *)
    exists v, A (k - j) _ v.

(* Check WellFounded *)
(*                   (MR val_type_termRel *)
(*                      (fun *)
(*                         hypspack : sigma ty *)
(*                                      (fun _ : ty => *)
(*                                       sigma nat (fun _ : nat => ())) => *)
(*                       (fun *)
(*                          hypspack0 : sigma ty *)
(*                                        (fun _ : ty => *)
(*                                         sigma nat (fun _ : nat => ())) => *)
(*                        (pr1 hypspack0, pr1 (pr2 hypspack0))) hypspack)). *)

(* Program Definition expr_sem {n} T (A : pretype_dom n) k (p : k <= n) t : Prop := *)
(*   (* If evaluation terminates in at most k steps without running out of fuel, *) *)
(*   closed_ty 0 0 T /\ *)
(*   forall v j, *)
(*     steps t v j -> *)
(*     irred v -> *)
(*     j <= k -> *)
(*     (* then evaluation did not get stuck and the result satisfies A. *) *)
(*     exists v, A (k - j) _ v. *)

(* Definition meas := MR lt tsize_flat. *)
(* Lemma w *)
Instance WF_val_type_termRel: WellFounded val_type_termRel := wf_val_type_termRel.

Local Obligation Tactic := valTypeObligationsSSReflection.

Equations val_type (Tn: argPair) (t : tm) : Prop :=
  val_type Tn t by rec Tn val_type_termRel :=
    val_type (pair T (S n)) t := val_type (pair T n) t;
    val_type (pair T O) t := True.


Next Obligation. Qed.
Preterm.
(* Transparent val_type_unfold. *)
Next Obligation.
  (* destruct Tn as [? n]; induction n; rewrite val_type_unfold_eq; unfold val_type_unfold; constructor; auto. *)
  (* apply val_type_ind_ind; intros; try constructor; eauto. *)
  (* eauto. *)
  (* funelim (val_type Tn t). *)
  (* rewrite val_type_equation_1; constructor. *)
  (* rewrite val_type_equation_2; constructor. *)
  (* funelim (val_type Tn t). *)
  (* Print val_type_ind. *)
Admitted.
Next Obligation. Qed.

(*     val_type T n := False. *)
(* Equations val_type (T: ty) (n : nat): vl_prop := *)
(*         (* {measure (val_type_measure T n) (termRel)}: vl_prop := *) *)
(*   val_type T n by rec (T, n) val_type_termRel := *)
(*     val_type T n := False. *)
