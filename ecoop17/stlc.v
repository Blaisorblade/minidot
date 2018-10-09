Require Import tactics.
Require Export dot_infrastructure_lemmas.

Require Export Arith.EqNat.
Require Export Arith.Le.

Inductive tm : Set :=
| tvar : id -> tm
| tabs : tm -> tm
| tapp : tm -> tm -> tm
| tnat : nat -> tm.

Inductive vl : Set :=
(* a closure for a lambda abstraction *)
| vabs : list vl (*H*) -> tm -> vl
| vnat: nat -> vl.

Inductive ty : Set :=
| TFun : ty -> ty -> ty
| TNat : ty.

Notation tenv := (list ty).
Notation venv := (list vl).

Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.

(* de Bruijn levels! *)
Inductive has_type: tenv -> tm -> ty -> Prop :=
| t_var : forall gamma x T,
    indexr x gamma = Some T ->
    has_type gamma (tvar x) T
| t_abs : forall gamma t S T,
    has_type (S :: gamma) t T ->
    has_type gamma (tabs t) (TFun S T)
| t_app : forall gamma f t S T,
    has_type gamma f (TFun S T) ->
    has_type gamma t S ->
    has_type gamma (tapp f t) T
| t_nat: forall gamma n, has_type gamma (tnat n) TNat
.
Hint Constructors has_type.

Example ex1: has_type [TNat] (tvar 0) TNat. eauto. Qed.
Example ex2: has_type [TFun TNat TNat] (tabs (tvar 1)) (TFun TNat TNat). eauto. Qed.

Hint Extern 5 => match goal with
                | |- indexr _ _ = _ => progress cbn; eauto
                end.

Example ex__apply: has_type [TFun TNat TNat] (tabs (tabs (tapp (tvar 1) (tvar 2))))
                          (TFun (TFun TNat TNat) (TFun TNat TNat)). eauto 6. Qed.

(* Adapted from dot_monads.v *)
Require Import dot_monads.

Fixpoint tevalSM (t: tm) (n: nat) (env: venv): option (option vl * nat) :=
  match n with
  | 0 => None
  | S n =>
    match t with
    | tvar x       => ret (indexr x env, 0)
    (* | ttyp T       => ret (vty env T) *)
    | tabs y     => ret (vabs env y)
    | tnat n     => ret (vnat n)
    | tapp tf ta   =>
      va <- tevalSM ta n env;
      vf <- tevalSM tf n env;
      match vf with
      | vabs env2 tbody =>
        logStep 1 (tevalSM tbody n (va :: env2))
      | _ => error
      end
    (* | tunpack tx ty => *)
    (*   vx <- tevalSM tx n env; *)
    (*   logStep 1 (tevalSM ty n (vx::env)) *)
    end
  end.

Fixpoint tevalS (t: tm) (n: nat) (env: venv): option (option vl * nat) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | tvar x       => Some (indexr x env, 0)
        (* | ttyp T       => Some (Some (vty env T), 0) *)
        | tabs y     => Some (Some (vabs env y), 0)
        | tnat n     => Some (Some (vnat n), 0)
        | tapp ef ex   =>
          match tevalS ex n env with
            | None => None
            | Some (None, k1) => Some (None, k1)
            | Some (Some vx, k1) =>
              match tevalS ef n env with
                | None => None
                | Some (None, k2) => Some (None, k1 + k2)
                | Some (Some (vabs env2 ey), k2) =>
                  logStep (k1 + k2 + 1) (tevalS ey n (vx::env2))
                | Some (Some _, k2) => Some (None, k1 + k2)
              end
          end
        (* | tunpack ex ey => *)
        (*   match tevalS ex n env with *)
        (*     | None => None *)
        (*     | Some (None, k) => Some (None, k) *)
        (*     | Some (Some vx, k1) => *)
        (*       logStep (k1 + 1) (tevalS ey n (vx::env)) *)
        (*   end *)
      end
  end.

Ltac better_case_match_ex := try better_case_match; try beq_nat; injectHyps; try discriminate.
Theorem evalMs_equiv: forall n env t, tevalSM t n env = tevalS t n env.
Proof.
  intros; revert env t; induction n; simpl_unfold_monad; unfold logStep; try reflexivity;
    intros;
    repeat progress
      (try better_case_match_ex;
       repeat fequalSafe;
       repeat rewrite IHn in *;
       try abstract (reflexivity || discriminate || omega)).
Qed.
(** Define "evaluation with enough fuel".
    We can show that adding more fuel to evaluation that doesn't time out gives
    the same result. But we can also build that in our assumptions.
 *)
Definition tevalSnmOpt env e optV k nm := forall n, n > nm -> tevalS e n env = Some (optV, k).
Definition tevalSnm env e v k nm := tevalSnmOpt env e (Some v) k nm.
Definition tevalSnOpt env e optV k := exists nm, tevalSnmOpt env e optV k nm.
Definition tevalSn env e v k := tevalSnOpt env e (Some v) k.

Hint Transparent tevalSnOpt tevalSnm tevalSn.
Ltac unfold2tevalSnmOpt := unfold tevalSn, tevalSnOpt, tevalSnm in *.
Ltac unfoldTeval := unfold2tevalSnmOpt; unfold tevalSnmOpt in *.

Ltac n_is_succ_hp :=
  ev; match goal with
  | H : forall n, n > ?nm -> _ |- _ =>
    let H2 := fresh "H" in
    lets ? : H (S nm) __; eauto; clear H; simpl in H2; try unfold logStep in H2
  end.

(** [tevalSnmOpt] (expanded) is monotonic relative to [nm]. This does not
    follow from properties of [tevalS], but by construction of [tevalSnmOpt]. *)
Lemma tevalS_kripke_mono: forall env e optV k nm1,
    (forall n, n > nm1 -> tevalS e n env = Some (optV, k)) ->
    forall nm2, nm2 >= nm1 ->
    forall n, n > nm2 -> tevalS e n env = Some (optV, k).
Proof. eauto. Qed.
Hint Resolve tevalS_kripke_mono.

(** [tevalSnmOpt] is monotonic relative to [nm]. This does not follow from
    properties of [tevalS], but by construction of [tevalSnmOpt]. *)
Lemma tevalSnmOpt_mono: forall env e optV k nm1,
    tevalSnmOpt env e optV k nm1 ->
    forall nm2, nm2 >= nm1 ->
    tevalSnmOpt env e optV k nm2.
Proof. intros; unfoldTeval; eauto using tevalS_kripke_mono. Qed.

Lemma max_bigger_both: forall n1 n2, max n1 n2 >= n1 /\ max n1 n2 >= n2.
  intuition eauto using Nat.le_max_l, Nat.le_max_r.
Qed.

Ltac alignTevalAssumptions :=
  unfoldTeval;
  match goal with
  | H1 : forall n, n > ?nm1 -> tevalS ?t n ?env = Some ?t1 , H2 : forall n, n > ?nm2 -> tevalS ?t n ?env = Some ?t2 |- _ =>
    let nm := fresh "nm" in
    remember (max (nm1) (nm2)) as nm;
    assert (nm >= nm1 /\ nm >= nm2) as (? & ?) by (subst; eauto using max_bigger_both);
    assert (tevalSnmOpt env t (fst t1) (snd t1) nm) by (simpl; unfoldTeval; eauto);
    assert (tevalSnmOpt env t (fst t2) (snd t2) nm) by (simpl; unfoldTeval; eauto);
    clear H1 H2;
    unfoldTeval
  end.

Lemma tevalS_det: forall optV1 optV2 env t j1 j2 nm1 nm2,
  (forall n : nat, n > nm1 -> tevalS t n env = Some (optV1, j1)) ->
  (forall n : nat, n > nm2 -> tevalS t n env = Some (optV2, j2)) ->
  optV1 = optV2 /\ j1 = j2.
Proof.
  intros; alignTevalAssumptions;
    repeat n_is_succ_hp; optFuncs_det; eauto.
Qed.

(* Experiment on different way of writing tevalS_det: can we make auto happier about injecting p1 = p2 than splitting it? *)
Lemma tevalS_det2: forall optV1 optV2 env t j1 j2 nm1 nm2,
  (forall n : nat, n > nm1 -> tevalS t n env = Some (optV1, j1)) ->
  (forall n : nat, n > nm2 -> tevalS t n env = Some (optV2, j2)) ->
  (optV1, j1) = (optV2, j2).
Proof.
  intros; alignTevalAssumptions;
    repeat n_is_succ_hp; optFuncs_det; eauto.
Qed.

Tactic Notation "try_once_tac" constr(T) tactic(tac) :=
  match goal with
  | H : usedLemma T |- _ => fail 1
  | _ => markUsed T; tac
  end.

Definition injectHyps_marker := 0.
Hint Extern 5 => try_once_tac injectHyps_marker injectHyps.
(* Hint Extern 5 => optFuncs_det. *)

(* XXX this used tevalS_detp, the next uses _det, seems _detp might not be that useful here yet... *)
Lemma tevalS_det_optV: forall optV1 optV2 env t j1 j2 nm1 nm2,
  (forall n : nat, n > nm1 -> tevalS t n env = Some (optV1, j1)) ->
  (forall n : nat, n > nm2 -> tevalS t n env = Some (optV2, j2)) ->
  optV1 = optV2.
Proof. intros. lets ?: tevalS_det2 optV1 optV2 ___; eauto. Qed.

(* Hint Extern 5 => ev. *)

Lemma tevalS_det_j: forall optV1 optV2 env t j1 j2 nm1 nm2,
  (forall n : nat, n > nm1 -> tevalS t n env = Some (optV1, j1)) ->
  (forall n : nat, n > nm2 -> tevalS t n env = Some (optV2, j2)) ->
  j1 = j2.
Proof. intros; lets ?: tevalS_det optV1 optV2 ___; ev; eauto. Qed.

Hint Resolve tevalS_det_optV tevalS_det_j.

Lemma tevalSnmOpt_det_optV: forall env t optV1 optV2 j1 j2 nm1 nm2,
    tevalSnmOpt env t optV1 j1 nm1 ->
    tevalSnmOpt env t optV2 j2 nm2 ->
    optV1 = optV2.
Proof. (* firstorder eauto. (* Or: *) *) intros; unfoldTeval; eauto. Qed.

Lemma tevalSnmOpt_det_j: forall env t optV1 optV2 j1 j2 nm1 nm2,
    tevalSnmOpt env t optV1 j1 nm1 ->
    tevalSnmOpt env t optV2 j2 nm2 ->
    j1 = j2.
Proof. unfoldTeval; eauto. Qed.

Hint Resolve tevalSnmOpt_det_optV tevalSnmOpt_det_j.

Lemma tevalSnmOpt_det: forall env t optV1 optV2 j1 j2 nm1 nm2,
    tevalSnmOpt env t optV1 j1 nm1 ->
    tevalSnmOpt env t optV2 j2 nm2 ->
    optV1 = optV2 /\ j1 = j2.
Proof. eauto. Qed.

(* Convince Coq that if n > m then n = S n' for some n', then there's enough
   fuel to perform one evaluation step. *)
Lemma n_to_Sn: forall n m, n > m -> exists n', n = S n'.
  intros; destruct n; [ exfalso; omega | eauto].
Qed.
Hint Unfold gt ge lt.
Hint Transparent gt ge lt.

Tactic Notation "n_is_succ'" simple_intropattern(P) :=
  unfold gt, ge, lt in *;
  match goal with
  | [H : S ?m <= ?n |- _] => lets [P ->]: n_to_Sn H
  end.

Ltac n_is_succ := let n' := fresh "n" in n_is_succ' n'.

Ltac step_eval := n_is_succ; simpl in *.
(* Hint Extern 5 => step_eval. *)

Lemma teval_var: forall env x,
  exists optV, tevalSnOpt env (tvar x) optV 0 /\ indexr x env = optV.
Proof. unfoldTeval; eexists; split_conj; try exists 0; intros; try step_eval; trivial. Qed.
Hint Resolve teval_var.

(*******************)
(* Logical relation. *)

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Equations.Equations.

(*******************)
(* Define language infrastructure. *)

Definition vl_prop := vl -> Prop.
Hint Unfold vl_prop.

Fixpoint tsize (T: ty): nat :=
  match T with
  | TNat => 1
  | TFun T1 T2 => 1 + tsize T1 + tsize T2
  end.
Definition tsize_rel (T1 T2: ty) := tsize T1 < tsize T2.
Hint Extern 1 (tsize_rel _ _) => unfold tsize_rel; eauto.

Ltac eval_det :=
  unfold2tevalSnmOpt; ev;
  match goal with
  | H1 : tevalSnmOpt _ _ _ _ _, H2 : tevalSnmOpt _ _ _ _ _ |- _ =>
    lets (? & ?) : tevalSnmOpt_det H1 H2 ___
  end; injectHyps.

(** Fuel monotonicity: If evaluation does not time out, increasing fuel preserves the result.
 **** Proof sketch.
      By induction on the available fuel [n] in the initial evaluation and case
      analysis on terms.

      In the inductive step, recursive calls happen with fuel [n - 1], hence by
      the induction hypothesis they satisfy fuel monotonicity, the recursive
      calls with more fuel give the same result, hence overall evaluation with
      more fuel gives the same result.
 *)
Lemma tevalS_mono: forall n e env optV, tevalS e n env = Some optV -> forall m, m >= n -> tevalS e m env = Some optV.
Proof.
  (** [tevalS_det] applies the induction hypothesis to recursive calls. *)
  Ltac tevalS_det n m' IHn :=
    match goal with
    | H1: tevalS ?e n ?env = Some ?r1, H2 : tevalS ?e m' ?env = ?r2 |- _ =>
      let H := fresh "H" in
      assert (tevalS e m' env = Some r1) as H by (eapply IHn; auto 1);
      rewrite H in *; clear H
    end.

  induction n; intros * Heval * Hmn; try solve [inverse Heval];
  n_is_succ' m';

  generalize dependent optV; generalize dependent n; destruct e;
    intros; simpl in *; unfold logStep in *;
    trivial;

  repeat (better_case_match_ex; try tevalS_det n m' IHn); trivial.
Qed.
Hint Resolve tevalS_mono.

Module Type vtp_arg.
  Parameter vtp : ty -> vl_prop.
  Parameter expr_sem : vl_prop -> tm -> venv -> Prop.
End vtp_arg.

Module Envs (VTP: vtp_arg).
  Import VTP.

  (* Copy-pasted and modularizable. *)
  Inductive R_env : venv -> tenv -> Set :=
  | R_nil :
      R_env [] []
  | R_cons : forall T v env G,
      R_env env G ->
      vtp T v ->
      R_env (v :: env) (T :: G).
  Hint Constructors R_env.

  Lemma wf_length : forall vs ts,
      R_env vs ts ->
      (length vs = length ts).
  Proof. intros * H; induction H; simpl; congruence. Qed.

  Ltac lenG_to_lenEnv :=
    try match goal with
        | H: R_env ?env ?G |- _ =>
          replace (length G) with (length env) in * by (eauto using wf_length)
        end.

  Lemma R_env_to_indexr_success: forall G env x T, indexr x G = Some T -> R_env env G -> exists v, indexr x env = Some v.
    intros * HT Henv; induction Henv; simpl in *;
      [ discriminate |
        lenG_to_lenEnv;
        repeat (better_case_match; beq_nat); eauto].
  Qed.
  Hint Resolve R_env_to_indexr_success.

  Lemma R_env_to_vtp: forall G env x T v, indexr x G = Some T -> indexr x env = Some v -> R_env env G -> vtp T v.
  Proof.
    intros * HT Hv Henv; induction Henv; simpl in *;
      [ discriminate |
        lenG_to_lenEnv;
        repeat (better_case_match; beq_nat); eauto].
  Qed.
  Hint Resolve R_env_to_vtp.
  (* Copy-pasted and modularizable, until at least here. *)

  Definition etp T e env :=
    expr_sem (fun v => vtp T v) e env.

  (* Semantic typing *)
  Definition sem_type (G : tenv) (T : ty) (e: tm) :=
    forall env,
      R_env env G ->
      etp T e env.
End Envs.

Module LR_Type_Soundness.
(* Only expr_sem changes here. *)

(* Maybe make both normal definitions, or at least Program Definitions? Let's limit equations weird rules? *)
Definition expr_sem (A : vl_prop) (t : tm) (env: venv): Prop :=
  forall optV j,
    tevalSnOpt env t optV j -> exists v, optV = Some v /\ A v.

(* Non-step-indexed unary logical relation. *)
Equations vtp (T: ty) (v : vl) : Prop :=
  vtp T t by rec T tsize_rel :=
  vtp TNat (vnat n) := True;
  vtp (TFun T1 T2) (vabs env body) := forall v, vtp T1 v -> expr_sem (fun v => vtp T2 v) body (v :: env);
  vtp _ _ := False.
Solve All Obligations with program_simpl.

Example ex0 : vtp (TFun TNat TNat) (vabs [] (tvar 0)).
Proof.
  simp vtp; unfold expr_sem; intros.
  unfoldTeval; n_is_succ_hp; eauto.
Qed.

Include Envs.

Lemma vtp_etp: forall e v j nm T env,
    tevalSnm env e v j nm -> vtp T v -> etp T e env.
Proof. unfold etp, expr_sem in *; intros; unfoldTeval; ev; eauto. Qed.
Hint Resolve vtp_etp.

Lemma etp_vtp: forall e v j nm T env,
    tevalSnm env e v j nm -> etp T e env -> vtp T v.
Proof. unfold etp, expr_sem; unfold2tevalSnmOpt; intros * ? H; edestruct H; ev; eauto. Qed.
(* Unused *)
(* Hint Resolve etp_vtp. *)

Lemma fund_t_abs: forall G T1 T2 t,
  sem_type (T1 :: G) T2 t ->
  sem_type G (TFun T1 T2) (tabs t).
Proof.
  unfold sem_type; simpl; intros; eapply vtp_etp with (nm := 0).
  - unfoldTeval; intros; step_eval; trivial.
  - unfold etp in *; simp vtp; eauto.
Qed.

Lemma fund_t_var: forall G x T, indexr x G = Some T -> sem_type G T (tvar x).
Proof.
  unfold sem_type, etp, expr_sem; intros;
  (* repeat (intros; hnf). *)
  pose proof (teval_var env x); eval_det; subst.
  edestruct R_env_to_indexr_success; eauto.
Qed.

(** Fundamental property, application case.
 **** Proof sketch.
      It's easy to show that the result has the right type, *if it exists*, but
      showing it exists is harder.

      That is, what's harder is showing that if evaluation of the application [t
      = tapp t1 t2] terminates without timeout, then it does not fail. That's
      because the various proof steps are closely interlocked.

      Evaluation of [t]  proceeds by evaluating [t2], then [t1], and then
      performing application, in the evaluation monad; failures (timeouts and
      runtime errors) interrupt evaluation and propagate.
      If [t] does not timeout, then [t2] does not time out (by case analysis);
      then, since [t2] is semantically well-typed, its evaluation does not fail.
      Then, evaluation [t] proceeds to [t1], which by the same reasoning neither
      times out nor fails; moreover, it produces a closure.
      Finally, evaluating [t] proceeds to applying the closure, which by the
      same reasoning neither times out nor fails, producing a well-typed result. *)
Lemma fund_t_app: forall G T1 T2 t1 t2, sem_type G (TFun T1 T2) t1 -> sem_type G T1 t2 -> sem_type G T2 (tapp t1 t2).
Proof.
  unfold sem_type, etp, expr_sem; unfoldTeval;
  intros * Hfun Harg ? ? * [nmR HappEv].

  (* Various implementations of the same case analysis are possible.
     It's faster to only do as much case analysis as strictly needed. *)


  (* V1 Fast *)
  n_is_succ_hp;
    (** We must show that nmR is at least one, since that's required by the
        hypothesis of semantic expression typing for Hfun and Harg. *)
    destruct nmR;
    (* The iteration counts are optimized for speed, but it's also OK to do all *)
    (*   case splits in advance as in V1.1. *)
    do 2 better_case_match_ex; edestruct Harg; ev; eauto; try discriminate; injectHyps;
      do 3 better_case_match_ex; edestruct Hfun; ev; eauto; try discriminate; injectHyps;
        repeat better_case_match_ex; simp vtp in *; unfold expr_sem in *; unfoldTeval; eauto; contradiction.

  (* V1.1 less fast, more maintainable. *)
  (* n_is_succ_hp; destruct nmR; *)
  (*   repeat better_case_match_ex; edestruct Harg; ev; eauto; try discriminate; injectHyps; *)
  (*     better_case_match_ex; edestruct Hfun; ev; eauto; try discriminate; injectHyps; *)
  (*       simp vtp in *; unfold expr_sem in *; unfoldTeval; eauto; contradiction. *)
Qed.

Lemma fund_t_nat: forall G n,
  sem_type G TNat (tnat n).
Proof.
  unfold sem_type; intros; eapply vtp_etp with (nm := 0).
  - unfoldTeval; intros; step_eval; trivial.
  - unfold etp in *; simp vtp; eauto.
Qed.

(** Fundamental property.
    Proved by induction on typing derivations. *)
Theorem fundamental: forall G t T, has_type G t T -> sem_type G T t.
Proof. intros * Htp; induction Htp; eauto using fund_t_var, fund_t_nat, fund_t_abs, fund_t_app. Qed.

(** Type soundness: If evaluation of a well-typed program terminates, the result
    is not a runtime error. Proved as a corollary of the [fundamental] property. *)
Theorem sound: forall G t T env optV j, has_type G t T ->
    R_env env G ->
    tevalSnOpt env t optV j ->
    exists v, optV = Some v /\ vtp T v.
Proof. intros; edestruct fundamental; ev; eauto. Qed.
(* Concluding tevalSn env t v j -> vtp T v would talk only about successful
   evaluations, not about runtime errors! *)

End LR_Type_Soundness.

(** Prove normalization: all terms evaluate. *)
Module normalization.
  Definition expr_sem (A : vl_prop) (t : tm) (env: venv): Prop :=
    exists v j,
      tevalSn env t v j /\ A v.

  (* Non-step-indexed reducibility *)
  Equations vtp (T: ty) (v : vl) : Prop :=
    vtp T t by rec T tsize_rel :=
    vtp TNat (vnat n) := True;
    vtp (TFun T1 T2) (vabs env body) := forall v, vtp T1 v -> expr_sem (fun v => vtp T2 v) body (v :: env);
    vtp _ _ := False.
  Solve All Obligations with program_simpl.

  Example ex0 : vtp (TFun TNat TNat) (vabs [] (tvar 0)).
  Proof.
    simp vtp; unfold expr_sem; unfoldTeval; intros.
    do 3 eexists; try exists 0; intros; try step_eval; eauto.
  Qed.

  (* Require Import Setoid. *)
  (* Stolen from https://github.com/coq/coq/issues/3814, and dangerous, but enable setoid_rewrite using equalities on the goal. *)
  (* Instance subrelation_eq_impl : subrelation eq impl. congruence. Qed. *)
  (* Instance subrelation_eq_flip_impl : subrelation eq (flip impl). congruence. Qed. *)

  Include Envs.

  Lemma vtp_etp: forall e v j nm T env,
      tevalSnm env e v j nm -> vtp T v -> etp T e env.
  Proof. unfold etp, expr_sem in *; intros; unfoldTeval; ev; eauto. Qed.
  Hint Resolve vtp_etp.

  Lemma etp_vtp: forall e v j nm T env,
      tevalSnm env e v j nm -> etp T e env -> vtp T v.
  Proof. unfold etp, expr_sem; unfold2tevalSnmOpt; intros; ev; eval_det; eauto. Qed.
  (* Unused *)
  (* Hint Resolve etp_vtp. *)

  Lemma fund_t_abs: forall G T1 T2 t,
      sem_type (T1 :: G) T2 t ->
      sem_type G (TFun T1 T2) (tabs t).
  Proof.
    unfold sem_type; simpl; intros; eapply vtp_etp with (nm := 0).
    - unfoldTeval; intros; step_eval; trivial.
    - unfold etp in *; simp vtp; eauto.
  Qed.

  Lemma fund_t_nat: forall G n,
      sem_type G TNat (tnat n).
  Proof.
    unfold sem_type; intros; eapply vtp_etp with (nm := 0).
    - unfoldTeval; intros; step_eval; trivial.
    - unfold etp in *; simp vtp; eauto.
  Qed.

  Lemma fund_t_var: forall G x T, indexr x G = Some T -> sem_type G T (tvar x).
  Proof.
    unfold sem_type, etp, expr_sem; intros.
    pose proof (teval_var env x).
    unfold2tevalSnmOpt; ev; subst.
    edestruct R_env_to_indexr_success as [? Hrew]; eauto.
    rewrite Hrew in *.
    repeat eexists; eauto.
  Qed.

  Lemma fund_t_app: forall G T1 T2 t1 t2, sem_type G (TFun T1 T2) t1 -> sem_type G T1 t2 -> sem_type G T2 (tapp t1 t2).
  Proof.
    unfold sem_type, etp, expr_sem; unfoldTeval.
    intros * Hfun Harg * Henv.
    specialize (Hfun _ Henv) as (v1 & j1 & (nm1 & Hev1) & Hvtp1);
    specialize (Harg _ Henv) as (v2 & j2 & (nm2 & Hev2) & Hvtp2).

    (* v1 is a function by semantic well-typing. *)
    destruct v1; simp vtp in *; try contradiction.
    unfold expr_sem in *; unfoldTeval.
    edestruct Hvtp1 as (vR & jR & (nmR & HevR) & HvtpR); eauto; clear Hvtp1.
    remember (max nm1 nm2) as nmA.
    remember (max nmA nmR) as nm.
    assert (nm >= nm1 /\ nm >= nm2 /\ nm >= nmR) as (? & ? & ?). {
      assert (nmA >= nm1 /\ nmA >= nm2) as (? & ?) by (subst; eauto using max_bigger_both);
        assert (nm >= nmA /\ nm >= nmR) as (? & ?) by (subst; eauto using max_bigger_both);
        intuition eauto.
    }

    (* Align all assumtions to use nm. *)
    repeat match goal with
    | H1 : forall n, n > ?nm1 -> tevalS ?t1 n ?env = Some ?r1 |- _ =>
      assert (tevalSnmOpt env t1 (fst r1) (snd r1) nm) by (simpl; unfoldTeval; eauto);
      clear H1
    end; unfoldTeval; simpl in *.
    remember (S nm) as nm'.

    do 2 eexists; split_conj; try exists (S nm'); eauto.

    intros; step_eval; unfold logStep in *;
    repeat match goal with
    | H : forall n, ?nm <= n -> _ |- _ => lets ?: H n0 __; eauto; clear H end.
    now repeat better_case_match_ex.
  Qed.

  (** Fundamental property.
      Proved by induction on typing derivations. *)
  Theorem fundamental: forall G t T, has_type G t T -> sem_type G T t.
  Proof. intros * Htp; induction Htp; eauto using fund_t_var, fund_t_nat, fund_t_abs, fund_t_app. Qed.

  (** Strong normalization: evaluation of a well-typed program terminates with a
      result of the right type. Proved as a corollary of the [fundamental] property.
   *)
  Theorem normalize: forall G t T env, has_type G t T ->
      R_env env G ->
      exists v j,
        tevalSn env t v j /\ vtp T v.
  Proof. intros; edestruct fundamental; ev; eauto. Qed.

  (** Type soundness: If evaluation of a well-typed program terminates, the result
      is not a runtime error. Proved as a corollary of [normalize]. *)
  Theorem sound: forall G t T env optV j, has_type G t T ->
      R_env env G ->
      tevalSnOpt env t optV j ->
      exists v, optV = Some v /\ vtp T v.
  Proof.
    (** [t] normalizes. *)
    intros; edestruct normalize; ev; eauto.
    (** Since evaluation is deterministic, the given evaluation has the same
        result, hence is sound. *)
    unfold2tevalSnmOpt; eval_det; eauto.
  Qed.
End normalization.
