Require Import Omega.
Require Import Equations.Equations.
Require Import tactics.

Require Import dot_storeless_tidy.
Require Import dot_storeless_subst_aux.
Require Import dot_storeless_wfrel_aux.

Definition venv := list dms.
Definition tenv := list ty.
Hint Unfold venv.
Hint Unfold tenv.

Hint Rewrite map_length.

Definition vtpEnvCore T k v env :=
  exists T', subst_all (map VObj env) T = Some T' /\
        vtp T' k v.

Definition vtpEnv T k v env :=
  wf env T /\ vtpEnvCore T k v env.

Lemma vtpEnvCore_v_closed: forall T n v env, vtpEnvCore T n v env -> tm_closed 0 0 v.
Proof. unfold vtpEnvCore; intros; ev; eauto. Qed.
Hint Resolve vtpEnvCore_v_closed.

Lemma vtpEnv_v_closed: forall T n v env, vtpEnv T n v env -> tm_closed 0 0 v.
Proof. unfold vtpEnv; intros; intuition eauto 2. Qed.
Hint Resolve vtpEnv_v_closed.

Lemma vtpEnv_closed:
  forall T k v env, vtpEnv T k v env -> wf env T.
Proof. unfold vtpEnv, wf, closed_ty; program_simpl. Qed.
Hint Resolve vtpEnv_closed.

Lemma vtpEnvCore_mon: forall T v env m n,
    vtpEnvCore T n v env ->
    m <= n ->
    vtpEnvCore T m v env.
Proof. unfold vtpEnvCore; intros; ev; eauto. Qed.
Hint Extern 5 (vtpEnvCore _ _ _ _) => try_once vtpEnvCore_mon.

Lemma vtpEnv_mon: forall T v env m n,
    vtpEnv T n v env ->
    m <= n ->
    vtpEnv T m v env.
Proof. unfold vtpEnv; intuition eauto. Qed.
Hint Extern 5 (vtpEnv _ _ _ _) => try_once vtpEnv_mon.

Definition etpEnvCore T k e env : Prop :=
  forall v j kmj,
    evalToSome env e v k j ->
    kmj = k - j ->
    vtpEnvCore T kmj v env.

Definition etpEnv T k e env :=
  tm_closed (length env) 0 e /\ wf env T /\ etpEnvCore T k e env.

Lemma etpEnv_closed: forall T k v env,
    etpEnv T k v env -> wf env T.
Proof. unfold etpEnv; program_simpl. Qed.
Hint Resolve etpEnv_closed.

Inductive R_env (k : nat) : venv -> tenv -> Set :=
| R_nil :
    R_env k [] []
| R_cons : forall T v env G,
    R_env k env G ->
    vtpEnv T k (tvar (VObj v)) (v :: env) ->
    R_env k (v :: env) (T :: G)
.
Hint Constructors R_env.

Lemma R_env_mon: forall G env m n,
    R_env n env G ->
    m <= n ->
    R_env m env G.
Proof. intros * Henv; induction Henv; eauto. Qed.
Hint Extern 5 (R_env _ _ _) => try_once R_env_mon.

Lemma wf_length : forall k vs ts,
                    R_env k vs ts ->
                    (length vs = length ts).
Proof. intros * H; induction H; simpl; congruence. Qed.
Hint Resolve wf_length.

Ltac lenG_to_lenEnv :=
  try match goal with
  | H: R_env _ ?env ?G |- _ =>
    replace (length G) with (length env) in * by (eauto using wf_length)
  end.

Hint Constructors Forall.

Lemma env_dms_closed: forall k env G, R_env k env G -> Forall (dms_closed 0 1) env.
Proof.
  induction env; intros * Henv; subst; inverts Henv; constructor; simpl; eauto using Forall_impl.
  assert (tm_closed 0 0 (tvar (VObj a))) by eauto; repeat inverts_closed; eauto.
Qed.
Hint Resolve env_dms_closed.

Definition sem_type (G : tenv) (T : ty) (e: tm) :=
  wf G T /\ tm_closed 0 (length G) e /\
      forall k env (Henv: R_env k env G), etpEnvCore T k e env.

Lemma sem_type_closed : forall G T e,
    sem_type G T e -> wf G T.
Proof. unfold sem_type; program_simpl. Qed.

Definition sem_subtype (G : tenv) (T1 T2: ty) :=
  wf G T1 /\ wf G T2 /\
      forall e (HwfE : tm_closed (length G) 0 e),
      forall k env (Henv : R_env k env G),
        etpEnvCore T1 k e env -> etpEnvCore T2 k e env.

Definition sem_vl_subtype (G : tenv) (T1 T2: ty) :=
  wf G T1 /\ wf G T2 /\
      forall v,
      forall k env (Henv : R_env k env G),
        vtpEnvCore T1 k v env -> vtpEnvCore T2 k v env.

Lemma sem_subtype_closed1 : forall G T1 T2,
    sem_subtype G T1 T2 -> wf G T1.
Proof. unfold sem_subtype; program_simpl. Qed.

Lemma sem_subtype_closed2 : forall G T1 T2,
    sem_subtype G T1 T2 -> wf G T2.
Proof. unfold sem_subtype; program_simpl. Qed.

Lemma sem_vl_subtype_closed1 : forall G T1 T2,
    sem_vl_subtype G T1 T2 -> wf G T1.
Proof. unfold sem_vl_subtype; program_simpl. Qed.

Lemma sem_vl_subtype_closed2 : forall G T1 T2,
    sem_vl_subtype G T1 T2 -> wf G T2.
Proof. unfold sem_vl_subtype; program_simpl. Qed.

Hint Resolve sem_type_closed
     sem_subtype_closed1
     sem_subtype_closed2
     sem_vl_subtype_closed1
     sem_vl_subtype_closed2.

Lemma vl_subtype_to_subtype : forall G T1 T2
    (Hsub: sem_vl_subtype G T1 T2), sem_subtype G T1 T2.
Proof. unfold sem_subtype, sem_vl_subtype, etpEnvCore; intuition eauto. Qed.
Hint Resolve vl_subtype_to_subtype.

Hint Unfold wf sem_type sem_subtype sem_vl_subtype.

Ltac to_vl_stp L :=
  unfold sem_vl_subtype, vtpEnvCore;
    intuition eauto; ev;
      simpl in *; repeat better_case_match; try congruence; injectHyps;
        eauto using L.

Lemma sem_vl_and_stp1 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_vl_subtype G (TAnd T1 T2) T1.
Proof. to_vl_stp and_stp1. Qed.

Lemma sem_and_stp1 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_subtype G (TAnd T1 T2) T1.
Proof. eauto using vl_subtype_to_subtype, sem_vl_and_stp1. Qed.

Lemma sem_vl_and_stp2 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_vl_subtype G (TAnd T1 T2) T2.
Proof. to_vl_stp and_stp2. Qed.

Lemma sem_and_stp2 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_subtype G (TAnd T1 T2) T2.
Proof. eauto using vl_subtype_to_subtype, sem_vl_and_stp2. Qed.

Lemma etp_vtp_core_j:
  forall e v k j kmj l T env,
  evalToSome env e v k j ->
  tm_closed l 0 e -> wf env T -> etpEnvCore T k e env ->
  l = length env ->
  kmj = k - j ->
  wf env T /\ vtpEnvCore T kmj v env.
Proof.
  unfold etpEnv, etpEnvCore, vtpEnv, vtpEnvCore; intros; ev;
    assert (exists T', subst_all (map VObj env) T = Some T' /\ vtp T' (k - j) v) by eauto; ev;
      intuition eauto.
Qed.
Hint Resolve etp_vtp_core_j.

Hint Extern 5 (_ = _ :> nat) => ineq_solver.
Lemma etp_vtp_core:
  forall e v k T env,
  evalToSome env e v k 0 ->
  tm_closed (length env) 0 e -> wf env T -> etpEnvCore T k e env ->
  wf env T /\ vtpEnvCore T k v env.
Proof. eauto. Qed.
Hint Resolve etp_vtp_core.

Lemma etp_vtp_j: forall e v k j l T env,
    evalToSome env e v k j -> etpEnv T k e env ->
    l = k - j ->
    vtpEnv T l v env.
Proof. unfold etpEnv, vtpEnv; intros; ev; eauto. Qed.
Hint Resolve etp_vtp_j.

Lemma etp_vtp: forall e v k T env,
    evalToSome env e v k 0 -> etpEnv T k e env -> vtpEnv T k v env.
Proof. eauto 2. Qed.
Hint Resolve etp_vtp.

(* I think these lemmas are all false, so vtp_env_j needs its local closure assumption. *)

(* Lemma tm_subst_all_closed_inv: forall e e' env l, tm_closed 0 0 e' -> tm_subst_all env e = Some e' -> length env = l -> tm_closed l  0 e. Admitted. *)
(* Lemma steps_closed_inv: forall e v j, steps e v j -> tm_closed 0 0 v -> tm_closed 0 0 e. Admitted. *)
(* Lemma step_closed_inv: forall e v, step e v -> tm_closed 0 0 v -> tm_closed 0 0 e. *)
(* Proof. *)
(*   intros; induction H; repeat inverts_closed; eauto; unfold subst_tm in *; *)
(*     destruct t12; simpl in *; try discriminate; inverts H1. *)
(*   - repeat constructor. *)
(*   - inverts H1; admit. *)
(*   - unfold subst_tm in *. destruct t12; simpl in *; try discriminate; inverts H1. *)

Lemma vtp_etp_core_j: forall e v T env k j kmj l,
    vtpEnvCore T kmj v env ->
    wf env T ->
    tm_closed l 0 e ->
    evalToSome env e v k j ->
    kmj = k - j ->
    l = length env ->
    etpEnvCore T k e env.
Proof.
  unfold etpEnvCore, vtpEnvCore; intros; ev; subst;
  match goal with
  | H0: evalToSome ?env ?e ?v0 ?k ?j0, H1: evalToSome ?env ?e ?v1 ?k ?j1
    |- _ =>
    assert (v1 = v0 /\ j1 = j0) as (-> & ->) by eauto
  end; intuition eauto.
Qed.
Hint Resolve vtp_etp_core_j.

Lemma vtp_etp_core: forall e v T env k l,
    vtpEnvCore T k v env ->
    wf env T ->
    tm_closed l 0 e ->
    evalToSome env e v k 0 ->
    l = length env ->
    etpEnvCore T k e env.
Proof. eauto. Qed.
Hint Resolve vtp_etp_core.

Lemma vtp_etp_j: forall e v T env k j kmj l,
    vtpEnv T kmj v env ->
    tm_closed l 0 e ->
    evalToSome env e v k j ->
    kmj = k - j ->
    l = length env ->
    etpEnv T k e env.
Proof. unfold etpEnv, vtpEnv; intros; subst; intuition eauto. Qed.
Hint Resolve vtp_etp_j.

Lemma vtp_etp: forall e v T env k l,
    vtpEnv T k v env ->
    tm_closed l 0 e ->
    evalToSome env e v k 0 ->
    l = length env ->
    etpEnv T k e env.
Proof. eauto. Qed.
Hint Resolve vtp_etp.

Lemma vtpEnvCoreToEval: forall T k v env, vtpEnvCore T k v env -> evalToSome env v v k 0.
Proof. unfold vtpEnvCore, evalToSome; intros; ev; intuition eauto 7. Qed.
Hint Resolve vtpEnvCoreToEval.

Lemma vtp_extend : forall vx v k env T,
  vtpEnv T k v env ->
  vtpEnv T k v (vx::env).
Proof.
  unfold vtpEnv, vtpEnvCore, wf; simpl; intros; ev; intuition eauto using map_length.
Qed.

Lemma subtype_to_vl_subtype : forall G T1 T2,
    sem_subtype G T1 T2 -> sem_vl_subtype G T1 T2.
Proof.
  unfold sem_subtype, sem_vl_subtype, wf; intros * (? & ? & Hsub);
    intuition idtac; lenG_to_lenEnv.
  (* Either: *)
  (* eapply Hsub with (e := v); eauto 7. *)
  (* Or, faster: *)
  assert (tm_closed (length env) 0 v) by eauto.
  eapply Hsub with (e := v); eauto.
Qed.
Hint Resolve subtype_to_vl_subtype.

Require Import PropExtensionality.
Lemma vl_sub_equiv: sem_subtype = sem_vl_subtype.
Proof.
  repeat (apply functional_extensionality; intro); apply propositional_extensionality;
    split; eauto.
Qed.
Hint Rewrite vl_sub_equiv.

(* Shorter proof than the one in storeless_tidy. *)
(* Lemma index_max : forall X vs n (T: X), *)
(*                        index n vs = Some T -> *)
(*                        n < length vs. *)
(* Proof. *)
(*   induction vs; intros * H; inversion H; simpl; case_match; beq_nat; subst; unfold lt in *; eauto. *)
(* Qed. *)
Hint Resolve index_max.

Lemma index_open_swap: forall x env v vx n,
    index x env = Some v ->
    Forall (vr_closed 0 0) env ->
    index x (vx :: env) = Some v /\
    v = vr_open n vx v.
Proof.
  intros; simpl;
    assert (vr_closed 0 0 v) by apply_Forall;
    assert (x < length env) by eauto;
    case_match; beq_nat; subst; try omega;
      unmut_lemma closed_no_open_rec; intuition eauto.
Qed.
Hint Resolve index_open_swap.

Lemma subst_all_open_swap_rec:
  (forall v v0 env vx n l,
      vr_subst_all env v = Some v0 ->
      Forall (vr_closed 0 0) env ->
      length env = l ->
      exists v1,
        vr_subst_all (vx :: env) (vr_open n (VarF l) v) = Some v1 /\
        v1 = vr_open n vx v0) /\
  (forall T T0 env vx n l,
      subst_all env T = Some T0 ->
      Forall (vr_closed 0 0) env ->
      length env = l ->
      exists T1,
        subst_all (vx :: env) (open n (VarF l) T) = Some T1 /\
        open n vx T0 = T1) /\
  (forall t t0 env vx n l,
      tm_subst_all env t = Some t0 ->
      Forall (vr_closed 0 0) env ->
      length env = l ->
      exists t1,
        tm_subst_all (vx :: env) (tm_open n (VarF l) t) = Some t1 /\
        t1 = tm_open n vx t0) /\
  (forall d d0 env vx n l,
      dm_subst_all env d = Some d0 ->
      Forall (vr_closed 0 0) env ->
      length env = l ->
      exists d1,
        dm_subst_all (vx :: env) (dm_open n (VarF l) d) = Some d1 /\
        d1 = dm_open n vx d0) /\
  (forall d d0 env vx n l,
      dms_subst_all env d = Some d0 ->
      Forall (vr_closed 0 0) env ->
      length env = l ->
      exists d1,
        dms_subst_all (vx :: env) (dms_open n (VarF l) d) = Some d1 /\
        d1 = dms_open n vx d0).
Proof.
  apply syntax_mutind; cbn -[index]; intros; injectHyps; eauto; simpl in *;
    repeat case_match_hp; injectHyps; try discriminate;
    simpl; eexists; split_conj; fequal; trivial;
      try solve [repeat (better_case_match; beq_nat; subst; simpl); eauto].

  (* repeat (better_case_match; try beq_nat; subst; try beq_nat; simpl); eauto. *)
  (* try solve [repeat (better_case_match; try beq_nat; subst; try beq_nat; simpl); eauto]. *)
  all: repeat match goal with
              | Hind : context [ ?f (_ :: _) (?sth_open _ _ ?T) ] |- context [ match ?f (_ :: _) (?sth_open ?n ?l ?T) with _ => _ end ] =>
                lets (? & -> & ?) : Hind n ___; eauto
              end; repeat fequal; eauto.
Qed.

Lemma vr_subst_all_open_swap: forall v v0 env vx n l,
    vr_subst_all env v = Some v0 ->
    Forall (vr_closed 0 0) env ->
    length env = l ->
    exists v1,
      vr_subst_all (vx :: env) (vr_open n (VarF l) v) = Some v1 /\
      v1 = vr_open n vx v0.
Proof. unmut_lemma subst_all_open_swap_rec. Qed.
Lemma subst_all_open_swap: forall T T0 env vx n l,
    subst_all env T = Some T0 ->
    Forall (vr_closed 0 0) env ->
    length env = l ->
    exists T1,
      subst_all (vx :: env) (open n (VarF l) T) = Some T1 /\
      open n vx T0 = T1.
Proof. unmut_lemma subst_all_open_swap_rec. Qed.
Lemma tm_subst_all_open_swap: forall t t0 env vx n l,
    tm_subst_all env t = Some t0 ->
    Forall (vr_closed 0 0) env ->
    length env = l ->
    exists t1,
      tm_subst_all (vx :: env) (tm_open n (VarF l) t) = Some t1 /\
      t1 = tm_open n vx t0.
Proof. unmut_lemma subst_all_open_swap_rec. Qed.
Lemma dm_subst_all_open_swap: forall d d0 env vx n l,
    dm_subst_all env d = Some d0 ->
    Forall (vr_closed 0 0) env ->
    length env = l ->
    exists d1,
      dm_subst_all (vx :: env) (dm_open n (VarF l) d) = Some d1 /\
      d1 = dm_open n vx d0.
Proof. unmut_lemma subst_all_open_swap_rec. Qed.
Lemma dms_subst_all_open_swap: forall d d0 env vx n l,
    dms_subst_all env d = Some d0 ->
    Forall (vr_closed 0 0) env ->
    length env = l ->
    exists d1,
      dms_subst_all (vx :: env) (dms_open n (VarF l) d) = Some d1 /\
      d1 = dms_open n vx d0.
Proof. unmut_lemma subst_all_open_swap_rec. Qed.

Hint Resolve
     vr_subst_all_open_swap
     subst_all_open_swap
     tm_subst_all_open_swap
     dm_subst_all_open_swap
     dms_subst_all_open_swap.

(* Awkward to state with vtp? *)
Lemma vtp_tbind_i: forall env v T n,
    vtpEnv (open 0 (VarF (length env)) T) n (tvar (VObj v)) (v :: env) ->
    Forall (dms_closed 0 1) env ->
    closed_ty 0 (length env) (TBind T) -> (* Ensures that TBind T doesn't mention `VarF (length env)`. *)
    vtpEnv (TBind T) n (tvar (VObj v)) env.
Proof.
  unfold vtpEnv, vtpEnvCore, vtp, closed_ty; simpl; intros; inverts_closed; simpl_vtp; split_conj; eauto.
  assert (exists T', subst_all (map VObj env) T = Some T' /\ closed 0 1 T') as (T'base & Hsubst & ?) by eauto;
    rewrite Hsubst;
    eexists; split_conj; trivial;
      simpl_vtp;
      split_conj; trivial.
  (* Or *)
  (* rewrite val_type_unfold_eq; simpl. *)
  assert (exists T', subst_all (VObj v :: map VObj env) (open 0 (VarF (length env)) T) = Some T' /\ open 0 (VObj v) T'base = T') by eauto (* subst_all_open_swap *);
    ev; optFuncs_det; assumption.
Qed.
