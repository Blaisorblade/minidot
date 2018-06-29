Require Import Omega.
Require Import Equations.Equations.
Require Import tactics.

Require Import dot_storeless_tidy.
Require Import dot_storeless_subst_aux.
Require Import dot_storeless_wfrel_aux.
Require Import tactics.

Definition venv := list dms.
Definition tenv := list ty.
Hint Unfold venv.
Hint Unfold tenv.

Inductive R_env (k : nat) : venv -> tenv -> Set :=
| R_nil :
    R_env k [] []
| R_cons : forall T v env G,
    R_env k env G ->
    vtp (open 0 (VObj v) T) k (tvar (VObj v)) ->
    R_env k (v :: env) (T :: G)
.
Hint Constructors R_env.

Lemma R_env_mon: forall G env m n,
    R_env n env G ->
    m <= n ->
    R_env m env G.
Proof. intros * Henv; induction Henv; eauto. Qed.
Hint Resolve R_env_mon.

Lemma wf_length : forall k vs ts,
                    R_env k vs ts ->
                    (length vs = length ts).
Proof. intros * H; induction H; simpl; congruence. Qed.
Hint Resolve wf_length.

Hint Constructors Forall.

Program Definition etp T k e :=
  expr_sem k T (fun k _ => vtp T k) k _ e.

Lemma etp_closed: forall T k v,
    etp T k v -> @wf ty [] T.
Proof. unfold etp; intros; simp expr_sem in *; tauto. Qed.
Hint Resolve etp_closed.

Hint Rewrite map_length.

Definition vtpEnvSomeCore T k v env :=
  exists T', subst_all_k (length env) (map VObj env) T = Some T' /\
        vtp T' k v.

Definition vtpEnvSome T k v env :=
  tm_closed 0 0 v /\ wf env T /\ vtpEnvSomeCore T k v env.

Lemma vtpEnvSome_closed:
  forall T k v env, vtpEnvSome T k v env -> wf env T.
Proof. unfold vtpEnvSome, wf, closed_ty; program_simpl. Qed.
Hint Resolve vtpEnvSome_closed.

Definition etpEnvSomeCore T k e l env : Prop :=
  forall v j,
    evalToSome env e v l k j ->
    vtpEnvSomeCore T (k - j) v env.

Definition etpEnvSome T k e l env :=
  tm_closed 0 (length env) e /\ wf env T /\ etpEnvSomeCore T k e l env.

Lemma etpEnvSome_closed: forall T k v l env,
    etpEnvSome T k v l env -> wf env T.
Proof. unfold etpEnvSome; program_simpl. Qed.
Hint Resolve etpEnvSome_closed.

Definition sem_type_some (G : tenv) (T : ty) (e: tm) :=
  wf G T /\ tm_closed 0 (length G) e /\
      forall k env (Henv: R_env k env G), etpEnvSomeCore T k e 0 env.

Lemma sem_type_some_closed : forall G T e,
    sem_type_some G T e -> wf G T.
Proof. unfold sem_type_some; program_simpl. Qed.

Definition sem_subtype_some (G : tenv) (T1 T2: ty) :=
  wf G T1 /\ wf G T2 /\
      forall e (HwfE : tm_closed 0 (length G) e),
      forall k env (Henv : R_env k env G),
        etpEnvSomeCore T1 k e 0 env -> etpEnvSomeCore T2 k e 0 env.

Definition sem_vl_subtype_some (G : tenv) (T1 T2: ty) :=
  wf G T1 /\ wf G T2 /\
      forall v (HwfV : tm_closed 0 0 v),
      forall k env (Henv : R_env k env G),
        vtpEnvSomeCore T1 k v env -> vtpEnvSomeCore T2 k v env.

Lemma sem_subtype_some_closed1 : forall G T1 T2,
    sem_subtype_some G T1 T2 -> wf G T1.
Proof. unfold sem_subtype_some; program_simpl. Qed.

Lemma sem_subtype_some_closed2 : forall G T1 T2,
    sem_subtype_some G T1 T2 -> wf G T2.
Proof. unfold sem_subtype_some; program_simpl. Qed.

Lemma sem_vl_subtype_some_closed1 : forall G T1 T2,
    sem_vl_subtype_some G T1 T2 -> wf G T1.
Proof. unfold sem_vl_subtype_some; program_simpl. Qed.

Lemma sem_vl_subtype_some_closed2 : forall G T1 T2,
    sem_vl_subtype_some G T1 T2 -> wf G T2.
Proof. unfold sem_vl_subtype_some; program_simpl. Qed.

Hint Resolve sem_type_some_closed
     sem_subtype_some_closed1
     sem_subtype_some_closed2
     sem_vl_subtype_some_closed1
     sem_vl_subtype_some_closed2.

Ltac lenG_to_lenEnv :=
  try match goal with
  | H: R_env _ ?env ?G |- _ =>
    replace (length G) with (length env) in * by (eauto using wf_length)
  end.

Lemma env_dms_closed: forall k env G l, R_env k env G -> length env = l -> Forall (dms_closed 0 1) env.
Proof.
  induction env; intros * Henv Hl; subst; inverts Henv; constructor; simpl; eauto using Forall_impl.
  assert (tm_closed 0 0 (tvar (VObj a))) by (eauto using vtp_v_closed); repeat inverts_closed; eauto.
Qed.

Hint Resolve env_dms_closed.

Lemma tm_closed_upgrade: forall i k k1 v,
  tm_closed i k v -> k <= k1 -> tm_closed i k1 v.
Proof. unmut_lemma closed_upgrade_rec. Qed.
Hint Resolve tm_closed_upgrade.

Lemma vl_subtype_some_to_subtype_some : forall G T1 T2
    (Hsub: sem_vl_subtype_some G T1 T2), sem_subtype_some G T1 T2.
Proof. unfold sem_subtype_some, sem_vl_subtype_some, etpEnvSomeCore; intuition eauto 10. Qed.
Hint Resolve vl_subtype_some_to_subtype_some.

Hint Unfold wf sem_type_some sem_subtype_some sem_vl_subtype_some.

Ltac to_vl_stp L :=
  unfold sem_vl_subtype_some, vtpEnvSomeCore;
    intuition eauto; ev;
      simpl in *; repeat better_case_match; try congruence; injectHyps;
        eauto using L.

Lemma sem_vl_and_stp1 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_vl_subtype_some G (TAnd T1 T2) T1.
Proof. to_vl_stp and_stp1. Qed.

Lemma sem_and_stp1 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_subtype_some G (TAnd T1 T2) T1.
Proof. eauto using vl_subtype_some_to_subtype_some, sem_vl_and_stp1. Qed.

Lemma sem_vl_and_stp2 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_vl_subtype_some G (TAnd T1 T2) T2.
Proof. to_vl_stp and_stp2. Qed.

Lemma sem_and_stp2 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_subtype_some G (TAnd T1 T2) T2.
Proof. eauto using vl_subtype_some_to_subtype_some, sem_vl_and_stp2. Qed.

Hint Resolve Nat.le_max_l Nat.le_max_r.
Lemma some_max_lemma: forall j k,
  max (S (S k)) (max (S k) j) <=
  S (max (S k) j).
Proof.
  intros;
  rewrite Nat.succ_max_distr;
  eapply Nat.max_lub_iff;
  split_conj; eauto using Nat.max_lub_iff.
  (* , Nat.le_max_r, Nat.le_max_l. *)
Qed.
Hint Resolve some_max_lemma.

Hint Resolve closed_upgrade.

Lemma etp_vtp_j: forall e v k j l T env,
    evalToSome env e v l k j -> etpEnvSome T k e l env -> j <= k -> vtpEnvSome T (k - j) v env.
Proof.
  intros.
  unfold etpEnvSome, etpEnvSomeCore, vtpEnvSome, vtpEnvSomeCore in *; ev.
  assert (exists T', subst_all_k (length env) (map VObj env) T = Some T' /\ vtp T' (k - j) v) by eauto; ev;
    intuition eauto.
Qed.
Hint Resolve etp_vtp_j.

Lemma step_det: forall t u1 u2, step t u1 -> step t u2 -> u1 = u2.
Proof.
  intros * H1; gen u2; induction H1;
    intros * H2; inverse H2; try optFuncs_det; eauto;
    try match goal with
        | H : step (tvar (VObj _)) _ |- _ => inversion H
        end;
    fequal; eauto.
Qed.
Hint Resolve step_det.

Lemma steps_irred_det: forall t v1 v2 j1 j2, steps t v1 j1 -> steps t v2 j2 -> irred v1 -> irred v2 -> v1 = v2 /\ j1 = j2.
Proof.
  unfold irred; intros * Hs1 Hs2 Hv1 Hv2; gen j2; induction Hs1; intros; inverse Hs2;
    try solve [exfalso; eauto | eauto];
    (* Why do I need parens for `by`'s argument? *)
    enough (t2 = v2 /\ i = i0) by (intuition eauto);
    match goal with
    | H1 : step ?a ?b, H2 : step ?a ?c |- _ =>
      assert (b = c) as -> by eauto using step_det
    end; eauto.
Qed.
Hint Resolve steps_irred_det.

Lemma evalToSome_det: forall env e l k j1 j2 {v1} {v2},
    evalToSome env e v1 l k j1 ->
    evalToSome env e v2 l k j2 ->
    v1 = v2 /\ j1 = j2.
Proof. unfold evalToSome; intros; ev; optFuncs_det; eapply steps_irred_det; eauto. Qed.
Hint Resolve evalToSome_det.

Lemma subst_env: forall v v' env, tm_subst_all_k 0 [] v = Some v' ->
                             tm_closed 0 0 v ->
                             tm_subst_all_k 0 env v = Some v'.
Admitted.

Lemma vtpEnvSomeCoreToEval: forall T k v env, vtpEnvSomeCore T k v env -> tm_closed 0 0 v -> evalToSome env v v 0 k 0.
  unfold vtpEnvSomeCore, evalToSome; intros; ev;
    intuition eauto using subst_env.
Qed.

Lemma subtype_to_vl_subtype : forall G T1 T2,
    sem_subtype_some G T1 T2 -> sem_vl_subtype_some G T1 T2.
Proof.
  (* unfold sem_subtype, sem_vl_subtype; intros; intuition eauto; *)
  (*   destruct (vl_to_tm v) as [e Heval]; firstorder eauto. *)
  unfold sem_subtype_some, sem_vl_subtype_some; intros * (? & ? & Hsub).
    split_conj; eauto;
      intros * Hcl * Henv * HvT1.
    unfold etpEnvSomeCore in *.
    assert (evalToSome env v v 0 k 0) by eauto using vtpEnvSomeCoreToEval.
    replace k with (k - 0) by omega;
    eapply Hsub with (e := v); eauto; intros.
    assert (v0 = v /\ j = 0) as (-> & ->) by eauto using evalToSome_det.
    replace (k - 0) with k by omega.
    eauto.
Qed.
