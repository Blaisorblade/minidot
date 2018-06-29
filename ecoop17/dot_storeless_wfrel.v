Require Import Omega.
Require Import Equations.Equations.
Require Import tactics.

Require Import dot_storeless_tidy.
Require Import dot_storeless_subst_aux.
Require Import dot_storeless_wfrel_aux.
Require Import tactics.

Program Definition etp T k e :=
  expr_sem k T (fun k _ => vtp T k) k _ e.

Lemma etp_closed: forall T k v,
    etp T k v -> @wf ty [] T.
Proof. unfold etp; intros; simp expr_sem in *; tauto. Qed.
Hint Resolve etp_closed.

Hint Rewrite map_length.

Definition vtpEnvCore T k v env :=
  exists T', subst_all_k (length env) (map VObj env) T = Some T' /\
        vtp T' k v.

Definition vtpEnv T k v env :=
  tm_closed 0 0 v /\ wf env T /\ vtpEnvCore T k v env.

Lemma vtpEnv_closed:
  forall T k v env, vtpEnv T k v env -> wf env T.
Proof. unfold vtpEnv, wf, closed_ty; program_simpl. Qed.
Hint Resolve vtpEnv_closed.

Definition etpEnvCore T k e l env : Prop :=
  forall v j kmj,
    evalToSome env e v l k j ->
    kmj = k - j ->
    vtpEnvCore T kmj v env.

Definition etpEnv T k e l env :=
  tm_closed 0 (length env) e /\ wf env T /\ etpEnvCore T k e l env.

Lemma etpEnv_closed: forall T k v l env,
    etpEnv T k v l env -> wf env T.
Proof. unfold etpEnv; program_simpl. Qed.
Hint Resolve etpEnv_closed.

Definition sem_type (G : tenv) (T : ty) (e: tm) :=
  wf G T /\ tm_closed 0 (length G) e /\
      forall k env (Henv: R_env k env G), etpEnvCore T k e 0 env.

Lemma sem_type_closed : forall G T e,
    sem_type G T e -> wf G T.
Proof. unfold sem_type; program_simpl. Qed.

Definition sem_subtype (G : tenv) (T1 T2: ty) :=
  wf G T1 /\ wf G T2 /\
      forall e (HwfE : tm_closed 0 (length G) e),
      forall k env (Henv : R_env k env G),
        etpEnvCore T1 k e 0 env -> etpEnvCore T2 k e 0 env.

Definition sem_vl_subtype (G : tenv) (T1 T2: ty) :=
  wf G T1 /\ wf G T2 /\
      forall v (HwfV : tm_closed 0 0 v),
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
Proof. unfold sem_subtype, sem_vl_subtype, etpEnvCore; intuition eauto 10. Qed.
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
    evalToSome env e v l k j -> etpEnv T k e l env -> j <= k -> vtpEnv T (k - j) v env.
Proof.
  intros.
  unfold etpEnv, etpEnvCore, vtpEnv, vtpEnvCore in *; ev.
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

Lemma vtpEnvCoreToEval: forall T k v env, vtpEnvCore T k v env -> tm_closed 0 0 v -> evalToSome env v v 0 k 0.
  unfold vtpEnvCore, evalToSome; intros; ev;
    intuition eauto using subst_env.
Qed.

Lemma subtype_to_vl_subtype : forall G T1 T2,
    sem_subtype G T1 T2 -> sem_vl_subtype G T1 T2.
Proof.
  unfold sem_subtype, sem_vl_subtype, etpEnvCore; intros * (? & ? & Hsub);
    split_conj; eauto;
      intros;
    eapply Hsub with (e := v); omega || eauto using vtpEnvCoreToEval; intros.
    match goal with
      | H: evalToSome env v ?v0 0 k j |- _ =>
        assert (v0 = v /\ j = 0) as (-> & ->) by eauto using evalToSome_det, vtpEnvCoreToEval
    end; subst; replace (k - 0) with k in * by omega; eauto.
Qed.
