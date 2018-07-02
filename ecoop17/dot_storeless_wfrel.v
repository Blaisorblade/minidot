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

Hint Rewrite map_length.

Definition vtpEnvCore T k v env :=
  exists T', subst_all (map VObj env) T = Some T' /\
        vtp T' k v.

Definition vtpEnv T k v env :=
  tm_closed 0 0 v /\ wf env T /\ vtpEnvCore T k v env.

Lemma vtpEnv_closed:
  forall T k v env, vtpEnv T k v env -> wf env T.
Proof. unfold vtpEnv, wf, closed_ty; program_simpl. Qed.
Hint Resolve vtpEnv_closed.

Lemma vtpEnv_mon: forall T v env m n,
    vtpEnv T n v env ->
    m <= n ->
    vtpEnv T m v env.
Proof. unfold vtpEnv, vtpEnvCore in *; intros; ev; intuition eauto. Qed.
Hint Resolve vtpEnv_mon.

Lemma vtpEnv_v_closed: forall T n v env, vtpEnv T n v env -> tm_closed 0 0 v.
Proof. unfold vtpEnv in *; ev; intuition eauto. Qed.
Hint Resolve vtpEnv_v_closed.

Definition etpEnvCore T k e env : Prop :=
  forall v j kmj,
    evalToSome env e v k j ->
    kmj = k - j ->
    vtpEnvCore T kmj v env.

Definition etpEnv T k e env :=
  tm_closed 0 (length env) e /\ wf env T /\ etpEnvCore T k e env.

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
Hint Resolve R_env_mon.

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

Lemma env_dms_closed: forall k env G l, R_env k env G -> length env = l -> Forall (dms_closed 0 1) env.
Proof.
  induction env; intros * Henv Hl; subst; inverts Henv; constructor; simpl; eauto using Forall_impl.
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

(* XXX These hints are applied multiple times in a sequence, not good! *)
(* Remove Hints val_type_mon vtp_mon tm_closed_upgrade R_env_mon. *)
(* Hint Immediate val_type_mon vtp_mon tm_closed_upgrade R_env_mon. *)
(* Remove Hints val_type_mon vtp_mon tm_closed_upgrade. *)

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

Lemma etp_vtp_j: forall e v k j T env,
    evalToSome env e v k j -> etpEnv T k e env -> j <= k -> vtpEnv T (k - j) v env.
Proof.
  intros.
  unfold etpEnv, etpEnvCore, vtpEnv, vtpEnvCore in *; ev.
  assert (exists T', subst_all (map VObj env) T = Some T' /\ vtp T' (k - j) v) by eauto; ev;
    intuition eauto.
Qed.
Hint Resolve etp_vtp_j.


(* Lemma subst_env_ext1: forall v v' env vx i, tm_subst_all env v = Some v' -> *)
(*                              tm_closed 0 0 v -> *)
(*                              tm_subst_all (vx :: env) v = Some v'. *)
(* Proof. *)
(*   induction v; intros; simpl. *)
(*   - admit. *)
(*   - *)
(*       match goal with *)
(*       | Hind : context [ ?f _ _ ?s ] |- context [ match ?f ?k ?env ?s with _ => _ end ] => *)
(*         lets ->: Hind vx ___; eauto *)
(*       end. *)
(* . *)
(*     repeat (case_match; try discriminate). *)
(*     + *)
(*       inverts_closed. *)


(*       lets ?: IHv1 vx Heqo ___; eauto. *)
(*       lets ?: IHv2 vx Heqo0 ___; eauto. *)
(*       now repeat optFuncs_det. *)
(*     + inverts_closed; lets ? : IHv2 vx Heqo0 ___; eauto; now repeat optFuncs_det. *)
(*     + inverts_closed; lets ? : IHv1 vx Heqo ___; eauto; now repeat optFuncs_det. *)
(* Admitted. *)

Lemma vtpEnvCoreToEval: forall T k v env, vtpEnvCore T k v env -> tm_closed 0 0 v -> evalToSome env v v k 0.
  unfold vtpEnvCore, evalToSome; intros; ev;
    intuition eauto.
Qed.
Hint Resolve vtpEnvCoreToEval.

Lemma vtp_extend : forall vx v k env T,
  vtpEnv T k v env ->
  vtpEnv T k v (vx::env).
Proof.
  unfold vtpEnv, vtpEnvCore, wf; simpl; intros; ev; intuition eauto using map_length with upgrade.
Qed.

(* TODO First relate vtp and etp? *)
Lemma subtype_to_vl_subtype : forall G T1 T2,
    sem_subtype G T1 T2 -> sem_vl_subtype G T1 T2.
Proof.
  unfold sem_subtype, sem_vl_subtype, etpEnvCore; intros * (? & ? & Hsub);
    split_conj; eauto;
      intros;
    eapply Hsub with (e := v); omega || eauto with upgrade; intros.
    match goal with
      | H: evalToSome env v ?v0 k j |- _ =>
        assert (v0 = v /\ j = 0) as (-> & ->) by eauto
    end; subst; replace (k - 0) with k in * by omega; eauto.
Qed.
Hint Resolve subtype_to_vl_subtype.

Require Import PropExtensionality.
Lemma vl_sub_equiv: sem_subtype = sem_vl_subtype.
Proof.
  repeat (apply functional_extensionality; intro); apply propositional_extensionality;
    split; eauto.
Qed.
Hint Rewrite vl_sub_equiv.
