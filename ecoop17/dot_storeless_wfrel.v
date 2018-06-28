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
  exists T', subst_all (map VObj env) T = Some T' /\
        vtp T' k v.

Definition vtpEnvSome T k v env :=
  tm_closed 0 0 v /\ wf env T /\ vtpEnvSomeCore T k v env.

Lemma vtpEnvSome_closed:
  forall T k v env, vtpEnvSome T k v env -> wf env T.
Proof. unfold vtpEnvSome, wf, closed_ty; program_simpl. Qed.
Hint Resolve vtpEnvSome_closed.

Definition etpEnvSomeCore T k e env : Prop :=
  forall v j,
    evalToSome env e v k j ->
    vtpEnvSomeCore T (k - j) v env.

Definition etpEnvSome T k e env :=
  tm_closed 0 (length env) e /\ wf env T /\ etpEnvSomeCore T k e env.

Lemma etpEnvSome_closed: forall T k v env,
    etpEnvSome T k v env -> wf env T.
Proof. unfold etpEnvSome; program_simpl. Qed.
Hint Resolve etpEnvSome_closed.

Definition sem_type_some (G : tenv) (T : ty) (e: tm) :=
  wf G T /\ tm_closed 0 (length G) e /\
      forall k env (Henv: R_env k env G), etpEnvSomeCore T k e env.

Lemma sem_type_some_closed : forall G T e,
    sem_type_some G T e -> wf G T.
Proof. unfold sem_type_some; program_simpl. Qed.

Definition sem_subtype_some (G : tenv) (T1 T2: ty) :=
  wf G T1 /\ wf G T2 /\
      forall e (HwfE : tm_closed 0 (length G) e),
      forall k env (Henv : R_env k env G),
        etpEnvSomeCore T1 k e env -> etpEnvSomeCore T2 k e env.

Definition sem_vl_subtype_some (G : tenv) (T1 T2: ty) :=
  wf G T1 /\ wf G T2 /\
      forall e (HwfE : tm_closed 0 (length G) e),
      forall k env (Henv : R_env k env G),
        vtpEnvSomeCore T1 k e env -> vtpEnvSomeCore T2 k e env.

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

Lemma env_dms_closed: forall k env G l, R_env k env G -> length env = l -> Forall (dms_closed 0 (S l)) env.
Proof.
  induction env; intros * Henv Hl; subst; inverts Henv; constructor; simpl; eauto using Forall_impl.
  assert (tm_closed 0 0 (tvar (VObj a))) by (eauto using vtp_v_closed); repeat inverts_closed; eauto.
Qed.
Hint Resolve env_dms_closed.

Lemma vl_subtype_some_to_subtype_some : forall G T1 T2
    (Hsub: sem_vl_subtype_some G T1 T2), sem_subtype_some G T1 T2.
Proof.
  unfold sem_subtype_some, sem_vl_subtype_some, etpEnvSomeCore;
    intuition eauto 8.
Qed.
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

Lemma tm_closed_upgrade: forall i k k1 v,
  tm_closed i k v -> k <= k1 -> tm_closed i k1 v.
Proof. unmut_lemma closed_upgrade_rec. Qed.
Hint Resolve tm_closed_upgrade.

Opaque max.

Lemma subst_all_nonTot_res_closed_rec2:
  (forall v, forall i j env, Forall (vr_closed i j) env -> forall (Hcl: vr_closed i (length env) v),
          forall j', j' = max (S (length env)) j ->
          exists v', vr_subst_all env v = Some v' /\
                vr_closed i j' v') /\
  (forall T, forall i j env, Forall (vr_closed i j) env -> forall (Hcl: closed i (length env) T),
          forall j', j' = max (S (length env)) j ->
          exists T', subst_all env T = Some T' /\
                closed i j' T') /\
  (forall t, forall i j env, Forall (vr_closed i j) env -> forall (Hcl: tm_closed i (length env) t),
          forall j', j' = max (S (length env)) j ->
          exists t', tm_subst_all env t = Some t' /\
                tm_closed i j' t') /\
  (forall d, forall i j env, Forall (vr_closed i j) env -> forall (Hcl: dm_closed i (length env) d),
          forall j', j' = max (S (length env)) j ->
          exists d', dm_subst_all env d = Some d' /\
                dm_closed i j' d') /\
  (forall d, forall i j env, Forall (vr_closed i j) env -> forall (Hcl: dms_closed i (length env) d),
          forall j', j' = max (S (length env)) j ->
          exists d', dms_subst_all env d = Some d' /\
                dms_closed i j' d').
Proof.
  Ltac smartInd :=
    match goal with
    | Hind : context [ ?f _ ?s ] |- context [ match ?f ?env ?s with _ => _ end ] =>
      lets (? & -> & ?): Hind env ___; simpl; eauto
    end.
  apply syntax_mutind; simpl; intros;
      inverts_closed;
      assert (S (length env) <= j') by (subst; eauto);
      subst;
      repeat smartInd; eauto 8 using index_Forall, some_max_lemma.
Qed.

Lemma etp_vtp_j: forall e v k j T env,
    evalToSome env e v k j -> etpEnvSome T k e env -> j <= k -> vtpEnvSome T (k - j) v env.
Proof.
  intros.
  assert (exists v0, Some v = Some v0 /\ vtpEnvSome T (k - j) v0 env). {
    
    unfold etpEnvSome, etpEnvSomeCore, vtpEnvSome, vtpEnvSomeCore in *.
    exists v. intuition eauto.
Abort.
(*     eapply tm_subst_all_nonTot_res_closed. *)
(*     eapply evalToSomeRes_closed. eauto. *)
(*     unfold evalToSome in *. *)
(*     ev. *)
(*     eapply steps_closed. eauto. *)
(*     eapply tm_subst_all_nonTot_res_closed. *)
(*     eauto using steps_closed. *)
(*   } *)
(*   ev; injectHyps; eauto. *)
(* Qed. *)
(* Hint Resolve etp_vtp_j. *)

(* Lemma subtype_to_vl_subtype : forall G T1 T2, *)
(*     sem_subtype_some G T1 T2 -> sem_vl_subtype_some G T1 T2. *)
(* Proof. *)
(*   (* unfold sem_subtype, sem_vl_subtype; intros; intuition eauto; *) *)
(*   (*   destruct (vl_to_tm v) as [e Heval]; firstorder eauto. *) *)
(*   unfold sem_subtype_some, sem_vl_subtype_some; intros * (? & ? & Hsub). *)
(*     split_conj; eauto; *)
(*       intros * Hcl * Henv * HvT1. *)
(*     unfold etpEnvSomeCore in *. *)
(*       firstorder eauto. *)
(*   (* specialize (Hsub k env Henv e); *) *)
(*   (*   specialize (Heval env). *) *)
(*   (*   (* assert (wf G T1) by eauto. *) *) *)
(*   (* assert (etp T2 k e env) as [? HeT2]. { *) *)
(*   (*   unfold etp, expr_sem in *; apply Hsub; intuition eauto. *) *)
(*   (*   exists v; unfold tevalSnOpt in *; ev; eval_det; eauto. *) *)
(*   (* } *) *)
(*   (* (* eauto. *) *) *)
(*   (* (* (* unfold etp, expr_sem, tevalSnOpt, tevalSnOpt, tevalSnmOpt in HeT2. *) *) *) *)
(*   (* (* (* eauto. *) *) *) *)
(*   (* (* (* destruct (HeT2 (Some v) 0) as (? & ? & ?); replace (k - 0) with k in * by omega; simpl. eauto. *) *) *) *)
(* Qed. *)

Require Import dot_monads.

Fixpoint vr_subst_all_k k (env: list vr) (v: vr) { struct v }: option vr :=
  match v with
    | VarF x => ret (VarF x)
    | VarB x => index x env
    | VObj dms =>
      dms' <- dms_subst_all_k (S k) (VarB k :: env) dms;
      ret (VObj dms')
  end
with subst_all_k k (env: list vr) (T: ty) { struct T }: option ty :=
  match T with
    | TTop        => ret TTop
    | TBot        => ret TBot
    | TSel v1 l     =>
      v1' <- vr_subst_all_k k env v1;
      ret (TSel v1' l)
    | TFun l T1 T2  =>
      T1' <- subst_all_k k env T1;
      T2' <- subst_all_k (S k) (VarB k :: env) T2;
      ret (TFun l T1' T2')
    | TMem l T1 T2  =>
      T1' <- subst_all_k k env T1;
      T2' <- subst_all_k k env T2;
      ret (TMem l T1' T2')
    | TBind T1    =>
      T1' <- subst_all_k (S k) (VarB k :: env) T1;
      ret (TBind T1')
    | TAnd T1 T2  =>
      T1' <- subst_all_k k env T1;
      T2' <- subst_all_k k env T2;
      ret (TAnd T1' T2')
    | TOr T1 T2   =>
      T1' <- subst_all_k k env T1;
      T2' <- subst_all_k k env T2;
      ret (TOr T1' T2')
  end
with tm_subst_all_k k (env: list vr) (t: tm) { struct t }: option tm :=
   match t with
     | tvar v => v' <- vr_subst_all_k k env v; ret (tvar v')
     | tapp t1 l t2 =>
       t1' <- tm_subst_all_k k env t1;
       t2' <- tm_subst_all_k k env t2;
       ret (tapp t1' l t2')
   end
with dm_subst_all_k k (env: list vr) (d: dm) { struct d }: option dm :=
   match d with
     | dfun T1 T2 t2 =>
       T1' <- subst_all_k k env T1;
       T2' <- subst_all_k (S k) (VarB k :: env) T2;
       t2' <- tm_subst_all_k (S k) (VarB k :: env) t2;
       ret (dfun T1' T2' t2')
     | dty T1 =>
       T1' <- subst_all_k k env T1;
       ret (dty T1')
   end
with dms_subst_all_k k (env: list vr) (ds: dms) { struct ds }: option dms :=
   match ds with
     | dnil => ret dnil
     | dcons d ds =>
       d'  <- dm_subst_all_k k env d;
       ds' <- dms_subst_all_k k env ds;
       ret (dcons d' ds')
   end.

Lemma subst_all_nonTot_res_closed_rec3:
  (forall v, forall i k env, Forall (vr_closed i k) env -> forall (Hcl: vr_closed i (length env) v),
          exists v', vr_subst_all_k k env v = Some v' /\
                vr_closed i k v') /\
  (forall T, forall i k env, Forall (vr_closed i k) env -> forall (Hcl: closed i (length env) T),
          exists T', subst_all_k k env T = Some T' /\
                closed i k T') /\
  (forall t, forall i k env, Forall (vr_closed i k) env -> forall (Hcl: tm_closed i (length env) t),
          exists t', tm_subst_all_k k env t = Some t' /\
                tm_closed i k t') /\
  (forall d, forall i k env, Forall (vr_closed i k) env -> forall (Hcl: dm_closed i (length env) d),
          exists d', dm_subst_all_k k env d = Some d' /\
                dm_closed i k d') /\
  (forall d, forall i k env, Forall (vr_closed i k) env -> forall (Hcl: dms_closed i (length env) d),
          exists d', dms_subst_all_k k env d = Some d' /\
                dms_closed i k d').
Proof.
  apply syntax_mutind; simpl; intros; inverts_closed;
    repeat
      match goal with
      | Hind : context [ ?f _ _ ?s ] |- context [ match ?f ?k ?env ?s with _ => _ end ] =>
        lets (? & -> & ?): Hind i k env ___
      end;
    eauto using index_Forall.
Qed.

Lemma subst_closed_id_rec3:
  (forall v i env, vr_env_id env -> forall (Hcl: vr_closed i (length env) v),
          vr_subst_all_k (length env) env v = Some v) /\
  (forall T i env, vr_env_id env -> forall (Hcl: closed i (length env) T),
          subst_all_k (length env) env T = Some T) /\
  (forall t i env, vr_env_id env -> forall (Hcl: tm_closed i (length env) t),
          tm_subst_all_k (length env) env t = Some t) /\
  (forall d i env, vr_env_id env -> forall (Hcl: dm_closed i (length env) d),
          dm_subst_all_k (length env) env d = Some d) /\
  (forall d i env, vr_env_id env -> forall (Hcl: dms_closed i (length env) d),
          dms_subst_all_k (length env) env d = Some d).
Proof.
  apply syntax_mutind; simpl; intros; inverts_closed;
    repeat
      match goal with
      | Hind : context [ ?f _ _ ?s ] |- context [ match ?f ?k ?env ?s with _ => _ end ] =>
        lets ->: Hind i env ___
      end;
    eauto.
Qed.
