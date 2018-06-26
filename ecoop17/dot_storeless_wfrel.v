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
  (* (env: venv) (G: tenv) : Set := *)
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
Proof.
  intros * Henv; induction Henv; eauto.
Qed.
Hint Resolve R_env_mon.

Lemma wf_length : forall k vs ts,
                    R_env k vs ts ->
                    (length vs = length ts).
Proof.
  intros * H; induction H; simpl; congruence.
Qed.

Hint Constructors Forall.

Program Definition etp T k e :=
  expr_sem k T (fun k _ => vtp T k) k _ e.

Lemma etp_closed: forall T k v,
    etp T k v -> @wf ty [] T.
Proof.
  unfold etp; intros; simp expr_sem in *; tauto.
Qed.
Hint Resolve etp_closed.
(* Scheme vr_mut_type := Induction for vr Sort Set *)
(* with   ty_mut_type := Induction for ty Sort Set *)
(* with   tm_mut_type := Induction for tm Sort Set *)
(* with   dm_mut_type := Induction for dm Sort Set *)
(* with   dms_mut_type := Induction for dms Sort Set. *)
(* Combined Scheme syntax_mut_typeind from vr_mut_type, ty_mut_type, tm_mut_type, dm_mut_type, dms_mut_type. *)

(* Lemma subst_all_success_rec_sig: *)
(*   (forall v, forall i env, forall j, vr_closed i j v -> length env = j -> { v' | vr_subst_all env v = Some v'}) * *)
(*   (forall T, forall i env, forall j, closed i j T -> length env = j -> { T' | subst_all env T = Some T'}) * *)
(*   (forall t, forall i env, forall j, tm_closed i j t -> length env = j -> { t' | tm_subst_all env t = Some t'}) * *)
(*   (forall dm, forall i env, forall j, dm_closed i j dm -> length env = j -> { dm' | dm_subst_all env dm = Some dm'}) * *)
(*   (forall T, forall i env, forall j, dms_closed i j T -> length env = j -> { dms' | dms_subst_all env T = Some dms'}). *)
(* Proof. *)
(*   apply syntax_mutind. *)
(*   Abort. *)

(* Program Definition subst_all_tot (env: venv) T (HclT: closed 0 (length env) T) := *)
(*   let '(ex_intro _ A B) := (subst_all_success T 0 (map VObj env) (length env) HclT eq_refl) *)
(*   in A. *)
(* Check subst_all_tot. *)

Hint Rewrite map_length.

(* Equations evalTo2 (env : list dms) (t : tm) (v : tm): nat -> nat -> tm_closed 0 (length env) t -> Prop := *)
(*   evalTo2 env t v := *)
(*     fun k j HwfV => *)
(*     let venv := map VObj env in *)
(*     steps (tm_subst_all_tot 0 venv t _) v j /\ irred v /\ j <= k. *)
(* Solve Obligations with program_simpl; rewrite map_length; auto. *)

Program Definition evalTo env e v k j (HwfE : tm_closed 0 (length env) e) :=
  steps (tm_subst_all_tot 0 (map VObj env) e _) v j /\ irred v /\ j <= k.
Solve Obligations with program_simpl; rewrite map_length; auto.

Program Definition vtpEnvCore T k v env (HwfT : wf env T) :=
  vtp (subst_all_tot 0 (map VObj env) T _) k v.
Solve Obligations with program_simpl; rewrite map_length; auto.

Program Definition vtpEnv T k v env :=
  tm_closed 0 0 v /\
  { HwfT : wf env T | vtpEnvCore T k v env _ }.

Lemma vtpEnv_closed:
  forall T k v env, vtpEnv T k v env -> wf env T.
Proof. unfold vtpEnv; program_simpl. Qed.
Hint Resolve vtpEnv_closed.

(* Program Definition vtpEnvCore2 T k v env (HwfT : wf env T) (HwfV : tm_closed 0 (length env) v) := *)
(*   let venv := map VObj env in *)
(*   vtp (subst_all_tot 0 venv T _) k (tm_subst_all_tot 0 venv v _). *)
(* Solve Obligations with program_simpl; rewrite map_length; auto. *)

Program Definition etpEnvCore T k e env
        (HwfE : tm_closed 0 (length env) e)
        (HwfT : wf env T): Prop :=
  forall v j,
    evalTo env e v k j _ ->
    vtpEnvCore T (k - j) v env _.
Hint Transparent wf.

Program Definition etpEnv T k e env :=
  { HwfT : wf env T |
    { HwfE : tm_closed 0 (length env) e | etpEnvCore T k e env _ _ }}.
Hint Unfold etpEnv.
Hint Transparent etpEnv.
Hint Transparent wf.

Lemma etpEnv_closed: forall T k v env,
    etpEnv T k v env -> wf env T.
Proof. unfold etpEnv; program_simpl. Qed.
Hint Resolve etpEnv_closed.

Definition evalToSome env e v k j :=
  (exists t', tm_subst_all (map VObj env) e = Some t' /\ steps t' v j) /\ irred v /\ j <= k.

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

(* Definition vtpEnv T k v env := *)
(*   let venv := map VObj env in *)
(*   let T' := subst_all venv T in *)
(*   let v' := tm_subst_all venv v in *)
(*   closed_ty 0 (length env) T /\ *)
(*   exists T'' v'', *)
(*     T' = Some T'' /\ *)
(*     v' = Some v'' /\ *)
(*     vtp T'' k v''. *)

(* Set Transparent Obligations. (* XXX only for one unfold later, check if really needed. *) *)

(* Program Definition etpEnvCore T k e env (HwfT : wf env T) (HwfE : tm_closed 0 (length env) e) := *)
(*   let venv := map VObj env in *)
(*   let T' := subst_all_tot 0 venv T _ in *)
(*   expr_sem k T' (fun k _ => vtp T' k) k _ (tm_subst_all_tot 0 venv e _). *)

(* Solve Obligations with program_simpl; rewrite map_length; auto. *)

(* Semantic typing *)
Program Definition sem_type (G : tenv) (T : ty) (e: tm) :=
  { HwfT : wf G T | { HwfE : tm_closed 0 (length G) e |
      forall k env (Henv: R_env k env G), etpEnvCore T k e env _ _ }}.
Solve Obligations with program_simpl; unfold wf in *; erewrite wf_length in *; eauto.

Program Definition sem_subtype (G : tenv) (T1 T2: ty) :=
  { HwfT1 : wf G T1 |
    { HwfT2 : wf G T2 |
      forall e (HwfE : tm_closed 0 (length G) e),
      forall k env (Henv : R_env k env G),
        etpEnvCore T1 k e env _ _ -> etpEnvCore T2 k e env _ _ }}.
Solve Obligations with program_simpl; unfold wf in *; erewrite wf_length in *; eauto.

Program Definition sem_vl_subtype (G : tenv) (T1 T2: ty) :=
  { HwfT1 : wf G T1 |
    { HwfT2 : wf G T2 |
      forall e (HwfE : tm_closed 0 (length G) e),
      forall k env (Henv : R_env k env G),
        vtpEnvCore T1 k e env _ -> vtpEnvCore T2 k e env _ }}.
Solve Obligations with program_simpl; unfold wf in *; erewrite wf_length in *; eauto.

Lemma sem_type_closed : forall G T e,
    sem_type G T e -> wf G T.
Proof. unfold sem_type; program_simpl. Qed.

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
Hint Resolve wf_length.

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

(* Lemma closed_subst_success: forall T env, *)
(*     (closed_ty 0 (length env) T) -> *)
(*     exists T1, subst_all env T = Some T1. *)
(* Admitted. *)

(* Deal with irrelevance of local closure proofs.
Credits to @Cypi on IRC, see gen_safe_proof and unify_lt_proofs
https://github.com/cmangin/template-coq/blob/8b3e6ecec085bab8ebe087af07c3db8e56e8aac2/template-coq/theories/Rtree.v#L108-L118
https://github.com/cmangin/template-coq/blob/8b3e6ecec085bab8ebe087af07c3db8e56e8aac2/template-coq/theories/Rtree.v#L161-L167
 *)

Ltac aux_gen_irr_proof P :=
  tryif is_var P then fail else
    let HPs := fresh "Hs" in
    generalize P as HPs; intro.
Ltac aux_rem_irr_proof H P :=
  tryif is_var P then fail else
    let HPs := fresh "HPs" in
    let Heqs := fresh "Heqs" in
    remember P as HPs eqn:Heqs; clear Heqs.
Ltac prove_closed_irrelevance := eauto using closed_irrelevance, tm_closed_irrelevance, vr_closed_irrelevance, dm_closed_irrelevance, dms_closed_irrelevance.
Ltac prove_tm_closed_irrelevance := apply tm_closed_irrelevance.
Ltac unify_tm_closed_proofs :=
  repeat match goal with
         | H1 : tm_closed ?i ?k ?T, H2 : tm_closed ?i ?k ?T |- _ =>
           assert (H1 = H2) as -> by prove_tm_closed_irrelevance
         end.
Ltac unify_closed_proofs :=
  repeat match goal with
         | H1 : closed ?i ?k ?T, H2 : closed ?i ?k ?T |- _ =>
           assert (H1 = H2) as -> by prove_closed_irrelevance
         end.

Ltac gen_irr_proofs :=
  repeat (reduce_indexTot; match goal with
         | |- context [ vtpEnvCore _ _ _ _ ?H] => aux_gen_irr_proof H; unfold wf in *
         | H : context [ vtpEnvCore _ _ _ _ ?P ] |- _ => aux_rem_irr_proof H P; unfold wf in *
         | H : context [ evalTo _ _ _ _ _ ?P ] |- _ => aux_rem_irr_proof H P
         end).

Ltac lenG_to_lenEnv :=
  try match goal with
  | H: R_env _ ?env ?G |- _ =>
    replace (length G) with (length env) in * by (eauto using wf_length)
  end.

Ltac remove_irrelevant_localClosure_mismatches :=
  gen_irr_proofs; lenG_to_lenEnv; unify_tm_closed_proofs; unify_closed_proofs.

Ltac evp := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: {_ : _ | _} |- _ =>
                      let x := fresh "x" in
                      let H' := fresh "H" in
                      destruct H as [x H']
                    | H: {_ : _ & _} |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
                   end.

Lemma evalToRes_closed: forall env e v n k j H,
    evalTo env e v n j H ->
    Forall (dms_closed 0 (S k)) env ->
    tm_closed 0 k v.
Proof.
  intros; destruct subst_all_res_closed_rec; ev.
  unfold evalTo in *; ev.
  repeat (match goal with
         | H : context [ tm_subst_all_tot _ _ _ ?P ] |- _ => aux_rem_irr_proof H P; unfold wf in *
         end).
  eauto using steps_closed, dms_to_env_closed.
Qed.
Hint Resolve evalToRes_closed.

Lemma env_dms_closed: forall k env G, R_env k env G -> Forall (dms_closed 0 (S (length env))) env.
Proof.
  induction env; intros * Henv; inverts Henv; constructor; simpl; eauto using Forall_impl.

  assert (tm_closed 0 0 (tvar (VObj a))) by eauto using vtp_v_closed; repeat inverts_closed; eauto.
Qed.
Hint Resolve env_dms_closed.

Lemma evalToSomeRes_closed: forall env e v n k j,
    evalToSome env e v n j ->
    tm_closed 0 (length env) e ->
    Forall (dms_closed 0 (S k)) env ->
    tm_closed 0 k v.
Proof.
  unfold evalToSome; intros * ((t0 & ?) & ?); intros; ev;
    assert (exists t', tm_subst_all (map VObj env) e = Some t' /\ tm_closed 0 k t') as (t1 & ? & ?)
      by (eapply tm_subst_all_nonTot_res_closed; try rewrite map_length; eauto);
    assert (t0 = t1) as -> by congruence;
    eauto using steps_closed.
Qed.
Hint Resolve evalToSomeRes_closed.

(* Write lemmas to get rid of all the extra side conditions and get to the meat. *)
Program Lemma vl_subtype_to_subtype : forall G T1 T2,
    sem_vl_subtype G T1 T2 -> sem_subtype G T1 T2.
Proof.
  unfold sem_subtype, sem_vl_subtype, wf.
  (* intros; evp. *)
  intros * (? & ? & Hvl).
  repeat match goal with
         | H: ?P |- { H : ?P | ?Q } => exists H
         end.
  intros * HeVtpT1; unfold etpEnvCore in *.
  ev; split_conj; intros.

  assert (Forall (dms_closed 0 (S (length env))) env) by eauto using env_dms_closed.
  assert (HwfV: tm_closed 0 (length env) v) by eauto.
  assert (HwfV2: tm_closed 0 (length G) v) by (erewrite <- wf_length; eauto).
  assert (Henvkj: R_env (k - j) env G) by eauto.
  specialize (Hvl _ HwfV2 (k - j) env Henvkj).
  specialize (HeVtpT1 v j).
  remove_irrelevant_localClosure_mismatches; eauto.
Qed.
Hint Resolve vl_subtype_to_subtype.

Lemma vl_subtype_some_to_subtype_some : forall G T1 T2,
    sem_vl_subtype_some G T1 T2 -> sem_subtype_some G T1 T2.
Proof.
  unfold sem_subtype_some, sem_vl_subtype_some, etpEnvSomeCore;
    intuition idtac; lenG_to_lenEnv; eauto 6.
Qed.
Hint Resolve vl_subtype_some_to_subtype_some.

Lemma and_stp1 : forall T1 T2 n v, vtp (TAnd T1 T2) n v -> vtp T1 n v.
Proof. unfold vtp; intros; simp val_type in *; tauto. Qed.

Hint Unfold wf sem_type_some sem_subtype_some sem_vl_subtype_some.

Ltac to_vl_stp L :=
  unfold sem_vl_subtype_some, vtpEnvSomeCore;
    intuition eauto; ev;
      simpl in *; repeat better_case_match; try congruence; injections_some;
        eauto using L.

Lemma sem_vl_and_stp1 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_vl_subtype_some G (TAnd T1 T2) T1.
Proof. to_vl_stp and_stp1. Qed.

Lemma sem_and_stp1 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_subtype_some G (TAnd T1 T2) T1.
Proof. eauto using vl_subtype_some_to_subtype_some, sem_vl_and_stp1. Qed.

Lemma and_stp2 : forall T1 T2 n v, vtp (TAnd T1 T2) n v -> vtp T2 n v.
Proof. unfold vtp; intros; simp val_type in *; tauto. Qed.

Lemma sem_vl_and_stp2 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_vl_subtype_some G (TAnd T1 T2) T2.
Proof. to_vl_stp and_stp2. Qed.

Lemma sem_and_stp2 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_subtype_some G (TAnd T1 T2) T2.
Proof. eauto using vl_subtype_some_to_subtype_some, sem_vl_and_stp2. Qed.

Lemma stp_and' : forall T1 T2 n v, vtp T1 n v -> vtp T2 n v -> vtp (TAnd T1 T2) n v.
Proof. unfold vtp; intros; simp val_type in *; tauto. Qed.

Lemma stp_and : forall S T1 T2 n v,
    (vtp S n v -> vtp T1 n v) ->
    (vtp S n v -> vtp T2 n v) ->
    vtp S n v -> vtp (TAnd T1 T2) n v.
Proof. unfold vtp; intros; simp val_type in *; tauto. Qed.

(* Lemma tm_closed_irrelevance1: forall i1 i2 k1 k2 t *)
(*                                (H1 : tm_closed i1 k1 t) (H2 : tm_closed i2 k2 t) *)
(*                                (Hi : i1 ~= i2) (Hk: k1 ~= k2), H1 ~= H2. *)
(* Proof. intros. *)
(*        dependent rewrite Hi. Hk. *)
(*   eauto using proof_irrelevance. Qed. *)
(*   dependent rewrite Hlen in HPs2. *)

(*   - admit. *)
(*   - *)
(*     unfold vtpEnvCore in *. *)
(*     (* unfold etpEnvCore_obligation_1 in *. *) *)
(*     intuition eauto. *)
(*     (* XXX Reprove subst_all_closed_upgrade_rec for subst_all_tot. Then, modify *)
(*     vtp to ensure it only holds for closed terms, prove it, lift that proof to *)
(*     R_env, then try again (or maybe rather move the hard work in vtp_etp and etp_vtp lemmas). *) *)

(* (*   - intros. *) *)
(* (*   vtp, etpEnvCore, vtpEnvCore; simp val_type. *) *)
(* (*   unfold etpEnv in *. *) *)
(* (*   Transparent expr_sem. *) *)
(* (*   unfold expr_sem. *) *)
(* (*   Opaque expr_sem. *) *)
(* (*   intros * (? & ? & Himpl); split_conj; eauto. intros * Henv * (? & ?). *) *)

(* (*   ev; split_conj; *) *)
(* (*     replace (length G) with (length env) in * by eauto; *) *)
(* (*     eauto. *) *)
(* (*   lets (? & ?): closed_subst_success T2 (map VObj env) ___; *) *)
(* (*   try rewrite map_length; eauto. *) *)
(* (*   do 2 eexists; split_conj; eauto. *) *)
(* (*   admit. *) *)
(* (*   eauto. *) *)
(* (*   (* info_eauto. *) *) *)
(* (*   (* info_eauto. *) *) *)
(* (*   (* info_eauto. *) *) *)

(* (*   (* intuition info_eauto. *) *) *)
(* (*   (* - admit. *) *) *)
(* (*   (* - lets (? & ?) : H5 v j ___; eauto. eapply H9. *) *) *)
(* (*   (*   eauto. *) *) *)

(* (*   (* simp expr_sem in *; ev. *) *) *)
(* (*   (* lets ? : Himpl Henv e ___; intuition eauto; repeat eexists. *) *) *)
(* (*   (* eauto. *) *) *)
(* (*   (* eauto. *) *) *)
