Require Import Omega.
Require Import Equations.Equations.
Require Import tactics.

Require Import dot_storeless_tidy.
Require Import dot_storeless_subst_aux.
Require Import dot_storeless_wfrel_aux.
Require Import tactics.

Require Import dot_storeless_wfrel.

(* Anomaly! *)
(* Program Lemma index_sigT : forall {X} vs (n : id), n < length vs -> *)
(*                        {T:X & index (proj1_sig n) vs = Some T}. *)

Program Lemma index_sigT : forall {X} vs (n : id), n < length vs ->
                       {T:X & index n vs = Some T}.
Proof.
  intros; induction vs; simpl in *.
  - omega.
  - case_match; beq_nat; subst; eauto.
Defined.

Definition indexTot {X} (xs : list X) (n : id) (H : n < length xs): X :=
  projT1 (index_sigT xs n H).

Program Fixpoint vr_subst_all_tot i (env: list vr) (v: vr) (_ : vr_closed i (length env) v) { struct v }: vr :=
  match v with
    | VarF x => VarF x
    | VarB x => indexTot env x _
    | VObj dms =>
      let dms' := dms_subst_all_tot i (VarB 0 :: env) dms _ in
      VObj dms'
  end
with subst_all_tot i (env: list vr) (T: ty) (_ : closed i (length env) T){ struct T }: ty :=
  match T with
    | TTop        => TTop
    | TBot        => TBot
    | TSel v1 l     =>
      let v1' := vr_subst_all_tot i env v1 _ in
      TSel v1' l
    | TFun l T1 T2  =>
      let T1' := subst_all_tot i env T1 _ in
      let T2' := subst_all_tot i (VarB 0 :: env) T2 _ in
      TFun l T1' T2'
    | TMem l T1 T2  =>
      let T1' := subst_all_tot i env T1 _ in
      let T2' := subst_all_tot i env T2 _ in
      TMem l T1' T2'
    | TBind T1    =>
      let T1' := subst_all_tot i (VarB 0 :: env) T1 _ in
      TBind T1'
    | TAnd T1 T2  =>
      let T1' := subst_all_tot i env T1 _ in
      let T2' := subst_all_tot i env T2 _ in
      TAnd T1' T2'
    | TOr T1 T2   =>
      let T1' := subst_all_tot i env T1 _ in
      let T2' := subst_all_tot i env T2 _ in
      TOr T1' T2'
  end
with tm_subst_all_tot i (env: list vr) (t: tm) (_ : tm_closed i (length env) t) { struct t }: tm :=
   match t with
     | tvar v => let v' := vr_subst_all_tot i env v _ in tvar v'
     | tapp t1 l t2 =>
       let t1' := tm_subst_all_tot i env t1 _ in
       let t2' := tm_subst_all_tot i env t2 _ in
       tapp t1' l t2'
   end
with dm_subst_all_tot i (env: list vr) (d: dm) (_ : dm_closed i (length env) d) { struct d }: dm :=
   match d with
     | dfun T1 T2 t2 =>
       let T1' := subst_all_tot i env T1 _ in
       let T2' := subst_all_tot i (VarB 0 :: env) T2 _ in
       let t2' := tm_subst_all_tot i (VarB 0 :: env) t2 _ in
       dfun T1' T2' t2'
     | dty T1 =>
       let T1' := subst_all_tot i env T1 _ in
       dty T1'
   end
with dms_subst_all_tot i (env: list vr) (ds: dms) (_ : dms_closed i (length env) ds) { struct ds }: dms :=
   match ds with
     | dnil => dnil
     | dcons d ds =>
       let d'  := dm_subst_all_tot i env d _ in
       let ds' := dms_subst_all_tot i env ds _ in
       dcons d' ds'
   end.
Solve All Obligations with program_simpl; abstract (inverts H; auto).

Ltac reduce_indexTot :=
  try match goal with
  | H : context [ indexTot ?env ?i _] |- _ => unfold indexTot in *; destruct (index_sigT env i)
  | |- context [ indexTot ?env ?i _] => unfold indexTot in *; destruct (index_sigT env i)
  end.

Program Definition ex_type := forall i l v, subst_all_tot i [v] (TSel (VarB 0) l) _ = TSel v l.
Program Lemma ex: ex_type.
Proof. red; intros; simpl; reduce_indexTot; simpl in *; congruence. Qed.
Program Definition ex2_type:= forall i l v0 v1, subst_all_tot i [v1, v0] (TSel (VarB 1) l) _ = TSel v1 l.
Program Lemma ex2: ex2_type.
Proof. red; intros; intros; simpl; reduce_indexTot; simpl in *; congruence. Qed.

Lemma indexTot_Forall: forall {X} (env: list X) i (P: X -> Prop) (Henv: Forall P env) (Hlen: i < length env),
    P (indexTot env i Hlen).
Proof.
  unfold indexTot; intros; destruct (index_sigT env i);
    (* A special case of apply_Forall below *)
    lets ?: @index_Forall' ___ Henv; eauto.
Qed.

(* Use "solve" because in subst_all_res_closed_rec this tactic leads the proof
   search down the wrong path whenever it doesn't solve the goal immediately;
   using "solve" is sort of what eauto's proof search and backtracking would do
   anyway: if applying this lemma and searching further doesn't help, backtrack. *)
Ltac apply_Forall :=
  match goal with
  | H: Forall ?P ?env |- ?P (indexTot ?env _ _) => try solve [eapply indexTot_Forall; eauto]
  end.
(* Seems to actually work fine, but this is needed too seldom for now, and can be expensive. *)
(* Hint Extern 5 => apply_Forall. *)

Lemma subst_all_res_closed_rec:
  (forall v, forall i k env, Forall (vr_closed i k) env -> forall (Hcl: vr_closed i (length env) v), vr_closed i k (vr_subst_all_tot i env v Hcl)) /\
  (forall T, forall i k env, Forall (vr_closed i k) env -> forall (Hcl: closed i (length env) T), closed i k (subst_all_tot i env T Hcl)) /\
  (forall t, forall i k env, Forall (vr_closed i k) env -> forall (Hcl: tm_closed i (length env) t), tm_closed i k (tm_subst_all_tot i env t Hcl)) /\
  (forall dm, forall i k env, Forall (vr_closed i k) env -> forall (Hcl: dm_closed i (length env) dm), dm_closed i k (dm_subst_all_tot i env dm Hcl)) /\
  (forall dms, forall i k env, Forall (vr_closed i k) env -> forall (Hcl: dms_closed i (length env) dms), dms_closed i k (dms_subst_all_tot i env dms Hcl)).
Proof.
  apply syntax_mutind; intros; simpl in *; inverts_closed; solve [apply_Forall | eauto 11].
Qed.

Lemma closed_irrelevance_rec:
  (forall i k x (H1 H2: vr_closed i k x), H1 = H2) /\
  (forall i k T (H1 H2: closed i k T), H1 = H2) /\
  (forall i k t (H1 H2: tm_closed i k t), H1 = H2) /\
  (forall i k dm (H1 H2: dm_closed i k dm), H1 = H2) /\
  (forall i k dms (H1 H2: dms_closed i k dms), H1 = H2).
Proof.
  apply closed_mutind; intros; depelim H2; fequal; eauto using le_unique.
Qed.

Lemma closed_irrelevance: forall T i k (H1 H2: closed i k T), H1 = H2.
Proof. destruct closed_irrelevance_rec; ev; eauto. Qed.
Lemma tm_closed_irrelevance: forall i k t (H1 H2: tm_closed i k t), H1 = H2.
Proof. destruct closed_irrelevance_rec; ev; eauto. Qed.
Lemma vr_closed_irrelevance: forall i k x (H1 H2: vr_closed i k x), H1 = H2.
Proof. destruct closed_irrelevance_rec; ev; eauto. Qed.
Lemma dm_closed_irrelevance: forall i k d (H1 H2: dm_closed i k d), H1 = H2.
Proof. destruct closed_irrelevance_rec; ev; eauto. Qed.
Lemma dms_closed_irrelevance: forall i k d (H1 H2: dms_closed i k d), H1 = H2.
Proof. destruct closed_irrelevance_rec; ev; eauto. Qed.

(* Evaluation *)
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
