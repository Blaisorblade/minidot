(** Prove STLC normalization: all well-typed terms evaluate to a value. *)
Require Import stlc.
Require Import Equations.Equations.

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

Lemma fund_t_var: forall G x T, indexr x G = Some T -> sem_type G T (tvar x).
Proof.
  unfold sem_type, etp, expr_sem; intros;
    pose proof (teval_var env x); ev; subst.
  edestruct R_env_to_indexr_success as [? Hrew]; try rewrite Hrew in *; eauto.
Qed.

Lemma fund_t_nat: forall G n,
    sem_type G TNat (tnat n).
Proof.
  unfold sem_type; intros; eapply vtp_etp with (nm := 0).
  - unfoldTeval; intros; step_eval; trivial.
  - unfold etp in *; simp vtp; eauto.
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

Lemma fund_t_let: forall G T1 T2 t1 t2, sem_type G T1 t1 -> sem_type (T1 :: G) T2 t2 -> sem_type G T2 (tlet t1 t2).
Proof.
  unfold sem_type, etp, expr_sem; unfoldTeval.
  intros * Hvtp10 Hvtp20 * Henv.
  lets (v1 & j1 & (nm1 & Hev1) & Hvtp1): Hvtp10 __; eauto.
  lets (v2 & j2 & (nm2 & Hev2) & Hvtp2): Hvtp20 __; eauto.
  remember (max nm1 nm2) as nm.
  assert (nm >= nm1 /\ nm >= nm2) as (? & ?) by (subst; eauto using max_bigger_both).

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
Theorem fundamental: forall G t T, has_type false G t T -> sem_type G T t.
Proof. intros * Htp; dependent induction Htp; eauto using fund_t_var, fund_t_nat, fund_t_abs, fund_t_app, fund_t_let. Qed.

(** Strong normalization: evaluation of a well-typed program terminates with a
    result of the right type. Proved as a corollary of the [fundamental] property.
  *)
Theorem normalize: forall G t T env, has_type false G t T ->
    R_env env G ->
    exists v j,
      tevalSn env t v j /\ vtp T v.
Proof. intros; edestruct fundamental; ev; eauto. Qed.

(** Type soundness: If evaluation of a well-typed program terminates, the result
    is not a runtime error. Proved as a corollary of [normalize]. *)
Theorem sound: forall G t T env optV j, has_type false G t T ->
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
