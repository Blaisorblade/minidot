(** Prove STLC type soundness: no well-typed terms causes a runtime type error. *)
Require Import stlc.
Require Import Equations.Equations.

(* Maybe make both normal definitions, or at least Program Definitions? Let's limit equations weird rules? *)
(* Only expr_sem changes in definitions between here and normalization. *)
Definition expr_sem (A : vl_prop) (t : tm) (env: venv): Prop :=
  forall optV j,
    tevalSnOpt env t optV j -> exists v, optV = Some v /\ A v.

(* Non-step-indexed unary logical relation. *)
Equations vtp (T: ty) (v : vl) : Prop :=
  vtp T t by rec T tsize_rel :=
  vtp TNat (vnat n) := True;
  vtp (TFun T1 T2) (vabs env body) := forall v, vtp T1 v -> expr_sem (fun v => vtp T2 v) body (v :: env);
  vtp (TFun T1 T2) (vrec env body) := forall v, vtp T1 v -> expr_sem (fun v => vtp T2 v) body (v :: vrec env body :: env);
  vtp _ _ := False.
Solve All Obligations with program_simpl.

Example ex0 : vtp (TFun TNat TNat) (vabs [] (tvar 0)).
Proof.
  simp vtp; unfold expr_sem; intros.
  unfoldTeval; n_is_succ_hp; eauto.
Qed.

Include Envs.

Lemma vl_subtype_to_subtype : forall G T1 T2,
    sem_vl_subtype G T1 T2 -> sem_subtype G T1 T2.
Proof.
  unfold sem_subtype, sem_vl_subtype, etp, expr_sem;
    intros; split_conj; eauto.
  intros * ? * HeT1 **; edestruct HeT1; ev; eauto.
Qed.
Hint Resolve vl_subtype_to_subtype.

Require Import PropExtensionality.
Lemma vl_sub_equiv: sem_subtype = sem_vl_subtype.
Proof.
  repeat (apply functional_extensionality; intro); apply propositional_extensionality;
    split; eauto.
Qed.
Hint Rewrite vl_sub_equiv.

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
    pose proof (teval_var env x); eval_det; subst.
  edestruct R_env_to_indexr_success; eauto.
Qed.

Lemma fund_t_nat: forall G n,
    sem_type G TNat (tnat n).
Proof.
  unfold sem_type; intros; eapply vtp_etp with (nm := 0).
  - unfoldTeval; intros; step_eval; trivial.
  - unfold etp in *; simp vtp; eauto.
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
Ltac n_is_succ_hp ::=
  ev; match goal with
  | H : forall n, n > ?nm -> _ |- _ =>
    let H2 := fresh "H" in
    lets ? : H (S nm) __; eauto; clear H;
    cbn [tevalSM] in H2; try unfold logStep in H2
  end.
  n_is_succ_hp. simpl_unfold_monad.
  SearchAbout eq_refl.
  ssimpl_unfold_monad.
Lemma inv_succ_opt_bind: forall {X Y M} (m: option X) (f : X -> option Y)
    bind m f = Some v ->
    (match p with None => None | Some x => f x end = Some r) ->
    exists v1 v2, p = Some (v1, v2) /\ f (v1, v2) = Some r.
Proof. intros; better_case_match; discriminate || ev; eauto. Qed.
  inv_mbind n.
    (** We must show that nmR is at least one, since that's required by the
        hypothesis of semantic expression typing for Hfun and Harg. *)
    inv_tevalSM.
    (* The iteration counts are optimized for speed, but it's also OK to do all *)
    (*   case splits in advance as in V1.1. *)
    do 2 better_case_match_ex; edestruct Harg; ev; eauto; try discriminate; injectHyps;
      do 3 better_case_match_ex; edestruct Hfun; ev; eauto; try discriminate; injectHyps;
        repeat better_case_match_ex; simp vtp in *; unfold expr_sem in *; unfoldTeval; eauto. contradiction.

  (* V1.1 less fast, more maintainable. *)
  (* n_is_succ_hp; destruct nmR; *)
  (*   repeat better_case_match_ex; edestruct Harg; ev; eauto; try discriminate; injectHyps; *)
  (*     better_case_match_ex; edestruct Hfun; ev; eauto; try discriminate; injectHyps; *)
  (*       simp vtp in *; unfold expr_sem in *; unfoldTeval; eauto; contradiction. *)
Qed.

(* Copy-paste of fund_t_rec. *)
Lemma fund_t_let: forall G T1 T2 t1 t2, sem_type G T1 t1 -> sem_type (T1 :: G) T2 t2 -> sem_type G T2 (tlet t1 t2).
Proof.
  unfold sem_type, etp, expr_sem; unfoldTeval;
  intros * Hvtp1 Hvtp2 ? ? * [nmR HappEv].

  (* Various implementations of the same case analysis are possible.
     It's faster to only do as much case analysis as strictly needed. *)

  (* V1 Fast *)
  n_is_succ_hp;
    (** We must show that nmR is at least one, since that's required by the
        hypothesis of semantic expression typing for Hfun and Harg. *)
    destruct nmR;
    (* The iteration counts are optimized for speed, but it's also OK to do all *)
    (*   case splits in advance as in V1.1. *)
    do 2 progress better_case_match_ex; edestruct Hvtp1; ev; eauto;
      do 3 better_case_match_ex; better_case_match_ex; eauto.
Qed.

Lemma fund_t_rec: forall G S T t, sem_type (S :: TFun S T :: G) T t -> sem_type G (TFun S T) (trec t).
Proof.
  unfold sem_type; simpl; intros; eapply vtp_etp with (nm := 0).
  - unfoldTeval; intros; step_eval; trivial.
  -
    unfold etp in *; simp vtp; eauto.
    intros.
    eapply H. repeat constructors; eauto.
    (* Now we're left again with the original question! *)
Abort.

(** Fundamental property.
    Proved by induction on typing derivations. *)
Theorem fundamental: forall G t T, has_type false G t T -> sem_type G T t.
Proof. intros * Htp; dependent induction Htp; eauto using fund_t_var, fund_t_nat, fund_t_abs, fund_t_app, fund_t_let.
Qed.

(** Type soundness: If evaluation of a well-typed program terminates, the result
    is not a runtime error. Proved as a corollary of the [fundamental] property. *)
Theorem sound: forall G t T env optV j, has_type false G t T ->
    R_env env G ->
    tevalSnOpt env t optV j ->
    exists v, optV = Some v /\ vtp T v.
Proof. intros; edestruct fundamental; ev; eauto. Qed.
(* Concluding tevalSn env t v j -> vtp T v would talk only about successful
   evaluations, not about runtime errors! *)