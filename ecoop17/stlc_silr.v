(** STLC_SILR: Step-indexed logical relations for STLC. *)

Require Import stlc.
Require Import Equations.Equations.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.

Definition val_type_measure T (k : nat) := (existT (fun _ => nat) k (tsize T)).
Hint Unfold val_type_measure.
Hint Transparent val_type_measure.

Definition argMeasure (p: ty * nat) := let '(T, n) := p in (existT (fun _ => nat) n (tsize T)).
Definition val_type_termRel := MR (lexprod lt (fun _ => lt)) argMeasure.
(* (fun p => let '(T, n) := p in (existT (fun _ => nat) n (tsize T))). *)

(* Definition termRel := lexprod lt (fun _ => lt). *)
(* Hint Unfold termRel. *)

Hint Constructors lexprod.

Lemma wf_val_type_termRel : well_founded val_type_termRel. Proof. apply measure_wf; apply wf_lexprod; intro; apply lt_wf. Defined.
Hint Resolve wf_val_type_termRel.
Instance WF_val_type_termRel: WellFounded val_type_termRel := wf_val_type_termRel.

Lemma ind_args : forall (P: ty -> nat -> Prop),
    (forall T n,
        (forall T' n', val_type_termRel (T', n') (T, n) -> P T' n') -> P T n) ->
    forall T n, P T n.
Proof.
  intros * Hind *.
  pose (p := (T, n));
  replace T with (fst p) by reflexivity;
  replace n with (snd p) by reflexivity;
  generalize dependent p;
  clear T n.
  eapply well_founded_ind; eauto.
  intros p1 Hless.
  destruct p1 as [T n]; simpl in *.
  apply Hind.
  intros *.
  apply Hless.
Qed.

Ltac vtp_induction T n :=
  apply ind_args with (T := T) (n := n);
  clear T n.

Definition pretype_dom n :=
  forall (n0: nat) (H: n0 <= n), vl_prop.
Hint Unfold pretype_dom.

Module Type SilrVtpArg.
  Parameter vtp : ty -> nat -> vl_prop.
  Parameter expr_sem : forall (n: nat), ty -> pretype_dom n -> venv -> tm -> Prop.
End SilrVtpArg.

(* Hook to fill in later. *)
Definition wf {A} (G : list A) (T: ty) := True.
(* closed (length G) 0 T. *)
Module SilrEnvs (VTP: SilrVtpArg).
  Import VTP.

  Inductive R_env (k : nat) : venv -> tenv -> Set :=
  | R_nil :
      R_env k [] []
  | R_cons : forall T v env G,
      R_env k env G ->
      vtp T k v ->
      R_env k (v :: env) (T :: G).
  Hint Constructors R_env.

  Lemma wf_length : forall k vs ts,
      R_env k vs ts ->
      (length vs = length ts).
  Proof. intros * H; induction H; simpl; congruence. Qed.

  Ltac lenG_to_lenEnv :=
    try match goal with
        | H: R_env _ ?env ?G |- _ =>
          replace (length G) with (length env) in * by (eauto using wf_length)
        end.

  Lemma R_env_to_indexr_success: forall G env x T k, indexr x G = Some T -> R_env k env G -> exists v, indexr x env = Some v.
    intros * HT Henv; induction Henv; simpl in *;
      [ discriminate |
        lenG_to_lenEnv;
        repeat (better_case_match; beq_nat); eauto].
  Qed.
  Hint Resolve R_env_to_indexr_success.

  Lemma R_env_to_vtp: forall G env x T v k, indexr x G = Some T -> indexr x env = Some v -> R_env k env G -> vtp T k v.
  Proof.
    intros * HT Hv Henv; induction Henv; simpl in *;
      [ discriminate |
        lenG_to_lenEnv;
        repeat (better_case_match; beq_nat); eauto].
  Qed.
  Hint Resolve R_env_to_vtp.

  Definition etp T k env e :=
    expr_sem k T (fun k _ => vtp T k) env e.

  (* Semantic typing *)
  Definition sem_type G T e :=
    wf G T /\
    forall k env,
      R_env k env G ->
      etp T k env e.

  Definition sem_vl_subtype (G : tenv) (T1 T2: ty) :=
    wf G T1 /\
    wf G T2 /\
    forall k env,
      R_env k env G ->
      forall v, vtp T1 k v -> vtp T2 k v.

  Definition sem_subtype (G : tenv) (T1 T2: ty) :=
    sem_vl_subtype G T1 T2 /\
    forall k env,
      R_env k env G ->
      forall e, etp T1 k env e -> etp T2 k env e.

  Lemma subtype_to_vl_subtype : forall G T1 T2,
      sem_subtype G T1 T2 -> sem_vl_subtype G T1 T2.
  Proof. unfold sem_subtype; tauto. Qed.
  Hint Resolve subtype_to_vl_subtype.

End SilrEnvs.

(* Maybe make both normal definitions, or at least Program Definitions? Let's limit equations weird rules? *)
(* Only expr_sem changes in definitions between here and normalization. *)
(* Definition expr_sem : forall (n: nat), ty -> pretype_dom n -> forall k, k <= n -> venv -> tm -> Prop. *)
Program Definition expr_sem n (T : ty) (A : pretype_dom n) (env: venv) (t : tm): Prop :=
  forall optV j (Hj: j <= n) nmj,
    tevalSnOpt env t optV j -> forall (Hnmj: nmj = n - j), exists v, optV = Some v /\ A nmj _ v.

Lemma termRelShow: forall j n T1 T2,
  j <= n -> tsize T2 < tsize T1 ->
  val_type_termRel (T2, j) (T1, n).
Proof.
  intros * Hj Ht; unfold val_type_termRel, MR, argMeasure.
  (* If we only know that Hj: j <= n, we must case-split on it, and use
     smaller_types when j = n and smaller_n when j < n. *)
    destruct Hj; try assert (j < S m) by omega; auto.
Qed.
Hint Resolve termRelShow.

(* Non-step-indexed unary logical relation. *)
Equations val_type (Tn: ty * nat) (v : vl) : Prop :=
  val_type Tn t by rec Tn val_type_termRel :=
  val_type (pair TNat n) (vnat _) := True;
  val_type (pair (TFun T1 T2) n) (vabs env body) := forall v k (Hk : k <= n), val_type (T1, k) v -> expr_sem k T2 (fun j _ v => val_type (T2, j) v) (v :: env) body;
  val_type (pair (TFun T1 T2) n) (vrec env body) := forall v k (Hk : k < n), val_type (T1, k) v -> expr_sem k T2 (fun j _ v => val_type (T2, j) v) (v :: vrec env body :: env) body;
  val_type _ _ := False.

Solve All Obligations with program_simpl.

Definition vtp T n v := val_type (T, n) v.
Include SilrEnvs.

Lemma val_type_mon: forall T v m n,
    val_type (T, n) v ->
    m <= n ->
    val_type (T, m) v.
Proof.
  intros; gen m.
  funind (val_type (T, n) v) Hcall;
    intros; eauto;
      simp val_type; eauto.
Qed.
Hint Extern 5 (val_type _ _) => try_once val_type_mon.

Lemma vtp_mon: forall T v m n,
    vtp T n v ->
    m <= n ->
    vtp T m v.
Proof. eapply val_type_mon. Qed.
Hint Extern 5 (vtp _ _ _) => try_once vtp_mon.

Lemma R_env_mon: forall G env m n,
    R_env n env G ->
    m <= n ->
    R_env m env G.
Proof. intros * Henv; induction Henv; eauto. Qed.
Hint Extern 5 (R_env _ _ _) => try_once R_env_mon.

Lemma wf_all: forall {A} (G : list A) T, wf G T.
Proof. auto. Qed.
Hint Resolve wf_all.

Example ex0 : forall k, vtp (TFun TNat TNat) k (vabs [] (tvar 0)).
Proof.
  unfold vtp; intros. simp val_type; unfold expr_sem; intros.
  split_conj; intros; eauto;
    unfoldTeval; n_is_succ_hp; eauto.
Qed.

Lemma vl_subtype_to_subtype : forall G T1 T2,
    sem_vl_subtype G T1 T2 -> sem_subtype G T1 T2.
Proof.
  unfold sem_subtype, sem_vl_subtype, etp, expr_sem.
  intros; ev; split_conj; eauto.
  intros * ? * HeT1. intuition eauto; edestruct HeT1; ev; eauto.
Qed.
Hint Resolve vl_subtype_to_subtype.

Require Import PropExtensionality.
Lemma vl_sub_equiv: sem_subtype = sem_vl_subtype.
Proof.
  repeat (apply functional_extensionality; intro); apply propositional_extensionality;
    split; eauto.
Qed.
Hint Rewrite vl_sub_equiv.

Hint Unfold tevalSnmOpt tevalSnOpt tevalSnm tevalSn.
Lemma etp_vtp_j: forall e v k j nm T env,
    tevalSnm env e v j nm -> etp T k env e -> j <= k -> vtp T (k - j) v.
Proof.
  intros.
    assert (exists v0, Some v = Some v0 /\ vtp T (k - j) v0) by
      (unfold etp, expr_sem in *; iauto).
  ev; eauto.
Qed.
Hint Resolve etp_vtp_j.

Lemma etp_vtp: forall e v k nm T env,
    tevalSnm env e v 0 nm -> etp T k env e -> vtp T k v.
Proof. eauto. Qed.
Hint Resolve etp_vtp.
(* Unused *)
(* Hint Resolve etp_vtp. *)

Lemma vtp_etp_j: forall e v T env k j nm,
    vtp T (k - j) v ->
    tevalSnm env e v j nm ->
    j <= k ->
    etp T k env e.
Proof. unfold etp, expr_sem; unfold2tevalSnmOpt; intuition trivial; eval_det; iauto. Qed.
Hint Resolve vtp_etp_j.

Lemma vtp_etp:
  forall e v T env k nm,
    tevalSnm env e v 0 nm ->
    vtp T k v ->
    etp T k env e.
Proof. eauto. Qed.
Hint Resolve vtp_etp.

Ltac int := intuition trivial.
(* XXX use the same trick as vtpEnvCore vs vtpEnv in definitions *)
Lemma fund_t_abs: forall G T1 T2 t,
    sem_type (T1 :: G) T2 t ->
    sem_type G (TFun T1 T2) (tabs t).
Proof.
  unfold sem_type; int; eapply vtp_etp with (nm := 0).
  - unfoldTeval; intros; step_eval; trivial.
  - unfold etp, vtp in *; simp val_type; iauto.
Qed.

Lemma fund_t_var: forall G x T, indexr x G = Some T -> sem_type G T (tvar x).
Proof.
  unfold sem_type, etp, expr_sem; int;
    pose proof (teval_var env x); eval_det; subst.
  edestruct R_env_to_indexr_success; eauto.
Qed.

Lemma fund_t_nat: forall G n,
    sem_type G TNat (tnat n).
Proof.
  unfold sem_type; int; eapply vtp_etp with (nm := 0).
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
  unfold sem_type, etp, vtp, expr_sem; unfoldTeval.
  intros * [? Hfun] [? Harg]; split_conj; eauto;
  intros * ? * ? * [nmR HappEv] **; subst.

  (* Various implementations of the same case analysis are possible.
     It's faster to only do as much case analysis as strictly needed. *)

  Ltac appVtpEval HvtpT t j :=
    match goal with
    | H : tevalS t _ _ = Some (?o, ?n) |- _ =>
      assert (n <= j) by (repeat better_case_match_ex; omega); lets ? : HvtpT o n ___; eauto; ev
    end.

  (* V1 Fast *)
  n_is_succ_hp;
    (** We must show that nmR is at least one, since that's required by the
        hypothesis of semantic expression typing for Hfun and Harg. *)
    destruct nmR;
    (* The iteration counts are optimized for speed, but it's also OK to do all *)
    (*   case splits in advance as in V1.1. *)
    do 2 better_case_match_ex; appVtpEval Harg t2 j;
  (* ev; eauto. try discriminate; injectHyps. *)
      do 3 better_case_match_ex; appVtpEval Hfun t1 j; ev; eauto.
  repeat better_case_match_ex; simp val_type in *; unfold expr_sem in *; unfoldTeval.
  all: try contradiction.
  - lets Hs : H7 x (k - n - n0) __ __; eauto 2.
    lets Hgoal : (Hs optV n1) __ __ __ __ ; eauto 3.
    ev; repeat esplit; eauto.

  - lets Hs : H7 x (k - n - n0 - 1) __ __; eauto 2.
    lets (res & -> & Hgoal) : (Hs optV n1) __ __ __ __ ; eauto 3.
    ev; repeat esplit.
    eapply (val_type_mon _ _ _ _ Hgoal).
    Require Import Lia.
    lia.

Qed.
  (* clear. *)
  (* simpl. *)

  (* Goal forall k n n0 n1, k - (n + n0 + 1 + n1) <= k - n - n0 - 1 - n1. *)
  (*   intros. *)
  (*   lia. omega. *)
  (* eapply Nat.eq_le_incl. *)
  (* omega. *)
  (* Search (?m = ?n -> ?m <= ?n). *)

  (* constructor. *)
  (* omega. *)
  (* Check (val_type_mon Hgoal). *)
  (* eauto. *)
  (* try_once val_type_mon; eauto. *)

  (* eapply Hgoal. *)
  (* lets ? : H2 Heqo __. *)
  (*   match goal with *)
  (*   | H : tevalS t _ _ = Some (?o, ?n), Hvtp: context [tevalS t] |- _ => *)
  (*     idtac Hvtp; *)
  (*     assert (n <= j) by admit; lets ? : HvtpT o n ___; eauto; ev *)
  (*   end. *)
Lemma loeb_vtp: forall T v,
    (forall k, (forall j, j < k -> vtp T j v) -> vtp T k v) ->
    forall j, vtp T j v.
Proof.
  unfold vtp; intros * Hloeb **. induction j;
    [ pose (l := 0) | pose (l := (S j)) ];
    lets H : Hloeb l; subst l;
      eapply H; intros; eauto; lia.
Qed.

Lemma loeb_vtp_2: forall n T v,
    (forall k, k <= n -> (forall j, j < k -> vtp T j v) -> vtp T k v) ->
    forall k, k <= n -> vtp T k v.
Proof.
  unfold vtp; intros * Hloeb. induction n;
    (* [ pose (l := 0) | pose (l := (S n)) ]; *)
    intros; try assert (k = 0) as -> by omega.
  - apply (Hloeb 0); trivial; intros; lia.
  - eauto.
Qed.
Lemma loeb_vtp_3: forall n T v,
    (forall k, k <= n -> (forall j, j < k -> vtp T j v) -> vtp T k v) ->
    vtp T n v.
Proof.
  unfold vtp; intros * Hloeb.
  induction n; intros;
    [apply (Hloeb 0); int; lia | eauto].
Qed.

(*     apply Hloeb; try lia. *)
(*     intros; apply IHn; try lia. *)
(*     intros. apply Hloeb. *)
(*     (* info_eauto 4. *) *)
(* (* info eauto: *) *)
(* simple apply Hloeb. *)
(* exact H. *)
(* intros. *)
(* simple apply IHn. *)
(* intros. *)
(* simple apply Hloeb. *)
(* (*external*) ineq_solver. *)
(* exact H2. *)
(* (*external*) ineq_solver. *)

(* No more subgoals. *)



(*   eapply (val_type_mon _ _ k (S n)); trivial. *)
(*   eapply Hl. *)
(*   intros. *)
(*   assert (j <= n) by lia. *)
(*   eapply (val_type_mon _ _ j n); trivial. *)
(*   eauto. *)
(*   eapply IHn; trivial. *)
(*   eauto. *)
(*   eapply Hl; intros; eauto. lia. *)
(* Qed. *)

Lemma fund_t_rec: forall G S T t, sem_type (S :: TFun S T :: G) T t -> sem_type G (TFun S T) (trec t).
Proof.
  unfold sem_type; intros * [? HvtpBody]; int. eapply vtp_etp with (nm := 0).
  - unfoldTeval; intros; step_eval; trivial.
  -
    (** We must show that the recursive closure [vrec env t] is semantically well-typed.
        We proceed by Loeb induction. *)
    eapply loeb_vtp_3; int.
    unfold etp in *; unfold vtp; simp val_type; int.
    eapply HvtpBody.
    (** Now we must show the recursive environment is also well-typed.
        For most entries this is trivial, but this environment also includes the
        recursive closure, so we're almost back where we started.

        However, we only need well-typedness *at a smaller index*, which we have
        as the inductive hypothesis of Loeb induction! *)
    repeat constructors; eauto.
Qed.


(* Copy-paste of fund_t_app. *)
Lemma fund_t_let: forall G T1 T2 t1 t2, sem_type G T1 t1 -> sem_type (T1 :: G) T2 t2 -> sem_type G T2 (tlet t1 t2).
Proof.
  (* unfold sem_type, etp, expr_sem; unfoldTeval; *)
  (* intros * Hvtp1 Hvtp2 ? ? * [nmR HappEv]. *)

  unfold sem_type, etp, vtp, expr_sem; unfoldTeval.
  intros * [? Hvtp1] [? Hvtp2]; split_conj; eauto;
  intros * ? * ? * [nmR HappEv] **; subst.

  (* Various implementations of the same case analysis are possible. *)
(*      It's faster to only do as much case analysis as strictly needed. *)

  (* V1 Fast *)

  n_is_succ_hp;
    (** We must show that nmR is at least one, since that's required by the *)
(*         hypothesis of semantic expression typing for Hfun and Harg. *)
    destruct nmR;
    (* The iteration counts are optimized for speed, but it's also OK to do all *)
    (*   case splits in advance as in V1.1. *)
    do 2 progress better_case_match_ex; appVtpEval Hvtp1 t1 j; subst;
  do 3 better_case_match_ex; appVtpEval Hvtp2 t2 (k - n); eauto.
Qed.

(** Fundamental property.
    Proved by induction on typing derivations. *)
Theorem fundamental: forall G t T b, has_type b G t T -> sem_type G T t.
Proof. intros * Htp; induction Htp; eauto using fund_t_var, fund_t_nat, fund_t_abs, fund_t_rec, fund_t_app, fund_t_let.
Qed.

(** Type soundness: If evaluation of a well-typed program terminates, the result
    is not a runtime error. Proved as a corollary of the [fundamental] property. *)
Theorem sound: forall G t T env optV k j b, has_type b G t T -> j <= k ->
    R_env k env G ->
    tevalSnOpt env t optV j ->
    exists v, optV = Some v /\ vtp T (k - j) v.
Proof. intros. eapply fundamental; eauto. Qed.
