Require Import tactics.
Require Import dot_wfrel.
Require Import dot_base.
Require Import dot_eval.
Require Import LibTactics.

Lemma vtp_unfold : forall T n v env,
    vtp T n v env =
    match T with
    | TAll T1 T2 =>
      closed_ty 0 (length env) T1 /\ closed_ty 1 (length env) T2 /\
      interpTAll n
                 (fun n p => vtp T1 n)
                 (fun n p => vtp (open (varF (length env)) T2) n)
                 n (le_n _) v env
    | TMem T1 T2 =>
      closed_ty 0 (length env) T1 /\ closed_ty 0 (length env) T2 /\
      interpTMem n
                 (fun n p => vtp T1 n)
                 (fun n p => vtp T2 n)
                 (fun T j p => vtp T j)
                 n (le_n _) v env
    | TTop => True
    | TBot => False
    | TSel x =>
      interpTSel n x (fun T j p => vtp T j)
                n (le_n _) v env
    | TAnd T1 T2 =>
      interpTAnd n
                 (fun n p => vtp T1 n)
                 (fun n p => vtp T2 n)
                 n (le_n _) v env
    | TBind T1 =>
      closed_ty 1 (length env) T1 /\
      vtp (open (varF (length env)) T1) n v (v::env)
    | TLater T =>
      interpTLater n
                 (fun n p => vtp T n)
                 (closed_ty 0 (length env) T)
                 n (le_n _) v env
    end.
Proof.
  intros;
    rewrite vtp_to_val_type;
    rewrite val_type_unfold;
    reflexivity.
Qed.

(* Split it here *)
Example ex0 : forall n v, vtp TTop n v [].
Proof.
  intros. rewrite vtp_unfold. auto.
Qed.

(* Example ex1: forall env T n, exists dd, forall v, vtp T n v env <-> dd v. *)
(* Proof. *)
(*   intros. remember (fun v => vtp T n v env) as V. *)

(*   simpl. *)
(*   exists V. *)
(*   exists (fun v => vtp T n v env). intros. *)
(*   split; intros; assumption. *)
(* Qed. *)

(* Simplify vtp when applied to a partially-known argument. *)
Ltac simpl_vtp :=
  match goal with
  | H : context [ vtp ?T _ _ _ ] |- _ =>
    tryif is_var T then fail else rewrite (vtp_unfold T) in H
  | |- context [ vtp ?T _ _ _ ] =>
    tryif is_var T then fail else rewrite (vtp_unfold T)
  end.

Example ex3: forall env T n, vtp (TMem TBot TTop) n (vty env T) [].
Proof.
  intros; rewrite vtp_unfold;
    repeat split_and; try constructor; repeat simpl_vtp; tauto.
Qed.

(* Infrastructure for well-founded induction for properties of vtp. *)
Lemma ind_args : forall (P: ty -> nat -> Prop),
    (forall T n,
        (forall T' n', val_type_termRel (T', n') (T, n) -> P T' n') -> P T n) ->
    forall T n, P T n.
Proof.
  intros * Hind *.
  pose (p := (T, n)).
  replace T with (fst p) by reflexivity.
  replace n with (snd p) by reflexivity.
  generalize dependent p.
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

Hint Unfold interpTAll interpTSel interpTMem interpTSel0 interpTAnd interpTLater.
Ltac vtp_unfold_pieces :=
  unfold interpTAll, interpTSel, interpTMem, interpTSel0, interpTAnd, interpTLater, expr_sem in *.
Ltac vtp_simpl_unfold := repeat simpl_vtp; vtp_unfold_pieces.

Lemma vtp_closed: forall T k v env,
    vtp T k v env -> closed_ty 0 (length env) T.
Proof.
  induction T; intros; destruct v; rewrite vtp_unfold in *; vtp_unfold_pieces; ev; try eauto;
  repeat case_match; repeat constructor; try contradiction; eauto.
Qed.
Hint Resolve vtp_closed.

Lemma vtp_mon: forall T env v m n,
    vtp T n v env ->
    m <= n ->
    vtp T m v env.
Proof.
  intros *.
  revert env v m.

  (* The proof is by well-founded induction on type T and count n, because monotonicity on intersection types follows by induction. *)
  vtp_induction T n.
  (* apply ind_args with (T := T) (n := n). *)
  (* clear T n. *)

  intros * Hind * Hvtpn1 * Hmn.

  (* We proceed by case analysis on types and values. *)
  destruct T;
    destruct v;
    rewrite vtp_unfold in *;
    vtp_unfold_pieces;
    ev; repeat split_conj;
      repeat case_match.
  (* We could finish the proof by a single line combining the next tactics. *)
  (* But let's look how our cases (24 right now!) are solved. *)
  (* Most cases (12) follow trivially, or by using the induction hypothesis. *)
  all: trivial.
  (* Many other cases (6) have hypothesis for all j < n and have a conclusion for
     all j < m (with m < n). So we assert that j < n, and then Coq can finish
     the proof automatically. *)

  all: intros; try assert (Hjn: j < n) by omega; try assert (j <= n) by omega; auto 2.

  (* A couple (6) follow just by using induction on smaller types. *)
  all: try (apply Hind with (n' := n); try smaller_types; assumption).

  (* handle TLater, for when m is less than 0 *)
  all: try omega.
  (* If m = 0 we must show that the produced type is closed. *)
  all: eauto using vtp_closed.

  (* handle TLater, for when m isn't 0.
     XXX: this assumes we have n = S n0 and m = S n1. *)
  all: assert (n1 <= n0) by auto;
    eapply Hind with (T' := T) (n' := n0) (m := n1);
    try smaller_n; assumption.

  (* XXX Sort-of-working alternative to avoid relying on generated names. Must
     be pasted twice, because Coq rejects this under all, as it doesn't believe
     that n is available in both branches.
   *)
    (* match goal with *)
    (* | [H : n = S ?n0 |- _ ] => rename n0 into n' *)
    (* end; *)
    (* match goal with *)
    (* | [H : m = S ?m0 |- _ ] => rename m0 into m' *)
    (* end; *)
    (* assert (m' <= n') by auto; *)
    (* eapply Hind with (T' := T) (n'0 := n') (m := m'); *)
    (* try smaller_n; assumption. *)
Qed.

Hint Resolve vtp_mon.

(* XXX questionable, why take env? But that comes from how vtp's defined internally. *)
Record vset := mkVset
  {
    pred : nat -> vl_prop;
    mon : forall env v m n, pred n v env -> m <= n -> pred m v env
  }.
Definition vtp_as_vset (T : ty) : vset :=
  {| pred := vtp T;
     mon := vtp_mon T
  |}.

Record vset' := mkVset'
  {
    pred' : nat -> vl -> Prop;
    mon' : forall v m n, pred' n v -> m <= n -> pred' m v
  }.
Definition vtp_as_vset' (T : ty) (env : venv): vset' :=
  {| pred' := fun n v => vtp T n v env;
     mon' := vtp_mon T env
  |}.

(* XXX Beware: here TAll is non-expansive rather than contractive, I guess by mistake. *)

(* Next step: define valid environments, then semantic typing! *)
Definition R_env_all k env G :=
  length env = length G /\
  forall x TX, indexr x G = Some TX ->
    (exists vx,
       indexr x env = Some vx /\ vtp TX k vx env).

Inductive R_env (k : nat) : venv -> tenv -> Set :=
  (* (env: venv) (G: tenv) : Set := *)
| R_nil :
    R_env k [] []
| R_cons : forall T v env G,
    R_env k env G ->
    vtp T k v (v :: env) ->
    R_env k (v :: env) (T :: G)
.

(* automation *)
Hint Unfold venv.
Hint Unfold tenv.

(* Hint Unfold R. *)
Hint Unfold R_env_all.
Hint Constructors R_env.

Lemma R_env_mon: forall G env m n,
    R_env n env G ->
    m <= n ->
    R_env m env G.
Proof.
  intros * Henv; induction Henv; eauto.
Qed.
Hint Resolve R_env_mon.

Lemma wf_length_all : forall k vs ts,
                    R_env_all k vs ts ->
                    (length vs = length ts).
Proof.
  intros * H. induction H. auto.
Qed.
Lemma wf_length : forall k vs ts,
                    R_env k vs ts ->
                    (length vs = length ts).
Proof.
  intros * H; induction H; simpl; congruence.
Qed.

Program Definition etp T k e env :=
  @expr_sem k (fun k _ => vtp T k) k _ env e env.

(* Semantic typing *)
Definition sem_type (G : tenv) (T : ty) (e: tm) :=
  forall k env,
    R_env k env G ->
    etp T k e env.

Definition sem_subtype (G : tenv) (T1 T2: ty) :=
  forall k env,
    R_env k env G ->
    forall e, etp T1 k e env -> etp T2 k e env.

Definition sem_vl_subtype (G : tenv) (T1 T2: ty) :=
  forall k env,
    R_env k env G ->
    forall v, vtp T1 k v env -> vtp T2 k v env.

Hint Unfold sem_type sem_subtype sem_vl_subtype etp.

Lemma vl_subtype_to_subtype : forall G T1 T2,
    sem_vl_subtype G T1 T2 -> sem_subtype G T1 T2.
Proof.
  unfold sem_subtype, sem_vl_subtype, etp;
  vtp_unfold_pieces;
  firstorder eauto.
Qed.
Hint Resolve vl_subtype_to_subtype.

Lemma and_stp1 : forall env T1 T2 n v, vtp (TAnd T1 T2) n v env -> vtp T1 n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

Lemma sem_and_stp1 : forall G T1 T2, sem_subtype G (TAnd T1 T2) T1.
Proof. eauto using and_stp1. Qed.

Lemma and_stp2 : forall env T1 T2 n v, vtp (TAnd T1 T2) n v env -> vtp T2 n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

Lemma sem_and_stp2 : forall G T1 T2, sem_subtype G (TAnd T1 T2) T2.
Proof. eauto using and_stp2. Qed.

Lemma stp_and' : forall env T1 T2 n v, vtp T1 n v env -> vtp T2 n v env -> vtp (TAnd T1 T2) n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

Lemma stp_and : forall env S T1 T2 n v,
    (vtp S n v env -> vtp T1 n v env) ->
    (vtp S n v env -> vtp T2 n v env) ->
    vtp S n v env -> vtp (TAnd T1 T2) n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

(* Can't do the version with sem_subtype until we add later as a type constructor. *)
(* First attempt. *)
Lemma mem_stp' : forall env x L U n v vx,
    vtp (TMem L U) (S n) v env ->
    vtp L n vx env ->
    indexr x env = Some v ->
    vtp (TSel (varF x)) n vx env.
Proof.
  intros; vtp_simpl_unfold; repeat case_match; ev; intros; try injections_some;
    solve [tauto | discriminate | assert (j < S n) by auto; firstorder eauto].
Qed.

(* Better attempt, where I only use "later" L, as expected. Note the proof is simpler! *)
Lemma mem_stp : forall env x L U n v vx,
    vtp (TMem L U) (S n) v env ->
    vtp L n vx env ->
    indexr x env = Some v ->
    vtp (TSel (varF x)) (S n) vx env.
Proof.
  intros; vtp_simpl_unfold; repeat case_match; ev; intros; try injections_some;
    solve [tauto | discriminate | firstorder eauto].
Qed.

(* Annoying: proof search by firstorder can't instantiate j < S n with j := n, unless we add a hint. *)
Lemma stp_mem : forall env x L U n v vx,
    vtp (TMem L U) (S n) v env ->
    vtp (TSel (varF x)) (S n) vx env ->
    indexr x env = Some v ->
    vtp U n vx env.
Proof.
  intros; vtp_simpl_unfold; repeat case_match; ev; intros; try injections_some;
    solve [tauto | discriminate | assert (n < S n) by auto; firstorder eauto].
Qed.

Program Definition vl_to_tm (v : vl): { (e, env) : tm * venv | forall n, forall Hfuel : n > 0, tevalS e n env = Some (Some v, 0) } :=
  match v with
  | vabs env T body =>
    (tabs T body, env)
  | vty env T =>
    (ttyp T, env)
  end.
Solve Obligations with program_simplify; destruct n; solve [inverse Hfuel] || reflexivity.

(* Require Import dot_monads. *)
(* Lemma inv_success_mbind2: *)
(*   forall {A B} {f : A -> option B} {c} {x}, *)
(*     bind c f = Some x -> *)
(*     exists y, c = Some y /\ f y = Some x. *)
(* Proof. *)
(*   intros * H. *)
(*   destruct c; simpl in * |-; try congruence. *)
(*   exists a. auto. *)
(* Qed. *)

(* Ltac inv_mbind := *)
(*   match goal with *)
(*     H : bind _ _ = Some _ |- _ => *)
(*     let x := fresh "x" in *)
(*     let Ha := fresh "Ha" in *)
(*     let Hb := fresh "Hb" in *)
(*     apply inv_success_mbind2 in H; *)
(*     (* invert, in one go, H into its pieces *) *)
(*     inversion H as [x [Ha Hb] ] *)
(*   end. *)

(* Ltac inv_mbind_some := *)
(*   repeat inv_mbind; repeat injections_some. *)

(* (* Lemma tevalS_mono: forall n e env optV, tevalS e n env = Some optV -> forall m, m >= n -> tevalS e m env = Some optV. *) *)
(* (*   induction e; *) *)
(* (*   induction n; intros * Heval * Hmn; try solve [inverse Heval]; *) *)
(* (*   destruct m; inversion Hmn; clear Hmn; subst; auto. *) *)
(* (*   simpl in Heval. simpl. *) *)
(* (*   eapply inv_success_mbind2 in Heval. *) *)

(* (* Lemma tevalSM_mono: forall e n env optV, tevalSM e n env = Some optV -> forall m, m >= n -> tevalSM e m env = Some optV. *) *)
(* (*   induction e; *) *)
(* (*   induction n; intros * Heval * Hmn; try solve [inverse Heval]; *) *)
(* (*   destruct m; inversion Hmn; clear Hmn; subst; auto. *) *)
(* (*   unfold tevalSM in Heval. *) *)
(* (*   eapply inv_success_mbind2 in Heval. *) *)
(* (*   fold tevalSM in *. *) *)
(* (*   unfold tevalSM. inv_mbind_some. *) *)
(* (*             inv_mbind_some; auto. *) *)
(* (*   - repeat inv_mbind_some. *) *)
(* (*     inversion Heval; subst; auto. *) *)

Lemma n_to_Sn: forall n m, n > m -> exists n', n = S n'.
  intros; destruct n; [ exfalso; omega | eauto].
Qed.
Hint Unfold gt ge lt.
Ltac n_is_succ :=
  unfold gt, ge, lt in *;
  match goal with
  | [H : S ?m <= ?n |- _] =>
    (* idtac *)
    apply n_to_Sn in H; let n' := fresh n in destruct H as [n' ->]
  end.
Tactic Notation "n_is_succ'" simple_intropattern(P) :=
  unfold gt, ge, lt in *;
  match goal with
  | [H : S ?m <= ?n |- _] =>
    apply n_to_Sn in H; destruct H as P
  end.

Ltac step_eval := n_is_succ; simpl in *.

(* Lemma tevalS_mono: forall n e env optV, tevalS e n env = Some optV -> forall m, m >= n -> tevalS e m env = Some optV. *)
(* Proof. *)
(*   induction n; intros * Heval * Hmn; try solve [inverse Heval]. *)
(*   assert (exists m', m = S m') as [m' ->] by ( *)
(*     destruct m; inversion Hmn; subst; eexists; auto *)
(*   ). *)
(*   (* destruct Hm as [m' ?]; subst. *) *)
(*   generalize dependent optV. *)
(*   generalize dependent n. *)
(*   induction e; auto; intros. *)
(*   - *)
(*     (* This is the job of inv_mbind or similar. *) *)
(*     assert (exists optV1, tevalS e1 n env = Some optV1) as [[optV1 j1] Hevaln1] by admit. *)
(*     assert (exists optV2, tevalS e2 n env = Some optV2) as [[optV2 j2] Hevaln2] by admit. *)
(*     (* Here auto uses the induction hypothesis! *) *)
(*     simpl in *. *)
(*     assert (tevalS e1 m' env = tevalS e1 n env) as -> by (rewrite Hevaln1; auto). *)
(*     assert (tevalS e2 m' env = tevalS e2 n env) as -> by (rewrite Hevaln2; auto). *)
(*     rewrite Hevaln1 in *. *)
(*     rewrite Hevaln2 in *. *)

(*     do 3 case_match; auto. *)
(*     unfold step in *. *)

(*     assert (exists optV0 j0, tevalS t0 n (v :: l) = Some (optV0, j0)) as [optV0 [j0 Hevaln0]] by admit. *)
(*     assert (tevalS t0 m' (v :: l) = tevalS t0 n (v :: l)) as -> by (rewrite Hevaln0; auto). *)
(*     rewrite Hevaln0 in *; injections_some; auto. *)
(*   -  *)
(*     assert (exists optV1, tevalS e1 n env = Some optV1) as [[optV1 j1] Hevaln1] by admit. *)
(*     simpl in *. *)
(*     assert (tevalS e1 m' env = tevalS e1 n env) as -> by (rewrite Hevaln1; auto). *)
(*     rewrite Hevaln1 in *. *)

(*     case_match; auto. *)
(*     unfold step in *. *)

(*     assert (exists optV2, tevalS e2 n (v::env) = Some optV2) as [[optV2 j2] Hevaln2] by admit. *)
(*     assert (tevalS e2 m' (v::env) = tevalS e2 n (v::env)) as -> by (rewrite Hevaln2; auto). *)
(*     rewrite Hevaln2 in *; injections_some; auto. *)
(* Admitted. *)
(* TODO: prove as exercise that if `eval (tapp e1 e2)` succeeds, evaluating e1 *)
(* and e2 succeeds. That should be an exercise on some tactic like inv_mbind. *)

(* We want to relate etp and vtp. *)
Lemma etp_vtp_j: forall e v k j nm T env,
    tevalSnm env e v j nm -> etp T k e env -> j <= k -> vtp T (k - j) v env.
Proof.
  intros;
  assert (exists v0, Some v = Some v0 /\ vtp T (k - j) v0 env) by eauto;
  ev; injections_some; eauto.
Qed.
Hint Resolve etp_vtp_j.

Lemma etp_vtp: forall e v k nm T env,
    tevalSnm env e v 0 nm -> etp T k e env -> vtp T k v env.
Proof. eauto. Qed.
Hint Resolve etp_vtp.

Lemma vtp_etp_j: forall e v T env k j nm,
    vtp T (k - j) v env ->
    tevalSnm env e v j nm ->
    j <= k ->
    etp T k e env.
Proof.
  intros * Hvtp Heval Hkj.
  unfold etp; vtp_unfold_pieces; unfold tevalSnOpt, tevalSnm in *.
  intros * [nm' Heval'] Hkj0.
  assert (optV = Some v /\ j = j0) as [-> ->] by (
    pose (N := nm + nm' + 1);
    assert (tevalS e N env = Some (Some v, j)) by (subst N; auto);
    assert (tevalS e N env = Some (optV, j0)) by (subst N; auto);
    split_conj; congruence);
  eexists; split_conj; eauto.
Qed.
Hint Resolve vtp_etp_j.

Lemma vtp_etp:
  forall e v T env k nm,
    vtp T k v env ->
    tevalSnm env e v 0 nm ->
    etp T k e env.
Proof. eauto. Qed.
Hint Resolve vtp_etp.

Lemma subtype_to_vl_subtype : forall G T1 T2,
    sem_subtype G T1 T2 -> sem_vl_subtype G T1 T2.
Proof.
  unfold sem_subtype, sem_vl_subtype.
  intros * H * Henv * HvT1.
  destruct (vl_to_tm v) as [[e env1] Heval]; eauto.
Admitted.
(* Qed. *)
Hint Resolve subtype_to_vl_subtype.

Lemma vl_sub_equiv: sem_subtype = sem_vl_subtype.
Proof.
  repeat (apply functional_extensionality; intro); apply prop_extensionality;
    split; eauto.
Qed.
Hint Rewrite vl_sub_equiv.

Lemma sem_stp_and : forall G S T1 T2,
    sem_subtype G S T1 ->
    sem_subtype G S T2 ->
    sem_subtype G S (TAnd T1 T2).
Proof.
  rewrite vl_sub_equiv; intros; eauto using stp_and.
Qed.

Lemma vtp_extend : forall vx v k env T,
  vtp T k v env ->
  vtp T k v (vx::env).
Proof.
  intros; vtp_simpl_unfold.
Admitted.
Hint Immediate vtp_extend.

Lemma vtp_etp_rev:
  forall e v T env k nm,
    tevalSnm env e v 0 nm ->
    vtp T k v env ->
    etp T k e env.
  eauto. Qed.

Lemma t_forall_i: forall G T1 T2 t,
  (* sem_type (T1 :: G) T2 t -> *)
  sem_type (T1 :: G) (open (varF (length G)) T2) t ->
  sem_type G (TAll T1 T2) (tabs T2 t).
Proof.
  unfold sem_type. intros.
  (* XXX needed: Lemma for syntactic values. *)
  (* Also needed: a way to swap goals that actually works! *)
  eapply vtp_etp_rev with (nm := 0).
  - unfold tevalSnm, tevalSnmOpt; intros; step_eval; trivial.
  -
    unfold etp in *; vtp_simpl_unfold;
    split_conj.
    + admit.
    + admit.
      (* assert (closed_ty 0 (length env) (open (varF (length G)) T2)). { *)
      (*   eapply vtp_closed. *)
        (* XXX Can't work unless we know that the body terminates. We need to change
        defs and prove *etp_closed* or expr_sem_closed. That wasn't a problem
        for strong normalization because there we _do_ know the body terminates. *)
      (* } *)
    +
    intros.
    (* assert (exists v : vl, optV = Some v /\ vtp T2 (k0 - j) v (vx :: env)) by eauto. *)
    assert (exists v, optV = Some v /\ vtp (open (varF (length G)) T2) (k0 - j) v (vx :: env)) by eauto.
    assert (length env = length G) as -> by eauto using wf_length.
    solve [ev; eexists; split_conj; eauto].
Admitted.

Lemma teval_var: forall env x,
  exists optV, tevalSnOpt env (tvar x) optV 0 /\ indexr x env = optV.
Proof.
  unfold tevalSnOpt, tevalSnmOpt;
    eexists;
    split_conj; [exists 1 (* For nm *); intros; step_eval|idtac]; eauto.
Qed.
Hint Resolve teval_var.

Lemma etp_var: forall env x T n,
  etp T n (tvar x) env ->
  exists v,
    indexr x env = Some v /\
    vtp T n v env.
Proof.
  unfold etp, expr_sem.
  intros * Hetp.
  simpl in *.
  (* Tactic *)
  assert (0 <= n) by auto.
  assert (exists optV, tevalSnOpt env (tvar x) optV 0 /\ indexr x env = optV) by auto.
    (* as (optV & Heval & Hx) by auto. *)
  (* lets ? : Hetp optV Heval ___; auto. *)
  firstorder (ev; subst; eauto).
  (* ev; subst; eauto. *)
  (* lets (v & -> & Hvtp) : Hetp optV Heval ___; auto. *)
  (* firstorder eauto. *)
  (* subst. *)
  (* eexists; *)
  (* firstorder eauto. *)
  (* lets (v & -> & Hvtp) : Hetp optV Heval ___; auto. *)
  (* eexists; split_conj; eauto. *)
Qed.

(* Better version of mem_stp. *)
Lemma mem_stp_etp : forall env x L U n vx,
    etp (TMem L U) (S n) (tvar x) env ->
    vtp L n vx env ->
    vtp (TSel (varF x)) (S n) vx env.
Proof.
  intros * H ?;
    apply etp_var in H;
    (* Either: *)
    ev; eauto using mem_stp.
    (* Or: *)
    (* firstorder (eauto using mem_stp). *)
  (* Apparently firstorder can't destruct existentials? *)
Qed.

Lemma stp_mem_etp : forall env x L U n vx,
    etp (TMem L U) (S n) (tvar x) env ->
    vtp (TSel (varF x)) (S n) vx env ->
    vtp U n vx env.
Proof.
  intros * H ?;
    apply etp_var in H;
    (* Either: *)
    ev; eauto using stp_mem.
Qed.

Lemma stp_refl : forall G T,
    sem_subtype G T T.
Proof. intros; eauto. Qed.

Lemma stp_trans : forall G T1 T2 T3,
    sem_subtype G T1 T2 ->
    sem_subtype G T2 T3 ->
    sem_subtype G T1 T3.
Proof. intros; auto. Qed.

Lemma t_sub: forall G T1 T2 e,
    sem_subtype G T1 T2 ->
    sem_type G T1 e ->
    sem_type G T2 e.
Proof. intros; eauto. Qed.

(* Variant of vtp_extend. *)
Lemma stp_weak : forall G T1 T2 T,
    sem_subtype G T1 T2 ->
    sem_subtype (T :: G) T1 T2.
Proof.
  unfold sem_subtype.
  intros * Hsub * Henv * HT1.
  dependent destruction Henv.
  (* etp, expr_sem. *)
  eapply Hsub; eauto.
Admitted.
(*   (* eexists; ev. *) *)
(*   eauto. *)
(*   eauto using vtp_extend. *)
(*   indexr_extend. *)
(* Qed. *)

Lemma t_weak : forall G T1 T2 T,
    sem_type G T1 T2 ->
    sem_type (T :: G) T1 T2.
Proof.
  unfold sem_type.
  intros ? * Htp * Henv.
  eapply Htp.
Admitted.
