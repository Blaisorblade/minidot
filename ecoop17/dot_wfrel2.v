Require Import tactics.
Require Import dot_base.
Require Import dot_eval.
Require Import dot_wfrel.

Lemma vtp_unfold : forall T n v env,
    vtp T n v env =
    match T with
    | TAll T1 T2 =>
      closed_ty 0 (length env) T1 /\ closed_ty 1 (length env) T2 /\
      interpTAll n
                 (open (varF (length env)) T2)
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
    | TSel x U =>
      interpTSel n x
                 (fun T j p => vtp T j)
                 (fun n p => vtp U n)
                 n (le_n _) v env
    | TAnd T1 T2 =>
      interpTAnd n
                 (fun n p => vtp T1 n)
                 (fun n p => vtp T2 n)
                 n (le_n _) v env
    | TOr T1 T2 =>
      closed_ty 0 (length env) T1 /\ closed_ty 0 (length env) T2 /\
      interpTOr n
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

Lemma vtp_unfold_underbinders :
    vtp =
    fun T n v env =>
    match T with
    | TAll T1 T2 =>
      closed_ty 0 (length env) T1 /\ closed_ty 1 (length env) T2 /\
      interpTAll n
                 (open (varF (length env)) T2)
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
    | TSel x U =>
      interpTSel n x
                 (fun T j p => vtp T j)
                 (fun n p => vtp U n)
                 n (le_n _) v env
    | TAnd T1 T2 =>
      interpTAnd n
                 (fun n p => vtp T1 n)
                 (fun n p => vtp T2 n)
                 n (le_n _) v env
    | TOr T1 T2 =>
      closed_ty 0 (length env) T1 /\ closed_ty 0 (length env) T2 /\
      interpTOr n
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
  repeat (apply functional_extensionality_dep; intro);
    rewrite vtp_unfold;
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
Ltac simpl_vtp_all :=
  match goal with
  | H : context [ vtp ?T _ _ _ ] |- _ =>
    tryif is_var T then fail else rewrite vtp_unfold_underbinders in H
  | |- context [ vtp ?T _ _ _ ] =>
    tryif is_var T then fail else rewrite vtp_unfold_underbinders
  end.

(* Hint Rewrite vtp_unfold_underbinders. *)

Hint Unfold interpTAll interpTSel interpTMem interpTSel0 interpTAnd interpTOr interpTLater.
Ltac vtp_unfold_pieces :=
  unfold interpTAll, interpTSel, interpTMem, interpTSel0, interpTAnd, interpTOr, interpTLater, expr_sem in *.
Ltac vtp_simpl_unfold := repeat simpl_vtp; vtp_unfold_pieces.
Ltac vtp_simpl_unfold_deep := repeat (simpl_vtp_all; vtp_unfold_pieces).
(* Ltac vtp_simpl_unfold := repeat simpl_vtp; vtp_unfold_pieces. *)


Example ex3: forall env T n, vtp (TMem TBot TTop) n (vty env T) [].
Proof.
  intros; vtp_simpl_unfold_deep; split_and; iauto.
Qed.

(* Infrastructure for well-founded induction for properties of vtp. *)
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

Ltac vtp_induction T k :=
  apply ind_args with (T := T) (n := k);
  clear T k.

Hint Unfold wf.
Lemma vtp_closed: forall T k v env,
    vtp T k v env -> wf env T.
Proof.
  unfold wf; induction T; intros; destruct v; vtp_simpl_unfold; ev; try eauto;
    (* Either case_match or better_case_match works*)
    repeat better_case_match; ev; eauto 6;
      contradiction.
Qed.
Hint Resolve vtp_closed.

Lemma wf_to_closed_ty: forall {A} (env: list A) T, wf env T -> closed_ty 0 (length env) T. Proof. eauto. Qed.
Hint Resolve wf_to_closed_ty.

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
      (* Either case_match or better_case_match works*)
      repeat better_case_match.
  (* We could finish the proof by a single line combining the next tactics. *)
  (* But let's look how our cases (24 right now!) are solved. *)
  (* Most cases (12) follow trivially, or by using the induction hypothesis. *)
  all: trivial.
  (* Many other cases (6) have hypothesis for all j < n and have a conclusion for
     all j < m (with m < n). So we assert that j < n, and then Coq can finish
     the proof automatically. *)

  all: intros; try assert (Hjn: j < n) by omega; try assert (j <= n) by omega; auto 2.

  Hint Constructors or.
  Ltac case_or_vtp :=
    match goal with
    | [ H : vtp _ _ _ _ \/ vtp _ _ _ _ |- _ ] => destruct H
    end.
  Ltac mon_induct_step Hind n := (try (apply Hind with (n' := n); try smaller_types; assumption)).
  (* A couple (6) follow just by using induction on smaller types. *)
  all: mon_induct_step Hind n.

  (* For TOr, we must also case_split on the disjunction in the hypothesis,
     and pick the right branch to prove in the conclusion. *)
  all: try case_or_vtp;
    intuition (mon_induct_step Hind n).

  (* handle TLater, for when m is less than 0 *)
  all: try omega.
  (* If m = 0 we must show that the produced type is closed. *)
  all: eauto.

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

Hint Extern 5 (vtp _ _ _ _) => try_once vtp_mon.

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
Hint Extern 5 (R_env _ _ _) => try_once R_env_mon.

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
  @expr_sem k T (fun k _ => vtp T k) k _ env e env.

Lemma etp_closed: forall T k v env,
    etp T k v env -> wf env T.
Proof.
  unfold etp, expr_sem; tauto.
Qed.
Hint Resolve etp_closed.

(* Semantic typing *)
Definition sem_type (G : tenv) (T : ty) (e: tm) :=
  wf G T /\
  forall k env,
    R_env k env G ->
    etp T k e env.

Definition sem_vl_subtype (G : tenv) (T1 T2: ty) :=
  wf G T1 /\
  wf G T2 /\
  forall k env,
    R_env k env G ->
    forall v, vtp T1 k v env -> vtp T2 k v env.

Definition sem_subtype (G : tenv) (T1 T2: ty) :=
  wf G T1 /\
  wf G T2 /\
  sem_vl_subtype G T1 T2 /\
  forall k env,
    R_env k env G ->
    forall e, etp T1 k e env -> etp T2 k e env.

Hint Unfold wf sem_type sem_subtype sem_vl_subtype etp.

Lemma sem_type_closed : forall G T e,
    sem_type G T e -> wf G T.
Proof. unfold sem_type; intros; tauto. Qed.

Lemma sem_subtype_closed1 : forall G T1 T2,
    sem_subtype G T1 T2 -> wf G T1.
Proof. unfold sem_subtype; intros; tauto. Qed.

Lemma sem_subtype_closed2 : forall G T1 T2,
    sem_subtype G T1 T2 -> wf G T2.
Proof. unfold sem_subtype; intros; tauto. Qed.

Lemma sem_vl_subtype_closed1 : forall G T1 T2,
    sem_vl_subtype G T1 T2 -> wf G T1.
Proof. unfold sem_vl_subtype; intros; tauto. Qed.

Lemma sem_vl_subtype_closed2 : forall G T1 T2,
    sem_vl_subtype G T1 T2 -> wf G T2.
Proof. unfold sem_vl_subtype; intros; tauto. Qed.

Hint Resolve sem_type_closed
     sem_subtype_closed1
     sem_subtype_closed2
     sem_vl_subtype_closed1
     sem_vl_subtype_closed2.

Hint Resolve wf_length.
Lemma vl_subtype_to_subtype : forall G T1 T2,
    sem_vl_subtype G T1 T2 -> sem_subtype G T1 T2.
Proof.
  unfold sem_subtype, sem_vl_subtype, etp, wf; vtp_unfold_pieces;
    intros; intuition idtac;
      replace (length G) with (length env) in * by eauto;
      firstorder eauto.
Qed.
Hint Resolve vl_subtype_to_subtype.

Lemma subtype_to_vl_subtype : forall G T1 T2,
    sem_subtype G T1 T2 -> sem_vl_subtype G T1 T2.
Proof. unfold sem_subtype; tauto. Qed.
Hint Resolve subtype_to_vl_subtype.

Require Import PropExtensionality.
Lemma vl_sub_equiv: sem_subtype = sem_vl_subtype.
Proof.
  repeat (apply functional_extensionality; intro); apply propositional_extensionality;
    split; eauto.
Qed.
Hint Rewrite vl_sub_equiv.

Lemma and_stp1 : forall env T1 T2 n v, vtp (TAnd T1 T2) n v env -> vtp T1 n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

Lemma sem_and_stp1 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_subtype G (TAnd T1 T2) T1.
Proof. eauto 8 using and_stp1. Qed.

Lemma and_stp2 : forall env T1 T2 n v, vtp (TAnd T1 T2) n v env -> vtp T2 n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

Lemma sem_and_stp2 : forall G T1 T2, wf G T1 -> wf G T2 -> sem_subtype G (TAnd T1 T2) T2.
Proof. eauto 8 using and_stp2. Qed.

Lemma stp_and' : forall env T1 T2 n v, vtp T1 n v env -> vtp T2 n v env -> vtp (TAnd T1 T2) n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

Lemma stp_and : forall env S T1 T2 n v,
    (vtp S n v env -> vtp T1 n v env) ->
    (vtp S n v env -> vtp T2 n v env) ->
    vtp S n v env -> vtp (TAnd T1 T2) n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

Lemma mem_stp : forall env x L U n v vx,
    vtp (TMem L U) n v env ->
    vtp L n vx env ->
    indexr x env = Some v ->
    vtp (TSel (varF x) U) n vx env.
Proof.
  (* This needs better_case_match (or discriminate later) *)
  intros; vtp_simpl_unfold; repeat better_case_match; ev; intros; injectHyps; try contradiction; firstorder eauto.
Qed.

Lemma stp_mem : forall env x L U n v vx,
    vtp (TMem L U) n v env ->
    vtp (TSel (varF x) U) n vx env ->
    indexr x env = Some v ->
    vtp U n vx env.
Proof.
  (* Either case_match or better_case_match works*)
  intros; vtp_simpl_unfold; repeat case_match; ev; intros; injectHyps; try contradiction; eauto.
Qed.

(* Once we define the OFE of semantic types, we can alternatively define a
language of term realizers that mention no types, not even in ttyp, just like in
Ahmed's typeless System F. *)

(* We want to relate etp and vtp. *)
Lemma etp_vtp_j: forall e v k j nm T env,
    tevalSnm env e v j nm -> etp T k e env -> j <= k -> vtp T (k - j) v env.
Proof.
  intros;
    assert (exists v0, Some v = Some v0 /\ vtp T (k - j) v0 env) by
      (unfold etp, expr_sem in *; iauto);
  ev; injectHyps; eauto.
Qed.
Hint Extern 5 (vtp _ _ _ _) => try_once etp_vtp_j.

Lemma etp_vtp: forall e v k nm T env,
    tevalSnm env e v 0 nm -> etp T k e env -> vtp T k v env.
Proof. eauto. Qed.
Hint Extern 5 (vtp _ _ _ _) => try_once etp_vtp.

Lemma vtp_etp_j: forall e v T env k j nm,
    vtp T (k - j) v env ->
    tevalSnm env e v j nm ->
    j <= k ->
    etp T k e env.
Proof.
  intros * Hvtp Heval Hkj.
  unfold etp; vtp_unfold_pieces; unfold tevalSnOpt, tevalSnm in *.
  split_conj; eauto.
  intros * [nm' Heval'] Hkj0.
  assert (optV = Some v /\ j = j0) as [-> ->] by (
    pose (N := nm + nm' + 1);
    assert (tevalS e N env = Some (Some v, j)) by (subst N; auto);
    assert (tevalS e N env = Some (optV, j0)) by (subst N; auto);
    split_conj; congruence);
  eexists; split_conj; eauto.
Qed.
Hint Extern 5 (etp _ _ _ _) => try_once vtp_etp_j.

Lemma vtp_etp:
  forall e v T env k nm,
    vtp T k v env ->
    tevalSnm env e v 0 nm ->
    etp T k e env.
Proof. eauto. Qed.
Hint Extern 5 (etp _ _ _ _) => try_once vtp_etp.

Lemma sem_stp_and : forall G S T1 T2,
    sem_subtype G S T1 ->
    sem_subtype G S T2 ->
    sem_subtype G S (TAnd T1 T2).
Proof.
  rewrite vl_sub_equiv; unfold sem_vl_subtype; intuition eauto using stp_and.
Qed.

Ltac invert_closed :=
  match goal with
  | H : closed_ty _ _ ?T  |- _ =>
    tryif is_var T then fail else inverts H
  end.
Ltac invert_closed_var :=
  match goal with
  | H : closed_var _ _ _ |- _ => inverts H
  end.

Lemma closed_var_extend: forall v i j,
    closed_var i j v -> closed_var i (S j) v.
Proof.
  destruct v; intros; invert_closed_var; eauto.
Qed.
Hint Resolve closed_var_extend.

Lemma closed_ty_extend: forall T i j,
    closed_ty i j T -> closed_ty i (S j) T.
Proof.
  induction T; intros; invert_closed; eauto.
Qed.
Hint Resolve closed_ty_extend.

(* Probably false as given, where does it come from??? *)
(* Lemma closed_open: forall T i j k, *)
(*     (* closed_ty i j (TSel u) -> *) *)
(*     closed_ty i (S j) (open_rec k (varF j) T) -> *)
(*     (* i >= k -> *) *)
(*     closed_ty (S i) j T. *)
(* Proof. *)
(* Admitted. *)
(* (*   (* unfold open_rec; fold open_rec. *) *) *)
(* (*   induction T; intros; eauto; inversion H; subst; *) *)
(* (*     simpl in *; *) *)
(* (*     constructor; eauto. *) *)
(* (*   destruct v. simpl in *. *) *)
(* (*     try better_case_match; try beq_nat; invert_closed_var; auto. *) *)
(* (*   inverts H. *) *)
(* (* Qed. *) *)

(*   (* - cinject H0. *) *)
(*   (*   inverse H. *) *)
(*   (*   inverse H3. *) *)
(*   (*   constructor. *) *)
(*   (*   admit. (* False! *) *) *)
(*   (* - beq_nat. *) *)
(*   (*   cinject H0. clear H. inverse H3. *) *)
(*   (*   + constructor. *) *)
(*   (*     admit. (* False! *) *) *)
(*   (*   + constructor. *) *)
(*   (*     admit. (* False! *) *) *)
(*   (* -  beq_nat. *) *)
(*   (*    cinject H0. *) *)

Definition valTypeObligationsSSReflection_marker := 0.
Hint Extern 5 (val_type_termRel _ _) => try_once_tac valTypeObligationsSSReflection_marker (solve [valTypeObligationsSSReflection]).

Lemma vtp_extend : forall vx v k env T,
  vtp T k v env ->
  vtp T k v (vx::env).
Proof.
Admitted.
  (* induction T; vtp_simpl_unfold; unfold wf; simpl; intuition eauto. *)
  (* - admit. *)
  (* - admit. *)
  (* - better_case_match; intuition eauto. *)
  (*   + admit. *)
  (*   +  *)
Hint Immediate vtp_extend.

Lemma vtp_etp_rev:
  forall e v T env k nm,
    tevalSnm env e v 0 nm ->
    vtp T k v env ->
    etp T k e env.
  eauto. Qed.

(* Awkward to state with vtp? *)
Lemma vtp_tbind_i: forall env v T n,
    closed_ty 0 (length env) (TBind T) ->
    (* Arguably shouldn't be needed, but I'll need some tricky binding lemma otherwise! *)
    vtp (open (varF (length env)) T) n v (v :: env) ->
    vtp (TBind T) n v env.
Proof.
  intros * Hc Hvtp; inverse Hc; rewrite vtp_unfold; eauto.
Qed.

Lemma t_forall_i: forall G T1 T2 t,
  (* sem_type (T1 :: G) T2 t -> *)
  wf G T1 ->
  closed_ty 1 (length G) T2 ->
  sem_type (T1 :: G) (open (varF (length G)) T2) t ->
  sem_type G (TAll T1 T2) (tabs T2 t).
Proof.
  unfold sem_type, wf; simpl; intros; intuition eauto.
  (* XXX needed: Lemma for syntactic values. *)
  (* Also needed: a way to swap goals that actually works! *)
  eapply vtp_etp_rev with (nm := 0).
  - unfold tevalSnm, tevalSnmOpt; intros; step_eval; trivial.
  - replace (length G) with (length env) in * by eauto.
    unfold etp in *; vtp_simpl_unfold;
      split_conj; eauto.
Qed.

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
    etp (TMem L U) n (tvar x) env ->
    vtp L n vx env ->
    vtp (TSel (varF x) U) n vx env.
Proof.
  intros * H ?;
    apply etp_var in H;
    (* Either: *)
    ev; eauto using mem_stp.
    (* Or: *)
    (* firstorder (eauto using mem_stp). *)
  (* Apparently firstorder can't destruct existentials? *)
Qed.

(* Lemma sem_type_tvar_closed: forall G T x, sem_type G T (tvar x) -> length G > x. *)
(* Proof. *)
(* Admitted. *)

(* Hint Resolve sem_type_tvar_closed. *)

Lemma mem_stp_sub : forall G L U x,
    sem_type G (TMem L U) (tvar x) ->
    closed_var 0 (length G) (varF x) ->
    sem_subtype G L (TSel (varF x) U).
Proof.
  intros; eapply vl_subtype_to_subtype;
    unfold sem_type, sem_vl_subtype, wf in *; ev; invert_closed;
      intuition idtac; eauto using mem_stp_etp.
Qed.

(* Let's pretend we have regularity for sem_vl_subtype. I should of course just add the needed assumptions, but don't want to go over all the existing proofs. *)
(* Lemma sem_vl_subtype_closed: forall G T1 T, *)
(*     sem_vl_subtype G T1 T2 -> *)
(*     closed_ty 0 (length G) T1 /\ *)
(*     closed_ty 0 (length G) T2. *)
(* Proof. unfold sem_vl_subtype, wf; intuition eauto. Qed. *)
(* Hint Resolve sem_vl_subtype_closed. *)

Lemma mem_mem_stp: forall G L1 L2 U1 U2,
    sem_subtype G L2 L1 ->
    sem_subtype G U1 U2 ->
    sem_subtype G (TMem L1 U1) (TMem L2 U2).
Proof.
  rewrite vl_sub_equiv; unfold sem_vl_subtype; intros; intuition idtac; intros; eauto; vtp_simpl_unfold.
  replace (length env) with (length G) in * by
      (rewrite wf_length with (ts := G) (k := k); eauto);
    intuition idtac;
    better_case_match; try contradiction; subst;
      firstorder eauto 6.
Qed.

Lemma stp_mem_etp : forall env x L U n vx,
    etp (TMem L U) n (tvar x) env ->
    vtp (TSel (varF x) U) n vx env ->
    vtp U n vx env.
Proof.
  intros * H ?;
    apply etp_var in H;
    (* Either: *)
    ev; eauto using stp_mem.
Qed.

Lemma stp_mem_sub : forall G L U x,
    sem_type G (TMem L U) (tvar x) ->
    closed_var 0 (length G) (varF x) ->
    sem_subtype G (TSel (varF x) U) U.
Proof.
  intros; eapply vl_subtype_to_subtype;
    unfold sem_type, sem_vl_subtype, wf in *; ev; invert_closed;
      intuition idtac; eauto using stp_mem_etp.
Qed.

Lemma stp_refl : forall G T,
    wf G T ->
    sem_subtype G T T.
Proof. intros; eauto. Qed.

Lemma stp_trans : forall G T1 T2 T3,
    sem_subtype G T1 T2 ->
    sem_subtype G T2 T3 ->
    sem_subtype G T1 T3.
Proof.
  rewrite vl_sub_equiv; unfold sem_vl_subtype; intuition auto.
Qed.

Lemma t_sub: forall G T1 T2 e,
    sem_subtype G T1 T2 ->
    sem_type G T1 e ->
    sem_type G T2 e.
Proof. unfold sem_subtype, sem_type; intuition auto. Qed.

(* Oh, this isn't quite vtp_tbind_i. *)
(* Lemma t_bind_i: forall G T t, *)
(*   sem_type (TLater T :: G) (open (varF (length G)) T) t -> *)
(*   sem_type G (TBind T) t. *)
(* Proof. *)
(*   unfold sem_type, etp, expr_sem. *)
(*   intros *;  *)
(*   intros * Hvtp * Henv * Heval Hjk *. *)
(*   induction k. *)
(*   - assert (j = 0) as -> by omega. *)
(*     assert (v: vl) by admit. *)

(*     assert (R_env 0 (v :: env) (TLater T :: G)). { *)
(*       constructor. *)
(*       - eauto. *)
(*       - vtp_simpl_unfold. *)
(*         assert (closed_ty 0 (length (v :: env)) T) by admit; eauto. *)
(*     } *)
(*     lets (v' & -> & Hvtp') : Hvtp 0 (v :: env) optV ___; eauto. { *)
(*       assert (tevalSnOpt (v :: env) t optV 0) by admit; eauto. *)
(*     } *)
(*     simpl in *. *)
(*     ev; subst. *)
(*     assert (closed_ty 0 (length env) (TBind T)). { *)
(*       constructor. *)
(*       eapply vtp_closed in Hvtp'. *)
(*       assert (closed_ty 1 (length env) T) by admit; eauto. *)
(*     } *)
(*     eexists; split_conj; eauto. *)
(*     eapply vtp_tbind_i; eauto. *)
(*     (* Uh, this almost works but not quite, but wouldn't be a problem in Iris. *)
(*        We must show t's result is v' and is well-typed in environment (v' :: env). *)
(*        We know that t's result is v' and is well-typed in environment (v :: env). *)

(*        In the Iris model, the difference wouldn't matter because we can only see *)
(*        the truncation of v and x, which are considered equal, but this isn't *)
(*        reflected by the current definitions I'm using --- I don't even have *)
(*        the "thunk" constructors `next` for values of TLater. *)
(*      *) *)
(*   assert (vtp (open (varF (length G)) T) 0 v' (v :: env)) by assumption. *)
(*   assert (vtp (open (varF (length env)) T) 0 v' (v' :: env)) by admit; eauto. *)

(*   (* Induction step. *) *)
(*   - *)
(*     (* Is j = S k?*) *)
(*     inverse Hjk. *)
(*     + clear IHk. (* Unapplicable *) *)
(*       assert (Henv': R_env k env G) by eauto. *)
(*       simpl. replace (k - k) with 0 by omega. *)
(*       eexists. *)
(*       vtp_simpl_unfold. *)
(*       split_conj. *)
(*       vtp_unfold_pieces. *)

(* Admitted. *)

(* Variant of vtp_extend. *)
Lemma stp_weak : forall G T1 T2 T,
    sem_subtype G T1 T2 ->
    sem_subtype (T :: G) T1 T2.
Proof.
  unfold sem_subtype, sem_vl_subtype, wf; simpl; intros * (? & ? & Hvlsub & Hsub); split_conj; eauto; intros * Henv * HT1; dependent destruction Henv.
  (* eapply Hvlsub; eauto. *)
  (* eapply Hsub; eauto. *)
Admitted.
(*   (* eexists; ev. *) *)
(*   eauto. *)
(*   eauto using vtp_extend. *)
(*   indexr_extend. *)
(* Qed. *)

Lemma t_weak : forall G T T1 e,
    sem_type G T e ->
    sem_type (T1 :: G) T e.
Proof.
  unfold sem_type.
  (* intros ? * Htp * Henv. *)
  (* eapply Htp. *)
Admitted.

Definition realizable G T :=
  forall k env, R_env k env G ->
    exists v, vtp T k v env.
Hint Unfold realizable.

(* XXX Not sure if what I want, and split this in a lemma for vtp and a high-level one as before. *)
Lemma realizable_int_wrong : forall G L1 L2 U1 U2,
    realizable G (TMem L1 U1) ->
    realizable G (TMem L2 U2) ->
    realizable G (TAnd L1 L2) ->
    realizable G (TMem (TAnd L1 L2) (TAnd U1 U2)).
Proof.
  unfold realizable; rewrite vtp_unfold_underbinders in *; vtp_unfold_pieces.

  intros * Hm1 Hm2 HL * Henv; specialize (Hm1 k env Henv); specialize (Hm2 k env Henv); specialize (HL k env Henv).

  ev; repeat case_match; iauto; subst.
  (* assert (exists v, forall j, j < k -> vtp (TAnd L1 L2) j v env) as [v0 Hv] by *)
  (*   (eexists; intros; vtp_simpl_unfold; firstorder eauto). *)

  eexists (vty env (TAnd L1 L2)); vtp_simpl_unfold_deep; firstorder eauto.
Qed.

(*
Counterexample:
L1 <: U1 <: L2 <: U2, where all inclusions are strict.
*)
Lemma realizable_int_vtp: forall L1 L2 U1 U2 v1 v2 vA k env,
    vtp (TMem L1 U1) k v1 env ->
    vtp (TMem L2 U2) k v2 env ->
    vtp (TAnd L1 L2) k vA env ->
    (forall v j, j < k -> vtp (TOr L1 L2) j v env -> vtp (TAnd U1 U2) j v env) ->
    exists v, vtp (TAnd (TMem L1 U1) (TMem L2 U2)) k v env.
Proof.
  intros; vtp_simpl_unfold_deep; ev.
  repeat case_match; iauto; subst.
  exists (vty env (TAnd U1 U2)).
  intuition idtac; repeat vtp_simpl_unfold; firstorder idtac.
Qed.

Lemma realizable_int : forall G L1 L2 U1 U2,
    realizable G (TMem L1 U1) ->
    realizable G (TMem L2 U2) ->
    realizable G (TAnd L1 L2) ->
    sem_vl_subtype G (TOr L1 L2) (TAnd U1 U2) ->
    realizable G (TAnd (TMem L1 U1) (TMem L2 U2)).
Proof.
  unfold realizable, sem_subtype; intros * Hm1 Hm2 HL Hsub * Henv;
    specialize (Hm1 k env Henv); specialize (Hm2 k env Henv); specialize (HL k env Henv);
      (* ev; eauto using realizable_int_vtp. (* Or *) *)
      firstorder eauto using realizable_int_vtp.
Qed.

(* Still wrong. We want the intersection of the inhabitant of (TMem L1 U1) and
   (TMem L2 U2), which is TAnd (TSel x) (TSel y) for x and y pointing at those
   inhabitants. That way, we'd account for the case where x and y have smaller
   bounds, but without needing to explicitly incorporate narrowing.
 *)

(* What we'd want is closer to: *)
(* Lemma realizable_int_vtp_real: forall L1 L2 U1 U2 v1 v2 vA k env, *)
(*     vtp (TMem L1 U1) k v1 env -> *)
(*     vtp (TMem L2 U2) k v2 env -> *)
(*     vtp (TAnd L1 L2) k vA env -> *)
(*     (forall v j, j < k -> vtp (TOr L1 L2) j v env -> vtp (TAnd U1 U2) j v env) -> *)
(*     exists v, vtp (TAnd (TSel v1) (TSel v2)) k v env. *)
