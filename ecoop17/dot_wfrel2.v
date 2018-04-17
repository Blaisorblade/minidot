Require Import tactics.
Require Import dot_wfrel.
Require Import dot_base.

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
    | _ =>
      False
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

Hint Unfold interpTAll interpTSel interpTMem interpTSel0 interpTAnd.
Ltac vtp_unfold_pieces :=
  unfold interpTAll, interpTSel, interpTMem, interpTSel0, interpTAnd, expr_sem in *.
Ltac vtp_simpl_unfold := repeat simpl_vtp; vtp_unfold_pieces.

(* Hint Extern 1 (tsize_flat (open_rec _ _ _)) => autorewrite with core. *)
Ltac ineq_solver := autorewrite with core; simpl in *; omega.
Hint Unfold gt. (* Using gt or lt other shouldn't affect proof search! *)
Hint Unfold ge. (* Ditto *)
Hint Extern 5 (_ > _) => ineq_solver.
Hint Extern 5 (_ >= _) => ineq_solver.
Hint Extern 5 (_ < _) => ineq_solver.
Hint Extern 5 (_ <= _) => ineq_solver.

Lemma vtp_mon: forall T env v m n,
    vtp T n v env ->
    m <= n ->
    vtp T m v env.
Proof.
  intros *.
  revert env v.

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

Program Definition etp T k env1 e env :=
  @expr_sem k (fun k _ => vtp T k) k _ env1 e env.

(* Semantic typing *)
Definition sem_type (G : tenv) (T : ty) (e: tm) :=
  forall k env,
    R_env k env G ->
    etp T k env e env.

Definition sem_subtype (G : tenv) (T1 T2: ty) :=
  forall k env,
    R_env k env G ->
    forall e, etp T1 k env e env -> etp T2 k env e env.

Definition sem_vl_subtype (G : tenv) (T1 T2: ty) :=
  forall k env,
    R_env k env G ->
    forall e, vtp T1 k e env -> vtp T2 k e env.

Hint Unfold sem_subtype sem_vl_subtype etp.

Lemma vl_subtype_to_subtype : forall G T1 T2,
    sem_vl_subtype G T1 T2 -> sem_subtype G T1 T2.
Proof.
  unfold sem_subtype, sem_vl_subtype, etp.
  intros * ? * ? * HeT1.
  vtp_unfold_pieces.
  intros * Hjk Heval.
  specialize (HeT1 optV j Hjk Heval).
  ev.
  eexists; split_conj; eauto.
Qed.
Hint Resolve vl_subtype_to_subtype.

Lemma and_stp1 : forall env T1 T2 n v, vtp (TAnd T1 T2) n v env -> vtp T1 n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

Lemma and_stp2 : forall env T1 T2 n v, vtp (TAnd T1 T2) n v env -> vtp T2 n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

Lemma stp_and : forall env T1 T2 n v, vtp T1 n v env -> vtp T2 n v env -> vtp (TAnd T1 T2) n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

Lemma vtp_closed: forall T k v env,
    vtp T k v env -> closed_ty 0 (length env) T.
Proof.
  induction T; intros; destruct v; rewrite vtp_unfold in *; vtp_unfold_pieces; ev; try eauto;
  repeat case_match; repeat constructor; try contradiction; eauto.
Qed.
Hint Resolve vtp_closed.

(* (* XXX Too hard to state, because we didn't define semantic typing yet! *) *)
(* Lemma t_forall_i : forall env T1 T2 n t, *)
(*     closed_ty 0 (length env) T1 -> *)
(*     closed_ty 1 (length env) T2 -> *)
(*     (forall v, vtp T1 n v env -> *)
(*         expr_sem (fun n' (p: n' <= n) v' => vtp T2 n v') n (le_refl n) (v :: env) t (v :: env)) -> *)
(*     vtp (TAll T1 T2) n (vabs env T1 t) env. *)
(* Proof. *)
(*   intros. *)
(*   vtp_simpl_unfold. repeat split_conj; try assumption. *)

(*   Abort. *)
(*   (* XXX Should prove closure assumptions from the hypothesis? *) *)
