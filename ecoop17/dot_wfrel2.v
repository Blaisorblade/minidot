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
  unfold interpTAll, interpTSel, interpTMem, interpTSel0, interpTAnd in *.
Ltac vtp_simpl_unfold := repeat simpl_vtp; vtp_unfold_pieces.

Lemma vtp_mon: forall env T n v, vtp T n v env -> forall m, m < n -> vtp T m v env.
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

  - apply H1; assumption || omega.
Qed.

Lemma and_stp1 : forall env T1 T2 n v, vtp (TAnd T1 T2) n v env -> vtp T1 n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

Lemma and_stp2 : forall env T1 T2 n v, vtp (TAnd T1 T2) n v env -> vtp T2 n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

Lemma stp_and : forall env T1 T2 n v, vtp T1 n v env -> vtp T2 n v env -> vtp (TAnd T1 T2) n v env.
Proof. intros; vtp_simpl_unfold; tauto. Qed.

(* XXX Beware: here TAll is non-expansive rather than contractive, I guess by mistake. *)

(* Next step: define valid environments, then semantic typing! *)

(* XXX Too hard to state, because we didn't! *)
Lemma t_forall_i : forall env T1 T2 n t,
    closed_ty 0 (length env) T1 ->
    closed_ty 1 (length env) T2 ->
    (forall v, vtp T1 n v'
        expr_sem (fun n' (p: n' <= n) v' => vtp T2 n v') n (le_refl n) (v :: env) t (v :: env)) ->
    vtp (TAll T1 T2) n (vabs env T1 t) env.
Proof.
  intros.
  vtp_simpl_unfold. repeat split_conj; try assumption.
