Require Import Omega.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Equations.Equations.

Require Import dot_storeless_tidy.
Require Import tactics.
(* Require Import dot_monads. *)

(*******************)
(* Define language infrastructure. *)

(*******************)
(* Renames for adaption. *)

Notation tsize_flat := tsize.

Lemma open_preserves_size': forall T v j,
    tsize_flat (open j v T) = tsize_flat T.
Proof. intros; rewrite <- open_preserves_size; easy. Qed.
Definition vl := tm.

Definition closed_ty i j T := closed j i T.

(*******************)
(* Small-step semantics *)
Inductive steps t0 : tm -> nat -> Prop :=
| Step0 : steps t0 t0 0
| StepS : forall t1 t2 i, step t0 t1 -> steps t1 t2 i -> steps t0 t2 (S i).

Definition irred t0 := not (exists t1, step t0 t1).

(* Definition env_prop := list vl ->  Prop. *)
(* Hint Unfold env_prop. *)

Definition vl_prop := vl -> Prop.
Hint Unfold vl_prop.

Definition pretype_dom n :=
  forall (n0: nat) (H: n0 <= n), vl_prop.
Hint Unfold pretype_dom.

Hint Constructors lexprod.

(*******************)
(* Infrastructure for well-founded induction for properties of vtp. *)
Definition argMeasure (p: ty * nat) := let '(T, n) := p in (existT (fun _ => nat) n (tsize_flat T)).
Definition val_type_termRel := MR (lexprod lt (fun _ => lt)) (fun p => let '(T, n) := p in (existT (fun _ => nat) n (tsize_flat T))).

(*******************)
(* Tactics. *)
(* Show that different branches are disjoint. *)
Ltac discriminatePlus :=
  idtac.
  (* (* repeat split; intros; let Habs := fresh "Habs" in intro Habs; destruct Habs; discriminate. *) *)
  (* repeat split_conj; intros; *)
  (* (let Habs := fresh "Habs" in *)
  (* try (intro Habs; destruct Habs) + idtac); *)
  (* discriminate. *)

(* Prove some inequalities needed below, without producing big proof terms like omega does. Probably not worth it. *)
Ltac simple_ineq :=
  (* simpl; omega. *)
  simpl; auto using le_n_S, le_plus_l, le_plus_r; abstract omega.
  (* If this tactic fails, add back omega at the end. *)

(* These three lemmas take care of the various forms of proof obligations that arise from val_type. *)
Lemma termRelShow: forall j n T1 T2,
  j <= n -> tsize_flat T2 < tsize_flat T1 ->
  val_type_termRel (T2, j) (T1, n).
Proof.
  intros * Hj Ht; unfold val_type_termRel, MR, argMeasure;
  (* If we only know that Hj: j <= n, we must case-split on it, and use
     smaller_types when j = n and smaller_n when j < n. *)
    destruct Hj; try assert (j < S m) by simple_ineq; auto.
Qed.

Hint Extern 5 (_ < tsize_flat _) =>
  rewrite open_preserves_size';
  simple_ineq.

Lemma termRelShowOpen: forall j n x T1 T2,
  j <= n -> tsize_flat T2 < tsize_flat T1 ->
  val_type_termRel (open 0 x T2, j) (T1, n).
Proof.
  intros * Hj Ht; unfold val_type_termRel, MR, argMeasure;
    destruct Hj; try assert (j < S m) by simple_ineq; auto.
Qed.

Lemma termRelShowLt: forall j n T1 T2,
  j < n ->
  val_type_termRel (T2, j) (T1, n).
Proof.
  intros * Hj; unfold val_type_termRel, MR, argMeasure; auto.
Qed.

Ltac applyNSimpleIneq l := apply l; simple_ineq.

Ltac smaller_n :=
  autounfold; apply left_lex;
  (* simpl; omega. *)
  simple_ineq.

Ltac smaller_types :=
  autounfold; apply right_lex;
  try rewrite open_preserves_size';
  (* simpl; omega. *)
  simple_ineq.

(* Solve obligations from valType using ssreflect-based ideas, that is, reusing lemmas for the various cases. *)
Ltac valTypeObligationsSSReflectionCore :=
  try solve [simple_ineq | applyNSimpleIneq termRelShowOpen | applyNSimpleIneq termRelShow | applyNSimpleIneq termRelShowLt | smaller_types | discriminatePlus].
Ltac valTypeObligationsSSReflection :=
  program_simpl; valTypeObligationsSSReflectionCore.

Ltac valTypeObligations Hj :=
  program_simpl;
  solve [ smaller_n | smaller_types | discriminatePlus | (try destruct Hj; [ smaller_types | smaller_n ])].

Local Obligation Tactic := valTypeObligationsSSReflection.
Require Import Equations.Equations.

Lemma wf_val_type_termRel : well_founded val_type_termRel.
Proof. apply measure_wf; apply wf_lexprod; intro; apply lt_wf. Qed.
Hint Resolve wf_val_type_termRel.
Instance WF_val_type_termRel: WellFounded val_type_termRel := wf_val_type_termRel.

(* Program Definition expr_sem {n} T (A : pretype_dom n) k (p : k <= n) t : Prop := *)
(*   (* If evaluation terminates in at most k steps without running out of fuel, *) *)
(*   closed_ty 0 0 T /\ *)
(*   forall v j, *)
(*     steps t v j -> *)
(*     irred v -> *)
(*     j <= k -> *)
(*     (* then evaluation did not get stuck and the result satisfies A. *) *)
(*     exists v, A (k - j) _ v. *)

(* Equations val_type (Tn: ty * nat) (t : tm) : Prop := *)
(*   val_type Tn t by rec Tn val_type_termRel := *)
(*     val_type (pair T O) t := True; *)
(*     val_type (pair T (S n)) t := val_type (pair T n) t. *)

(* Next Obligation. Qed. *)
(* Next Obligation. induction n; simp val_type. Defined. *)

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

Ltac vtp_induction T n :=
  apply ind_args with (T := T) (n := n);
  clear T n.

Equations expr_sem n (T : ty) (A : pretype_dom n) k (p : k <= n) (t : tm) : Prop :=
  expr_sem n T A k p t :=
  (* If evaluation terminates in at most k steps without running out of fuel, *)
  closed_ty 0 0 T /\
  forall v j,
    steps t v j ->
    irred v ->
    j <= k ->
    (* then evaluation did not get stuck and the result satisfies A. *)
    exists v, A (k - j) _ v.


Equations val_type (Tn: ty * nat) (v : tm) : Prop :=
  val_type Tn t by rec Tn val_type_termRel :=
    val_type (pair TBot n) v := False;
    val_type (pair TTop n) v := irred v /\ tm_closed 0 0 v;
    val_type (pair (TFun l T1 T2) n) (tvar (VObj ds)) :=
                                  closed 0 0 T1 /\ closed 0 1 T2 /\
                                  dms_closed 0 1 ds /\
                                  exists U1 U2 t,
                                    index l (dms_to_list (subst_dms ds ds)) = Some (dfun U1 U2 t) /\
                                    (forall vyds k (Hj: k < n),
                                        val_type (pair T1 k) (tvar (VObj vyds)) ->
                                        expr_sem k
                                          (open 0 (VObj vyds) T2)
                                          (fun kj p t => val_type (open 0 (VObj vyds) T2, kj) t)
                                          k _ (subst_tm vyds t));
    val_type (pair (TMem l L U) n) (tvar (VObj ds)) :=
                                       closed_ty 0 0 L /\ closed_ty 0 0 U /\ dms_closed 0 1 ds /\
                                       exists TX, index l (dms_to_list (subst_dms ds ds)) = Some (dty TX) /\
                                             (forall vy j (Hj: j <= n), val_type (pair L j) vy -> val_type (pair U j) vy) /\
                                             (forall vy j (Hj: j < n),
                                                 (val_type (pair L j) vy -> val_type (pair TX j) vy) /\
                                                 (val_type (pair TX j) vy -> val_type (pair U j) vy));
    val_type (pair (TSel (VObj ds) l) n) v :=
                                         irred v /\
                                         dms_closed 0 1 ds /\
                                         tm_closed 0 0 v /\
                                         exists TX, index l (dms_to_list (subst_dms ds ds)) = Some (dty TX) /\
                                               forall j (Hj: j < n), val_type (TX, j) v;
    val_type (pair (TBind T) n) (tvar (VObj ds)) :=
                                           closed_ty 1 0 T /\
                                           val_type (pair (open 0 (VObj ds) T) n) (tvar (VObj ds));
    val_type (pair (TAnd T1 T2) n) v := val_type (pair T1 n) v /\ val_type (pair T2 n) v;
    val_type (pair (TOr T1 T2) n) v :=
                                             closed_ty 0 0 T1 /\ closed_ty 0 0 T2 /\
                                             (val_type (pair T1 n) v \/ val_type (pair T2 n) v);
    val_type (pair T n) v := False.

Solve Obligations with valTypeObligationsSSReflection. (* Works *)
(* Solve All Obligations. (* No effect *) *)
(* Next Obligation. Qed. (* Works for 1 obligation. *) *)

Hint Constructors val_type_ind.
Hint Extern 5 (val_type_termRel _ _) =>
  smaller_types || smaller_n.

Next Obligation.
  Transparent val_type_unfold.
  Ltac loop := (subst; progress (better_case_match; simp val_type); loop) || idtac.
  apply ind_args with (T := t) (n := n); clear t n; intros * Hind;
    rewrite val_type_unfold_eq; unfold val_type_unfold; loop; eauto.
    (* rewrite val_type_unfold_eq in *. unfold val_type_unfold in *. simpl. auto. *)
  (* - constructors; rewrite val_type_unfold_eq in *; unfold val_type_unfold in *; easy. *)
  Opaque val_type_unfold.
Defined.

Definition vtp T n v := val_type (T, n) v.
Hint Unfold vtp.
Example ex0 : forall n v, irred v -> tm_closed 0 0 v -> vtp TTop n v.
Proof.
  intros; autounfold; now simp val_type.
Qed.

Lemma vtp_irred: forall T k v, vtp T k v -> irred v.
Proof.
  intros *; unfold vtp in *;
    funind (val_type (T, k) v) Hcall; intros; ev;
      solve [easy | intuition auto | unfold irred; intro Hsteps; ev; easy ].
Qed.
Hint Resolve vtp_irred.

Hint Unfold closed_ty.
Hint Constructors vr_closed.
Hint Constructors closed.
Hint Constructors dms_closed.
Hint Constructors dm_closed.
Hint Constructors tm_closed.
Hint Constructors dm_closed.

Lemma vtp_closed: forall T n v,
    vtp T n v -> closed_ty 0 0 T.
Proof.
  unfold vtp, closed_ty;
    intros *; vtp_induction T n; intros;
      destruct T;
      destruct v;
      simp val_type in *; ev;
        try eauto || easy.
  all: (destruct v0 || destruct v; simp val_type in *; ev; now eauto).
Qed.

Lemma vtp_v_closed : forall T n v, vtp T n v -> tm_closed 0 0 v.
  (* unfold vtp; intros; remember H as Hvtp; funind (val_type (T, n) v) Hcall; simp val_type in *. *)
  (* - admit. *)
  (* - ev; clear Hcall. simp expr_sem in *. *)
  (*   admit. *)
  unfold vtp;
    intros *; vtp_induction T n; intros * Hind; intros;
    destruct T;
    destruct v;
    simp val_type in *; ev;
      try eauto || easy.
  all: try solve [destruct v; simp val_type in *; ev; now eauto].
  all: try solve [destruct v0; simp val_type in *; ev; now eauto].
  all: try (destruct v0; simp val_type in *; ev; eauto).
  Ltac indSearch Hind :=
    match goal with
    | H : val_type (?T1, ?n1) _ |- _ =>
      lets ?: Hind H; eauto
    end.
  all: try match goal with
    | H : ?A \/ ?B |- _ => destruct H
    end; indSearch Hind.
Qed.
Hint Resolve vtp_v_closed.

Example ex3: forall T n, closed 0 1 T -> vtp (TMem 0 TBot TTop) n (tvar (VObj (dcons (dty T) dnil))).
Proof.
  intros; autounfold; simp val_type; intuition eauto; simpl;
    eexists; intuition eauto; simp val_type in *; eauto; try easy.
Qed.

(* (* Check syntax_mutind. *) *)
(* Check closed_mutind. *)
(* Lemma open_closed : *)
(*   (forall i jv T i j k, closed i j (open k v T) -> closed i (S j) T). *)
(*   (* (forall v T i j k, vr_closed i j (open k v T) -> closed i (S j) T) /\ *) *)
(* Proof. *)
(*   induction T; simpl in *; constructor; try easy; *)
(*     inversion H; subst; eauto. *)
(*   (* inversion H; subst; eauto. *) *)
(*   (* repeat better_case_match; try constructor; inverts H. *) *)
(* Admitted. *)
(* (* Lemma open_closed : *) *)
(* (*   (forall v T i j k, closed i j (open k v T) -> closed i (S j) T). *) *)
(* (*   (* (forall v T i j k, vr_closed i j (open k v T) -> closed i (S j) T) /\ *) *) *)
(* (* Proof. *) *)
(* (*   induction T; simpl in *; constructor; try easy; *) *)
(* (*     inversion H; subst; eauto. *) *)
(* (*   (* inversion H; subst; eauto. *) *) *)
(* (*   (* repeat better_case_match; try constructor; inverts H. *) *) *)
(* (* Admitted. *) *)

(* Hint Extern 100 (val_type_termRel _ _) => *)
(*   valTypeObligationsSSReflection. *)
  (* (* all: try solve [destruct v; simp val_type in *; ev; now eauto]. *) *)
  (* (* all: try solve *) *)
  (* (*       [ destruct v; simp val_type in *; ev; now eauto | *) *)
  (* (*         destruct v0; simp val_type in *; ev; now eauto | *) *)
  (* (*         constructor; eapply H; smaller_types *) *)
  (* (*       ]. *) *)
  (* (* intuition eauto. *) *)
  (* (* intuition eauto. *) *)
  (* - destruct v; simp val_type in *; ev; now eauto. *)
  (* - destruct v; simp val_type in *; ev; now eauto. *)
  (* - destruct v0; simp val_type in *; ev; now eauto. *)
  (* - destruct v0; simp val_type in *; ev; now eauto. *)
  (* - destruct v; simp val_type in *; ev; now eauto. *)
  (*   (* assert (closed 0 0 (open 0 (VObj d) T)). { *) *)
  (*   (*   eapply H; valTypeObligationsSSReflection. *) *)
  (*   (* } *) *)
  (*   (* eauto using open_closed. *) *)
  (* - *)
  (*   constructor. *)
  (*   eapply H. smaller_types. *)
  (*   intuition (try smaller_types || eauto). *)
  (* - constructor; eapply H; smaller_types. *)
  (* (* - destruct H0. constructor; eapply H; valTypeObligationsSSReflection. *) *)
  (* (* - constructor; eapply H; valTypeObligationsSSReflection. *) *)
  (* (* - destruct v. try easy; *) *)
  (* (*     try destruct v; simp val_type in *; ev; now eauto. *) *)
  (* (*   (* Either case_match or better_case_match works*) *) *)
  (* (*   repeat better_case_match; ev; eauto 6. *) *)
  (* (*     contradiction. *) *)
  (* (* unfold vtp; intros *; *) *)
  (* (* apply ind_args with (T := T) (n := n); clear T n; intros * Hind ?. *) *)
  (* (* funind val_type Hind. *) *)
  (* (* induction T; intros; destruct v; vtp_simpl_unfold; ev; try eauto; *) *)
  (* (*   (* Either case_match or better_case_match works*) *) *)
  (* (*   repeat better_case_match; ev; eauto 6; *) *)
  (* (*     contradiction. *) *)


Lemma vtp_mon: forall T v m n,
    vtp T n v ->
    m <= n ->
    vtp T m v.
Proof.
  unfold vtp.
  intros *. revert m.
  funind (val_type (T, n) v) Hcall.
  all: intros; simp val_type; ev;
    unfold closed_ty in *;
    simp expr_sem in *;
    repeat split_conj; eauto; try easy.

  - do 3 eexists; split_conj; eauto; intros.
    match goal with
    | Hfun: forall (ds: dms), _ |- _ =>
      lets Hfunsucceeds: Hfun ___; eauto
    end.
    Unshelve.
    omega.
  - eexists; split_conj; eauto.

  - match goal with
    | [ H : val_type _ _ \/ val_type _ _ |- _ ] => destruct H
    end; eauto.
Qed.

Hint Resolve vtp_mon.
  (* - case_or_vtp; eauto. *)
  (*   Hint Constructors or. *)
  (*   intuition (mon_induct_step Hind n). *)
  (* Ltac mon_induct_step Hind n := (try (apply Hind with (n' := n); try smaller_types; assumption)). *)
  (* - *)
  (*   intros. *)

  (*   lets Hfunsucceeds: H3 ___. eauto. eauto. *)
  (*     assert (Hk: k < n0) by omega; specialize (H3 vyds k Hk H4); simp expr_sem in H3; *)
  (*       ev; eauto. *)
  (*   lets (vr & Hworks): H8 ___; eauto; ev. eapply Hworks. *)
  (*   eapply H8. *)

  (*   firstorder eauto. *)

  (* lets H: (H3 vyds k). *)
  (* do 3 eexists; repeat split_conj; eauto. *)
  (* eexists. *)
  (* repeat eexists; eauto. *)
  (* - clear Hcall. *)
  (*   unfold closed_ty in *. eapply closed_open; simpl. assumption. *)
  (* eauto using closed_open, closed_upgrade. *)
  (* Check closed_open. *)
  (* Check closed_upgrade. *)

  (* (* Check val_type_ind_fun. *) *)
  (* (* induction (val_type_ind_fun (T, n) v). *) *)

  (* (* Print FunctionalInduction_val_type. *) *)
  (* (* funind val_type Hcall. *) *)
  (* (*   intros *; revert v m; *) *)
  (* (*   vtp_induction T n; intros * Hind * Hvtpn1 * Hmn. *) *)
  (* (* destruct T; destruct v; simp val_type in *; ev; repeat split_conj. *) *)

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

(* Fixpoint subst_all_ty (env : venv) (T: ty) := *)
(*   match env with *)
(*   | [] => T *)
(*   | v :: vs => *)
(*     subst_all_ty vs (open (length vs) (VObj v) T) *)
(*   end. *)

(* Goal forall l dms, subst_all_ty [dms] (TSel (VarB 0) l) = TSel (VObj dms) l. *)
(*   easy. *)
(* Qed. *)
(* Goal forall l dms0 dms1, subst_all_ty [dms1, dms0] (TSel (VarB 1) l) = TSel (VObj dms1) l. *)
(*   simpl. *)
(*   easy. *)
(* Qed. *)

(* Require Import dot_monads. *)

(* Fixpoint vr_subst_all (env: list vr) (v: vr) { struct v }: option vr := *)
(*   match v with *)
(*     | VarF x => ret (VarF x) *)
(*     | VarB x => index x env *)
(*     | VObj dms => *)
(*       dms' <- dms_subst_all (VarB 0 :: env) dms; *)
(*       ret (VObj dms') *)
(*   end *)
(* with subst_all (env: list vr) (T: ty) { struct T }: option ty := *)
(*   match T with *)
(*     | TTop        => ret TTop *)
(*     | TBot        => ret TBot *)
(*     | TSel v1 l     => *)
(*       v1' <- vr_subst_all env v1; *)
(*       ret (TSel v1' l) *)
(*     | TFun l T1 T2  => *)
(*       T1' <- subst_all env T1; *)
(*       T2' <- subst_all (VarB 0 :: env) T2; *)
(*       ret (TFun l T1' T2') *)
(*     | TMem l T1 T2  => *)
(*       T1' <- subst_all env T1; *)
(*       T2' <- subst_all env T2; *)
(*       ret (TMem l T1' T2') *)
(*     | TBind T1    => *)
(*       T1' <- subst_all (VarB 0 :: env) T1; *)
(*       ret (TBind T1') *)
(*     | TAnd T1 T2  => *)
(*       T1' <- subst_all env T1; *)
(*       T2' <- subst_all env T2; *)
(*       ret (TAnd T1' T2') *)
(*     | TOr T1 T2   => *)
(*       T1' <- subst_all env T1; *)
(*       T2' <- subst_all env T2; *)
(*       ret (TOr T1' T2') *)
(*   end *)
(* with tm_subst_all (env: list vr) (t: tm) { struct t }: option tm := *)
(*    match t with *)
(*      | tvar v => v' <- vr_subst_all env v; ret (tvar v') *)
(*      | tapp t1 l t2 => *)
(*        t1' <- tm_subst_all env t1; *)
(*        t2' <- tm_subst_all env t2; *)
(*        ret (tapp t1' l t2') *)
(*    end *)
(* with dm_subst_all (env: list vr) (d: dm) { struct d }: option dm := *)
(*    match d with *)
(*      | dfun T1 T2 t2 => *)
(*        T1' <- subst_all env T1; *)
(*        T2' <- subst_all (VarB 0 :: env) T2; *)
(*        t2' <- tm_subst_all (VarB 0 :: env) t2; *)
(*        ret (dfun T1' T2' t2') *)
(*      | dty T1 => *)
(*        T1' <- subst_all env T1; *)
(*        ret (dty T1') *)
(*    end *)
(* with dms_subst_all (env: list vr) (ds: dms) { struct ds }: option dms := *)
(*    match ds with *)
(*      | dnil => ret dnil *)
(*      | dcons d ds => *)
(*        d'  <- dm_subst_all env d; *)
(*        ds' <- dms_subst_all env ds; *)
(*        ret (dcons d' ds') *)
(*    end. *)

Ltac beq_nat :=
  match goal with
  | H : (?a =? ?b) = true |- _ => try eapply beq_nat_true in H
  | H : (?a =? ?b) = false |- _ => try eapply beq_nat_false in H
  end.

Lemma index_Forall:
  forall {X} (env : list X) i P, Forall P env -> i < length env ->
                            exists v, index i env = Some v /\ P v.
Proof.
  intros * HFor Hlen; induction env.
  - easy.
  - inverse HFor; simpl; case_match; beq_nat; eauto.
Qed.

(* (* SearchPattern ((?A -> Prop) -> list ?A -> Prop). *) *)
(* Lemma subst_all_closed_upgrade_rec_vr: *)
(*   forall env i, *)
(*     Forall (vr_closed i 0) env -> *)
(*     forall j v, *)
(*       vr_closed i j v -> length env = j -> *)
(*       exists v', vr_subst_all env v = Some v' /\ *)
(*             vr_closed i 0 v'. *)
(* Proof. *)
(*   intros * HenvCl; induction v; intros * Hcl Hlen; simpl in *; inverse Hcl; *)
(*   intuition eauto using index_Forall. *)
(* Abort. *)

(* Lemma subst_all_closed_upgrade_rec: *)
(*   (forall v, forall i k env, Forall (vr_closed i k) env -> forall j, vr_closed i j v -> length env = j -> exists v', vr_subst_all env v = Some v' /\ vr_closed i k v') /\ *)
(*   (forall T, forall i k env, Forall (vr_closed i k) env -> forall j, closed i j T -> length env = j -> exists T', subst_all env T = Some T' /\ closed i k T') /\ *)
(*   (forall t, forall i k env, Forall (vr_closed i k) env -> forall j, tm_closed i j t -> length env = j -> exists t', tm_subst_all env t = Some t' /\ tm_closed i k t') /\ *)
(*   (forall dm, forall i k env, Forall (vr_closed i k) env -> forall j, dm_closed i j dm -> length env = j -> exists dm', dm_subst_all env dm = Some dm' /\ dm_closed i k dm') /\ *)
(*   (forall T, forall i k env, Forall (vr_closed i k) env -> forall j, dms_closed i j T -> length env = j -> exists dms', dms_subst_all env T = Some dms' /\ dms_closed i k dms'). *)
(* Proof. *)
(*   apply syntax_mutind. *)
(*   all: try solve [intros * HenvCl * Hcl * Hlen; simpl in *; inverse Hcl; simpl in *; subst; intuition eauto using index_Forall]. *)
(*   - intros * Hind * HenvCl * Hcl * Hlen; simpl in *; inverts Hcl. *)

(*     Ltac indLater Hind env i j k :=  *)
(*       lets (? & -> & ?): Hind i (S k) (VarB 0 :: env) (S j) ___; simpl; eauto; *)
(*       try (constructors; [eauto | eapply Forall_impl with (P := vr_closed i k); intuition eauto using (proj1 closed_upgrade_rec)]). *)
(*     indLater Hind env i j k. *)
(*   - intros * Hindt * Hindt1 * HenvCl * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     Ltac indNow Hind env i j k :=  *)
(*       lets (? & -> & ?): Hind i k env j ___; simpl; eauto. *)
(*     indNow Hindt env i j k. *)
(*     indLater Hindt1 env i j k. *)
(*   - intros * Hindt * Hindt1 * HenvCl * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow Hindt env i j k. *)
(*     indNow Hindt1 env i j k. *)
(*   - intros * Hindt * HenvCl * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow Hindt env i j k. *)
(*   - intros * Hindt * HenvCl * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indLater Hindt env i j k. *)
(*   - intros * Hindt * Hindt1 * HenvCl * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow Hindt env i j k. *)
(*     indNow Hindt1 env i j k. *)
(*   - intros * Hindt * Hindt1 * HenvCl * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow Hindt env i j k. *)
(*     indNow Hindt1 env i j k. *)
(*   - intros * Hindt * HenvCl * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow Hindt env i j k. *)
(*   - intros * Hindt * Hindt1 * HenvCl * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow Hindt env i j k. *)
(*     indNow Hindt1 env i j k. *)
(*   - intros * Hindt * Hindt1 * Hindt2 * HenvCl * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow Hindt env i j k. *)
(*     indLater Hindt1 env i j k. *)
(*     indLater Hindt2 env i j k. *)
(*   - intros * Hindt * HenvCl * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow Hindt env i j k. *)
(*   - intros * Hindt * Hindt1 * HenvCl * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow Hindt env i j k. *)
(*     indNow Hindt1 env i j k. *)
(* Qed. *)

(* Lemma subst_all_success_rec: *)
(*   (forall v, forall i env, forall j, vr_closed i j v -> length env = j -> exists v', vr_subst_all env v = Some v') /\ *)
(*   (forall T, forall i env, forall j, closed i j T -> length env = j -> exists T', subst_all env T = Some T') /\ *)
(*   (forall t, forall i env, forall j, tm_closed i j t -> length env = j -> exists t', tm_subst_all env t = Some t') /\ *)
(*   (forall dm, forall i env, forall j, dm_closed i j dm -> length env = j -> exists dm', dm_subst_all env dm = Some dm') /\ *)
(*   (forall T, forall i env, forall j, dms_closed i j T -> length env = j -> exists dms', dms_subst_all env T = Some dms'). *)
(* Proof. *)
(*   apply syntax_mutind. *)
(*   all: try solve [intros * Hcl * Hlen; simpl in *; inverse Hcl; simpl in *; subst; intuition eauto using index_Forall]. *)
(*   - intros * Hcl * Hlen; simpl in *; inverts Hcl. apply index_exists; auto. *)
(*     Ltac indNow' Hind env i j := *)
(*       lets (? & ->): Hind i env j ___; simpl; eauto. *)
(*     Ltac indLater' Hind env i j := *)
(*       lets (? & ->): Hind i (VarB 0 :: env) (S j) ___; simpl; eauto. *)

(*   - intros * Hindt * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indLater' Hindt env i j. *)
(*   - intros * Hindt * Hindt1 * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow' Hindt env i j. *)
(*     indLater' Hindt1 env i j. *)
(*   - intros * Hindt * Hindt1 * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow' Hindt env i j. *)
(*     indNow' Hindt1 env i j. *)
(*   - intros * Hindt * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow' Hindt env i j. *)
(*   - intros * Hindt * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indLater' Hindt env i j. *)
(*   - intros * Hindt * Hindt1 * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow' Hindt env i j. *)
(*     indNow' Hindt1 env i j. *)
(*   - intros * Hindt * Hindt1 * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow' Hindt env i j. *)
(*     indNow' Hindt1 env i j. *)
(*   - intros * Hindt * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow' Hindt env i j. *)
(*   - intros * Hindt * Hindt1 * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow' Hindt env i j. *)
(*     indNow' Hindt1 env i j. *)
(*   - intros * Hindt * Hindt1 * Hindt2 * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow' Hindt env i j. *)
(*     indLater' Hindt1 env i j. *)
(*     indLater' Hindt2 env i j. *)
(*   - intros * Hindt * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow' Hindt env i j. *)
(*   - intros * Hindt * Hindt1 * Hcl * Hlen; simpl in *; inverts Hcl. *)
(*     indNow' Hindt env i j. *)
(*     indNow' Hindt1 env i j. *)
(* Qed. *)
(* (*   (*   assert (exists T', dms_subst_all env d. *) *) *)
(* (*   (*   lets ?: Hind ___; eauto. *) *) *)
(* (*   (*   rewrite Hind. *) *) *)
(* (*   (*   case_match. *) *) *)
(* (*   (* inverse HenvCl; intuition eauto using index_Forall)]. *) *) *)

(* Lemma subst_all_success: *)
(*   forall T, forall i env, forall j, closed i j T -> length env = j -> exists T', subst_all env T = Some T'. *)
(* Proof. *)
(*   apply subst_all_success_rec. *)
(* Qed. *)

(*   (* induction env. *) *)
(*   (* - admit. *) *)
(*   (* - intros * HenvCl * Hcl Hlen; *) *)
(*   (*   simpl in *; subst. *) *)
(*   (*   inverse HenvCl. *) *)

(*   (* intros HenvCL. *) *)
(*   (* intros * Hcl Hlen HenvCl. gen i j. *) *)
(*   (* induction env. admit. *) *)
(*   (* simpl in *; subst. *) *)
(*   (* intros * Hcl Hlen HenvCl. *) *)
(*   (* inverse HenvCl. *) *)
(*   (* induction v; *) *)
(*   (* simpl in *; subst; *) *)
(*   (*   inversion Hcl; subst; *) *)
(*   (*   eexists; split_conj; simpl; eauto; try omega. *) *)
(*   (* case_match. *) *)
(*   (* admit. *) *)

(* Lemma subst_all_closed_upgrade_rec: *)
(*   (forall l j v, vr_closed l j v -> forall vx, v = vr_open j vx v) /\ *)
(*   (forall l j T, closed l j T -> forall vx, T = open j vx T) /\ *)
(*   (forall l j t, tm_closed l j t -> forall vx, t = tm_open j vx t) /\ *)
(*   (forall l j d, dm_closed l j d -> forall vx, d = dm_open j vx d) /\ *)
(*   (forall l j ds, dms_closed l j ds -> forall vx, ds = dms_open j vx ds). *)
(* Proof. *)

(* The lemma that would be needed here is a different one. *)
(* Lemma etp_closed: forall T k v env, *)
(*     Forall (dms_closed 0 0) env -> *)
(*     etp T k v env -> wf env T. *)
(* Proof. *)
(*   unfold etp, wf, closed_ty. *)
(*   intros * Hcl H. *)
(*   destruct H as (T'' & e'' & Hty & Htm & Hclosed & Hexp). *)
(*   lets (_ & HclTh & _) : subst_all_closed_upgrade_rec. *)
(*   lets ? : HclTh T 0 0 env. *)
(*   (* lets (? & ? & ?) : (proj1 (proj2 subst_all_closed_upgrade_rec)) ___. *) *)
(*   simp expr_sem in *. ev. *)
(*   tauto. *)
(* Qed. *)
(* Hint Resolve etp_closed. *)

Definition wf {A} (G : list A) T := closed 0 (length G) T.

Program Definition etp T k e :=
  expr_sem k T (fun k _ => vtp T k) k _ e.

Lemma etp_closed: forall T k v,
    etp T k v -> @wf ty [] T.
Proof.
  unfold etp; intros; simp expr_sem in *; tauto.
Qed.
Hint Resolve etp_closed.

Program Lemma index_sigT : forall {X} vs (n : {n : id | n < length vs}),
                       {T:X & index (proj1_sig n) vs = Some T}.
Proof.
  intros ? vs [n H]; induction vs; simpl in *.
  - exfalso; inversion H.
  - better_case_match; beq_nat; subst; eauto.
Qed.

Definition indexTot {X} (xs : list X) (n : {n : id | n < length xs}): X :=
  projT1 (index_sigT xs n).

Program Fixpoint vr_subst_all_tot i (env: list vr) (v: vr) (_ : vr_closed i (length env) v) { struct v }: vr :=
  match v with
    | VarF x => VarF x
    | VarB x => indexTot env x
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
Solve All Obligations with program_simpl; inverts H; auto.

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

Program Definition vtpEnvCore T k v env (HwfT : wf env T) (HwfV : tm_closed 0 (length env) v) :=
  let venv := map VObj env in
  vtp (subst_all_tot 0 venv T _) k (tm_subst_all_tot 0 venv v _).
Solve Obligations with program_simpl; rewrite map_length; auto.

Program Definition vtpEnv T k v env :=
  { HwfT : wf env T |
    { HwfV : tm_closed 0 (length env) v | vtpEnvCore T k v env _ _ }}.

Lemma vtpEnv_closed:
  forall T k v env, vtpEnv T k v env -> wf env T.
Proof. unfold vtpEnv, wf, closed_ty; program_simpl. Qed.
Hint Resolve vtpEnv_closed.

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

Program Definition etpEnvCore T k e env (HwfT : wf env T) (HwfE : tm_closed 0 (length env) e) :=
  let venv := map VObj env in
  let T' := subst_all_tot 0 venv T _ in
  expr_sem k T' (fun k _ => vtp T' k) k _ (tm_subst_all_tot 0 venv e _).

Solve Obligations with program_simpl; rewrite map_length; auto.

Program Definition etpEnv T k e env :=
  { HwfT : wf env T |
    { HwfE : tm_closed 0 (length env) e | etpEnvCore T k e env _ _ }}.
Hint Unfold etpEnv.
Hint Transparent etpEnv.
Hint Transparent wf.

Lemma etpEnv_closed: forall T k v env,
    etpEnv T k v env -> wf env T.
Proof. unfold etpEnv, wf; program_simpl. Qed.
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
        vtpEnvCore T1 k e env _ _ -> vtpEnvCore T2 k e env _ _ }}.
Solve Obligations with program_simpl; unfold wf in *; erewrite wf_length in *; eauto.

(* Definition sem_subtype (G : tenv) (T1 T2: ty) := *)
(*   wf G T1 /\ *)
(*   wf G T2 /\ *)
(*   forall k env, *)
(*     R_env k env G -> *)
(*     forall e, etpEnv T1 k e env -> etpEnv T2 k e env. *)

(* Definition sem_vl_subtype (G : tenv) (T1 T2: ty) := *)
(*   wf G T1 /\ *)
(*   wf G T2 /\ *)
(*   forall k env, *)
(*     R_env k env G -> *)
(*     forall v, *)
(*       vtpEnv T1 k v env -> vtpEnv T2 k v env. *)

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

(* Lemma closed_subst_success: forall T env, *)
(*     (closed_ty 0 (length env) T) -> *)
(*     exists T1, subst_all env T = Some T1. *)
(* Admitted. *)

(* Write lemmas to get rid of all the extra side conditions and get to the meat. *)
Lemma vl_subtype_to_subtype : forall G T1 T2,
    sem_vl_subtype G T1 T2 -> sem_subtype G T1 T2.
Proof.
  unfold sem_subtype, sem_vl_subtype, wf.
  program_simpl.
  repeat match goal with
         | H: ?P |- { H : ?P | ?Q } => exists H
         end.
  intros.
  unfold etpEnvCore in *; simp expr_sem in *.
  ev; split_conj; intros.
  - admit.
  - exists v.
    unfold vtpEnvCore in *.
    (* unfold etpEnvCore_obligation_1 in *. *)
    intuition eauto.
    (* XXX Reprove subst_all_closed_upgrade_rec for subst_all_tot. Then, modify
    vtp to ensure it only holds for closed terms, prove it, lift that proof to
    R_env, then try again (or maybe rather move the hard work in vtp_etp and etp_vtp lemmas). *)

(*   - intros. *)
(*   vtp, etpEnvCore, vtpEnvCore; simp val_type. *)
(*   unfold etpEnv in *. *)
(*   Transparent expr_sem. *)
(*   unfold expr_sem. *)
(*   Opaque expr_sem. *)
(*   intros * (? & ? & Himpl); split_conj; eauto. intros * Henv * (? & ?). *)

(*   ev; split_conj; *)
(*     replace (length G) with (length env) in * by eauto; *)
(*     eauto. *)
(*   lets (? & ?): closed_subst_success T2 (map VObj env) ___; *)
(*   try rewrite map_length; eauto. *)
(*   do 2 eexists; split_conj; eauto. *)
(*   admit. *)
(*   eauto. *)
(*   (* info_eauto. *) *)
(*   (* info_eauto. *) *)
(*   (* info_eauto. *) *)

(*   (* intuition info_eauto. *) *)
(*   (* - admit. *) *)
(*   (* - lets (? & ?) : H5 v j ___; eauto. eapply H9. *) *)
(*   (*   eauto. *) *)

(*   (* simp expr_sem in *; ev. *) *)
(*   (* lets ? : Himpl Henv e ___; intuition eauto; repeat eexists. *) *)
(*   (* eauto. *) *)
(*   (* eauto. *) *)
(* Admitted. *)
(* Hint Resolve vl_subtype_to_subtype. *)

Abort.
