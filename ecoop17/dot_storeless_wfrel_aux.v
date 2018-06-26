Require Import Omega.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Equations.Equations.

Require Import dot_storeless_tidy.
Require Import tactics.

(*******************)
(* Renames for adaption. *)

Notation tsize_flat := tsize.

Lemma open_preserves_size': forall T v j,
    tsize_flat (open j v T) = tsize_flat T.
Proof. symmetry. eapply open_preserves_size. Qed.
Definition vl := tm.

Definition closed_ty i j T := closed j i T.
Hint Unfold closed_ty.

Hint Constructors vr_closed.
Hint Constructors closed.
Hint Constructors dms_closed.
Hint Constructors dm_closed.
Hint Constructors tm_closed.
Hint Constructors dm_closed.

(*******************)
(* Small-step semantics *)
Definition irred t0 := not (exists t1, step t0 t1).

Inductive steps t0 : tm -> nat -> Prop :=
| Step0 : steps t0 t0 0
| StepS : forall t1 t2 i, step t0 t1 -> steps t1 t2 i -> steps t0 t2 (S i).

(*******************)
(* Define language infrastructure. *)

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

Ltac smaller_n :=
  autounfold; apply left_lex;
  (* simpl; omega. *)
  simple_ineq.

Ltac smaller_types :=
  autounfold; apply right_lex; auto.

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

(* Solve obligations from valType using ssreflect-based ideas, that is, reusing lemmas for the various cases. *)
Ltac valTypeObligationsSSReflectionCore :=
  try solve [simple_ineq | applyNSimpleIneq termRelShowOpen | applyNSimpleIneq termRelShow | applyNSimpleIneq termRelShowLt | smaller_types | discriminatePlus].
Ltac valTypeObligationsSSReflection :=
  program_simpl; valTypeObligationsSSReflectionCore.

Ltac valTypeObligations Hj :=
  program_simpl;
  solve [ smaller_n | smaller_types | discriminatePlus | (try destruct Hj; [ smaller_types | smaller_n ])].

Local Obligation Tactic := valTypeObligationsSSReflection.

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
    A (k - j) _ v.


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
                                             (forall vy j (Hj: j <= n),
                                                 val_type (pair L j) vy -> val_type (pair U j) vy) /\
                                             (forall vy j (Hj: j < n),
                                                 val_type (pair L j) vy -> val_type (pair TX j) vy) /\
                                             (forall vy j (Hj: j < n),
                                                 val_type (pair TX j) vy -> val_type (pair U j) vy);
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
    eexists; intuition idtac; simp val_type in *; now eauto.
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
