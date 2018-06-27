Require Import Omega.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.

Require Import dot_storeless_tidy.
Require Import dot_storeless_wfrel_aux.
Require Import tactics.

(*******************)
(* Infrastructure for total parallel substitution on locally closed terms *)

Definition wf {A} (G : list A) T := closed 0 (length G) T.

Ltac inverts_if_nonvar x H :=
    tryif is_var x then fail else inverts H.
Ltac inverts_closed :=
  match goal with
  | H : vr_closed _ _ ?v  |- _ =>
    inverts_if_nonvar v H
  | H : closed _ _ ?T     |- _ =>
    inverts_if_nonvar T H
  | H : tm_closed _ _ ?t  |- _ =>
    inverts_if_nonvar t H
  | H : dm_closed _ _ ?d  |- _ =>
    inverts_if_nonvar d H
  | H : dms_closed _ _ ?d |- _ =>
    inverts_if_nonvar d H
  end.

Ltac beq_nat :=
  match goal with
  | H : (?a =? ?b) = true |- _ => try eapply beq_nat_true in H
  | H : (?a =? ?b) = false |- _ => try eapply beq_nat_false in H
  end.


Ltac unmut_lemma H := destruct H; ev; eauto.
Lemma vr_closed_upgrade: forall i k k1 v,
  vr_closed i k v -> k <= k1 -> vr_closed i k1 v.
Proof. unmut_lemma closed_upgrade_rec. Qed.
Hint Resolve vr_closed_upgrade.

Lemma env_closed_upgrade: forall i k k1 env,
  Forall (vr_closed i k) env ->
  k <= k1 ->
  Forall (vr_closed i k1) env.
Proof. eauto using Forall_impl. Qed.
Hint Resolve env_closed_upgrade.

Hint Constructors Forall.

Lemma index_Forall:
  forall {X} (env : list X) i P, Forall P env -> i < length env ->
                            exists v, index i env = Some v /\ P v.
Proof.
  intros * HFor Hlen; induction env.
  - easy.
  - inverse HFor; simpl; case_match; beq_nat; eauto.
Qed.

Lemma index_Forall': forall {X v} (env: list X) i (P: X -> Prop) (Henv: Forall P env) (Hlen: i < length env) (Hidx: index i env = Some v), P v.
  intros.
  destruct (index_Forall env i _ Henv); ev; congruence.
Qed.

(* Can't work because there's no constant head symbol in the conclusion, so auto wouldn't know when to try this out. So we write apply_Forall. *)
(* Hint Resolve index_Forall'. *)

(* Use "solve" because in subst_all_res_closed_rec this tactic leads the proof
   search down the wrong path whenever it doesn't solve the goal immediately;
   using "solve" is sort of what eauto's proof search and backtracking would do
   anyway: if applying this lemma and searching further doesn't help, backtrack. *)
Ltac apply_Forall :=
  match goal with
  | H: Forall ?P ?env |- ?P _ => try solve [eapply (index_Forall' _ _ _ H); eauto]
  end.
(* Seems to actually work fine, but this is needed too seldom for now, and can be expensive. *)
(* Hint Extern 5 => apply_Forall. *)

Lemma step_closed: forall e v i k, step e v -> tm_closed i k e -> tm_closed i k v.
Proof.
  intros * Hst ?.
  induction Hst; repeat inverts_closed; eauto.
  unfold subst_tm.
  assert (tm_closed i (S k) t12). {
    admit.
  }
  admit.
Admitted.
  (* pose proof (proj1 (proj2 (proj2 closed_subst_rec))) as tm_closed_subst. *)
  (* eapply (tm_closed_subst t12 0 k). *)
  (* pose proof (proj1 (proj2 (proj2 closed_open_rec))) as tm_closed_open. *)
  (* eapply (tm_closed_open t12 0 k). *)

Require Import dot_monads.

Fixpoint vr_subst_all (env: list vr) (v: vr) { struct v }: option vr :=
  match v with
    | VarF x => ret (VarF x)
    | VarB x => index x env
    | VObj dms =>
      dms' <- dms_subst_all (VarB (length env) :: env) dms;
      ret (VObj dms')
  end
with subst_all (env: list vr) (T: ty) { struct T }: option ty :=
  match T with
    | TTop        => ret TTop
    | TBot        => ret TBot
    | TSel v1 l     =>
      v1' <- vr_subst_all env v1;
      ret (TSel v1' l)
    | TFun l T1 T2  =>
      T1' <- subst_all env T1;
      T2' <- subst_all (VarB (length env) :: env) T2;
      ret (TFun l T1' T2')
    | TMem l T1 T2  =>
      T1' <- subst_all env T1;
      T2' <- subst_all env T2;
      ret (TMem l T1' T2')
    | TBind T1    =>
      T1' <- subst_all (VarB (length env) :: env) T1;
      ret (TBind T1')
    | TAnd T1 T2  =>
      T1' <- subst_all env T1;
      T2' <- subst_all env T2;
      ret (TAnd T1' T2')
    | TOr T1 T2   =>
      T1' <- subst_all env T1;
      T2' <- subst_all env T2;
      ret (TOr T1' T2')
  end
with tm_subst_all (env: list vr) (t: tm) { struct t }: option tm :=
   match t with
     | tvar v => v' <- vr_subst_all env v; ret (tvar v')
     | tapp t1 l t2 =>
       t1' <- tm_subst_all env t1;
       t2' <- tm_subst_all env t2;
       ret (tapp t1' l t2')
   end
with dm_subst_all (env: list vr) (d: dm) { struct d }: option dm :=
   match d with
     | dfun T1 T2 t2 =>
       T1' <- subst_all env T1;
       T2' <- subst_all (VarB (length env) :: env) T2;
       t2' <- tm_subst_all (VarB (length env) :: env) t2;
       ret (dfun T1' T2' t2')
     | dty T1 =>
       T1' <- subst_all env T1;
       ret (dty T1')
   end
with dms_subst_all (env: list vr) (ds: dms) { struct ds }: option dms :=
   match ds with
     | dnil => ret dnil
     | dcons d ds =>
       d'  <- dm_subst_all env d;
       ds' <- dms_subst_all env ds;
       ret (dcons d' ds')
   end.

Lemma subst_all_success_rec:
  (forall v, forall i env, forall j, vr_closed i j v -> length env = j -> exists v', vr_subst_all env v = Some v') /\
  (forall T, forall i env, forall j, closed i j T -> length env = j -> exists T', subst_all env T = Some T') /\
  (forall t, forall i env, forall j, tm_closed i j t -> length env = j -> exists t', tm_subst_all env t = Some t') /\
  (forall dm, forall i env, forall j, dm_closed i j dm -> length env = j -> exists dm', dm_subst_all env dm = Some dm') /\
  (forall T, forall i env, forall j, dms_closed i j T -> length env = j -> exists dms', dms_subst_all env T = Some dms').
Proof.
  apply syntax_mutind.
  (* all: try solve [intros * Hcl * Hlen; simpl in *; inverse Hcl; simpl in *; subst; intuition eauto using index_Forall]. *)
  all: try solve [intros; simpl in *; inverts_closed; simpl in *; subst; intuition eauto using index_Forall, index_exists].
  (* all: try solve [intros; simpl in *; inverts_closed; simpl in *; subst; firstorder (ev; simpl; autorewrite with core; eauto 20 using index_Forall, index_exists)]. *)
    Ltac indNow' Hind env i j :=
      lets (? & ->): Hind i env j ___; simpl; eauto.
    Ltac indLater' Hind env i j :=
      lets (? & ->): Hind i (VarB (length env) :: env) (S j) ___; simpl; eauto.
  - intros * Hindt; intros; simpl in *; inverts_closed.
    indLater' Hindt env i j.
  - intros * Hindt * Hindt1; intros; simpl in *; inverts_closed.
    (* Ltac guess H := *)
    (*   repeat match type of H with *)
    (*          | forall x : ?T, _ => *)
    (*            let x := fresh "x" in *)
    (*            evar (x: T); *)
    (*            let x' := eval unfold x in x *)
    (*              in specialize (H x') *)
    (*          end. *)

    (* Ltac firstorder_case_match T := *)
    (*   match goal with *)
    (*   | |- context [ match ?x with _ => _ end ] => *)
    (*     assert (exists y, x = Some y) as (? & ->); T *)
    (*   end. *)
    (* firstorder_case_match ltac:(firstorder eauto). *)
    (* firstorder_case_match idtac. *)
    (* (* ltac:(guess Hindt1; eauto). *) *)
    (* guess Hindt1. *)
    (* eauto. *)
    (* eauto. *)
    (* Unshelve. shelve. shelve. all: eauto.  *)

    (* eapply Hindt1; simpl; eauto. *)
    (* simpl in *. *)

    indNow' Hindt env i j.
    indLater' Hindt1 env i j.
  - intros * Hindt * Hindt1; intros; simpl in *; inverts_closed.
    indNow' Hindt env i j.
    indNow' Hindt1 env i j.
  - intros * Hindt; intros; simpl in *; inverts_closed.
    indNow' Hindt env i j.
  - intros * Hindt; intros; simpl in *; inverts_closed.
    indLater' Hindt env i j.
  - intros * Hindt * Hindt1; intros; simpl in *; inverts_closed.
    indNow' Hindt env i j.
    indNow' Hindt1 env i j.
  - intros * Hindt * Hindt1; intros; simpl in *; inverts_closed.
    indNow' Hindt env i j.
    indNow' Hindt1 env i j.
  - intros * Hindt; intros; simpl in *; inverts_closed.
    indNow' Hindt env i j.
  - intros * Hindt * Hindt1; intros; simpl in *; inverts_closed.
    indNow' Hindt env i j.
    indNow' Hindt1 env i j.
  - intros * Hindt * Hindt1 * Hindt2; intros; simpl in *; inverts_closed.
    indNow' Hindt env i j.
    indLater' Hindt1 env i j.
    indLater' Hindt2 env i j.
  - intros * Hindt; intros; simpl in *; inverts_closed.
    indNow' Hindt env i j.
  - intros * Hindt * Hindt1; intros; simpl in *; inverts_closed.
    indNow' Hindt env i j.
    indNow' Hindt1 env i j.
Qed.
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

Lemma steps_closed: forall e v n i k, steps e v n -> tm_closed i k e -> tm_closed i k v.
Proof. intros * Hst; induction Hst; eauto using step_closed. Qed.

Lemma Forall_map: forall {X Y} (xs: list X) (f: X -> Y) (P : X -> Prop) (Q : Y -> Prop),
    Forall P xs ->
    (forall a, P a -> Q (f a)) ->
    Forall Q (map f xs).
Proof. intros * Hforall; induction xs; simpl; inverts Hforall; eauto. Qed.
Hint Resolve Forall_map.

Lemma dms_to_env_closed: forall i k env,
    Forall (dms_closed i (S k)) env ->
    Forall (vr_closed i k) (map VObj env).
Proof. eauto using Forall_map. Qed.
Hint Resolve dms_to_env_closed.

Lemma dms_closed_upgrade: forall i k k1 v,
  dms_closed i k v -> k <= k1 -> dms_closed i k1 v.
Proof. unmut_lemma closed_upgrade_rec. Qed.
Hint Resolve dms_closed_upgrade.

Lemma subst_all_nonTot_res_closed_rec:
  (forall v i env, Forall (vr_closed i (length env)) env -> forall (Hcl: vr_closed i (length env) v),
          exists v', vr_subst_all env v = Some v' /\
                vr_closed i (length env) v') /\
  (forall T i env, Forall (vr_closed i (length env)) env -> forall (Hcl: closed i (length env) T),
          exists T', subst_all env T = Some T' /\
                closed i (length env) T') /\
  (forall t i env, Forall (vr_closed i (length env)) env -> forall (Hcl: tm_closed i (length env) t),
          exists t', tm_subst_all env t = Some t' /\
                tm_closed i (length env) t') /\
  (forall d i env, Forall (vr_closed i (length env)) env -> forall (Hcl: dm_closed i (length env) d),
          exists d', dm_subst_all env d = Some d' /\
                dm_closed i (length env) d') /\
  (forall d i env, Forall (vr_closed i (length env)) env -> forall (Hcl: dms_closed i (length env) d),
          exists d', dms_subst_all env d = Some d' /\
                dms_closed i (length env) d').
Proof.
    Ltac smartInd :=
      match goal with
      | Hind : context [ ?f _ ?s ] |- context [ match ?f ?env ?s with _ => _ end ] =>
        lets (? & -> & ?): Hind env ___; simpl; eauto
      end.
  apply syntax_mutind; simpl; intros;
      inverts_closed; subst;
      intuition eauto using index_Forall; repeat smartInd; eauto.
Qed.

Lemma vr_subst_all_nonTot_res_closed:
  (forall v i env, Forall (vr_closed i (length env)) env -> forall (Hcl: vr_closed i (length env) v),
          exists v', vr_subst_all env v = Some v' /\
                vr_closed i (length env) v').
Proof. unmut_lemma subst_all_nonTot_res_closed_rec. Qed.
Lemma subst_all_nonTot_res_closed:
  (forall T i env, Forall (vr_closed i (length env)) env -> forall (Hcl: closed i (length env) T),
          exists T', subst_all env T = Some T' /\
                closed i (length env) T').
Proof. unmut_lemma subst_all_nonTot_res_closed_rec. Qed.
Lemma tm_subst_all_nonTot_res_closed:
  (forall t i env, Forall (vr_closed i (length env)) env -> forall (Hcl: tm_closed i (length env) t),
          exists t', tm_subst_all env t = Some t' /\
                tm_closed i (length env) t').
Proof. unmut_lemma subst_all_nonTot_res_closed_rec. Qed.
Lemma dm_subst_all_nonTot_res_closed:
  (forall d i env, Forall (vr_closed i (length env)) env -> forall (Hcl: dm_closed i (length env) d),
          exists d', dm_subst_all env d = Some d' /\
                dm_closed i (length env) d').
Proof. unmut_lemma subst_all_nonTot_res_closed_rec. Qed.
Lemma dms_subst_all_nonTot_res_closed:
  (forall d i env, Forall (vr_closed i (length env)) env -> forall (Hcl: dms_closed i (length env) d),
          exists d', dms_subst_all env d = Some d' /\
                dms_closed i (length env) d').
Proof. unmut_lemma subst_all_nonTot_res_closed_rec. Qed.
Hint Resolve
     vr_subst_all_nonTot_res_closed
     subst_all_nonTot_res_closed
     tm_subst_all_nonTot_res_closed
     dm_subst_all_nonTot_res_closed
     dms_subst_all_nonTot_res_closed.

Definition evalToSome env e v k j :=
  (exists t', tm_subst_all (map VObj env) e = Some t' /\ steps t' v j) /\ irred v /\ j <= k.

Lemma evalToSomeRes_closed: forall env e v n j l,
    evalToSome env e v n j ->
    tm_closed 0 l e ->
    length env = l ->
    Forall (dms_closed 0 (S l)) env ->
    tm_closed 0 l v.
Proof.
  unfold evalToSome; intros; subst;
    assert (exists t', tm_subst_all (map VObj env) e = Some t' /\ tm_closed 0 (length (map VObj env)) t')
    by (eapply tm_subst_all_nonTot_res_closed; try rewrite map_length; eauto); ev;
      optFuncs_det;
      rewrite map_length in *;
      eauto using steps_closed.
Qed.
Hint Resolve evalToSomeRes_closed.

(*******************)
(* Prove irreducible closed terms evaluate to themselves (vl_evalToSome_self).
   We must first prove that substitution leaves them unchnaged. *)

(* Define what's an identity substitution, through the required property (rather than through an inductive type). *)
Definition vr_env_id xs := forall n, n < length xs -> index n xs = Some (VarB n).

(* Allow proving vr_env_id. These lemmas could probably be the constructors for
   an inductive characterization. *)
Lemma nil_vr_env_id: vr_env_id [].
Proof. unfold vr_env_id; simpl; easy. Qed.

Lemma cons_vr_env_id: forall env, vr_env_id env -> vr_env_id (VarB (length env) :: env).
Proof. unfold vr_env_id; simpl; intros; case_match; beq_nat; subst; auto. Qed.

Hint Resolve nil_vr_env_id cons_vr_env_id.

(* Prove that an identity substitution is also an identity when lifted to our
   language syntax. *)
Lemma subst_closed_id_rec:
  (forall v i env, vr_env_id env -> forall (Hcl: vr_closed i (length env) v),
          vr_subst_all env v = Some v) /\
  (forall T i env, vr_env_id env -> forall (Hcl: closed i (length env) T),
          subst_all env T = Some T) /\
  (forall t i env, vr_env_id env -> forall (Hcl: tm_closed i (length env) t),
          tm_subst_all env t = Some t) /\
  (forall d i env, vr_env_id env -> forall (Hcl: dm_closed i (length env) d),
          dm_subst_all env d = Some d) /\
  (forall d i env, vr_env_id env -> forall (Hcl: dms_closed i (length env) d),
          dms_subst_all env d = Some d).
Proof.
  apply syntax_mutind; intros; simpl; trivial;
    inverts_closed; subst; eauto;
      repeat
        match goal with
        | Hind : context [ ?f _ ?s ] |- context [ match ?f ?env ?s with _ => _ end ] =>
          lets ->: Hind env ___; eauto
        end.
Qed.

Lemma tm_subst_closed_id: forall t i env, tm_closed i (length env) t -> vr_env_id env -> tm_subst_all env t = Some t.
Proof. unmut_lemma subst_closed_id_rec. Qed.

Lemma tm_subst_closed_id_nil: forall t i, tm_closed i 0 t -> tm_subst_all [] t = Some t.
Proof. eauto using tm_subst_closed_id. Qed.
Hint Resolve tm_subst_closed_id_nil.

Hint Constructors steps.

Lemma vl_evalToSome_self: forall v n i, irred v -> tm_closed i 0 v -> evalToSome [] v v n 0.
Proof. unfold evalToSome; intuition eauto. Qed.
