Require Import Omega.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.

Require Import dot_storeless_tidy.
Require Import dot_storeless_wfrel_aux.
Require Import tactics.

(*******************)
(* Infrastructure for total parallel substitution on locally closed terms *)

Definition wf {A} (G : list A) T := closed (length G) 0 T.

Lemma closed_upgrade_both_rec:
  (forall i k v1, vr_closed i k v1 -> forall i1 k1, i <= i1 -> k <= k1 -> vr_closed i1 k1 v1) /\
  (forall i k T1, closed i k T1 -> forall i1 k1, i <= i1 -> k <= k1 -> closed i1 k1 T1) /\
  (forall i k t1, tm_closed i k t1 -> forall i1 k1, i <= i1 -> k <= k1 -> tm_closed i1 k1 t1) /\
  (forall i k d1, dm_closed i k d1 -> forall i1 k1, i <= i1 -> k <= k1 -> dm_closed i1 k1 d1) /\
  (forall i k ds1, dms_closed i k ds1 -> forall i1 k1, i <= i1 -> k <= k1 -> dms_closed i1 k1 ds1).
Proof. apply closed_mutind; eauto. Qed.

Ltac unmut_lemma H := destruct H; ev; eauto.

Lemma vr_closed_upgrade_both: forall t i i1 k k1, vr_closed i k t -> i <= i1 -> k <= k1 -> vr_closed i1 k1 t.
Proof. unmut_lemma closed_upgrade_both_rec. Qed.
Hint Extern 5 (vr_closed _ _ _) => try_once vr_closed_upgrade_both.

Lemma closed_upgrade_both: forall t i i1 k k1, closed i k t -> i <= i1 -> k <= k1 -> closed i1 k1 t.
Proof. unmut_lemma closed_upgrade_both_rec. Qed.
Hint Extern 5 (closed _ _ _) => try_once closed_upgrade_both.

Lemma tm_closed_upgrade_both: forall t i i1 k k1, tm_closed i k t -> i <= i1 -> k <= k1 -> tm_closed i1 k1 t.
Proof. unmut_lemma closed_upgrade_both_rec. Qed.
Hint Extern 5 (tm_closed _ _ _) => try_once tm_closed_upgrade_both.

Lemma dm_closed_upgrade_both: forall t i i1 k k1, dm_closed i k t -> i <= i1 -> k <= k1 -> dm_closed i1 k1 t.
Proof. unmut_lemma closed_upgrade_both_rec. Qed.
Hint Extern 5 (dm_closed _ _ _) => try_once dm_closed_upgrade_both.

Lemma dms_closed_upgrade_both: forall t i i1 k k1, dms_closed i k t -> i <= i1 -> k <= k1 -> dms_closed i1 k1 t.
Proof. unmut_lemma closed_upgrade_both_rec. Qed.
Hint Extern 5 (dms_closed _ _ _) => try_once dms_closed_upgrade_both.

(* Swap premises to help proof search! *)
Lemma Forall_impl' : forall A (P Q : A -> Prop) l, Forall P l ->
                     (forall a, P a -> Q a) ->
                     Forall Q l.
Proof. intuition eauto using Forall_impl. Qed.
Hint Extern 5 (Forall _ _) => try_once Forall_impl'.

Lemma env_closed_upgrade_both: forall i i1 k k1 env,
  Forall (vr_closed i k) env ->
  i <= i1 ->
  k <= k1 ->
  Forall (vr_closed i1 k1) env.
Proof. eauto. Qed.

Hint Extern 5 (Forall (vr_closed _ _) _) => try_once env_closed_upgrade_both.

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

Lemma step_closed: forall e v i, step e v -> tm_closed i 0 e -> tm_closed i 0 v.
Proof.
  destruct closed_open_rec; ev.
  intros * Hst ?; induction Hst; repeat inverts_closed; eauto;
    unfold subst_tm, subst_dms in *.
  match goal with
  | H: index _ _ = Some ?t |- _ =>
    assert (dm_closed i 0 t) by eauto using index_dm_closed
  end; inverts_closed; eauto.
Qed.
Hint Resolve step_closed.

Lemma steps_closed: forall e v n i, steps e v n -> tm_closed i 0 e -> tm_closed i 0 v.
Proof. intros * Hst; induction Hst; eauto using step_closed. Qed.
Hint Extern 5 (tm_closed _ _ _) => try_once steps_closed.

Lemma step_det: forall t u1 u2, step t u1 -> step t u2 -> u1 = u2.
Proof.
  intros * H1; gen u2; induction H1;
    intros * H2; inverse H2; try optFuncs_det; eauto;
    try match goal with
        | H : step (tvar (VObj _)) _ |- _ => inversion H
        end;
    fequal; eauto.
Qed.
Hint Resolve step_det.

Lemma steps_irred_det: forall t v1 v2 j1 j2, steps t v1 j1 -> steps t v2 j2 -> irred v1 -> irred v2 -> v1 = v2 /\ j1 = j2.
Proof.
  unfold irred; intros * Hs1 Hs2 Hv1 Hv2; gen j2; induction Hs1; intros; inverse Hs2;
    try solve [exfalso; eauto | eauto];
    (* Why do I need parens for `by`'s argument? *)
    enough (t2 = v2 /\ i = i0) by (intuition eauto);
    match goal with
    | H1 : step ?a ?b, H2 : step ?a ?c |- _ =>
      assert (b = c) as -> by eauto
    end; eauto.
Qed.
Hint Resolve steps_irred_det.

Require Import dot_monads.

Fixpoint vr_subst_par (sigma: id -> vr) (v: vr) { struct v }: vr :=
  match v with
    | VarF x => sigma x
    | VarB x => VarB x
    | VObj dms =>
      VObj (dms_subst_par sigma dms)
  end
with subst_par (sigma: id -> vr) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TBot        => TBot
    | TSel v1 l     =>
      TSel (vr_subst_par sigma v1) l
    | TFun l T1 T2  =>
      TFun l (subst_par sigma T1) (subst_par sigma T2)
    | TMem l T1 T2  =>
      TMem l (subst_par sigma T1) (subst_par sigma T2)
    | TBind T1    =>
      TBind (subst_par sigma T1)
    | TAnd T1 T2  =>
      TAnd (subst_par sigma T1) (subst_par sigma T2)
    | TOr T1 T2   =>
      TOr (subst_par sigma T1) (subst_par sigma T2)
    | TLater T1    =>
      TLater (subst_par sigma T1)
  end
with tm_subst_par (sigma: id -> vr) (t: tm) { struct t }: tm :=
   match t with
     | tvar v =>
       tvar (vr_subst_par sigma v)
     | tapp t1 l t2 =>
       tapp (tm_subst_par sigma t1) l (tm_subst_par sigma t2)
   end
with dm_subst_par (sigma: id -> vr) (d: dm) { struct d }: dm :=
   match d with
     | dfun T1 T2 t2 =>
       dfun (subst_par sigma T1) (subst_par sigma T2) (tm_subst_par sigma t2)
     | dty T1 =>
       dty (subst_par sigma T1)
   end
with dms_subst_par (sigma: id -> vr) (ds: dms) { struct ds }: dms :=
   match ds with
     | dnil => dnil
     | dcons d ds =>
       dcons (dm_subst_par sigma d) (dms_subst_par sigma ds)
   end.

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

Fixpoint env_to_sigma (env: list vr) (n: id): vr :=
  match env with
    | [] => VarF n
    | x :: xs  => if beq_nat n (length xs) then x else env_to_sigma xs n
  end.

Lemma env_to_sigma_index (env: list vr): forall n, n < length env -> index n env = Some (env_to_sigma env n).
Proof.
  induction env; simpl; intros;
    [ omega | better_case_match; beq_nat; eauto ].
Qed.

Lemma env_to_sigma_Forall:
  forall (env : list vr) i P, Forall P env -> i < length env ->
                            P (env_to_sigma env i).
Proof.
  intros * HFor Hlen; induction env; cbn in *.
  - omega.
  - inverse HFor; case_match; beq_nat; eauto.
Qed.

(* Use "solve" because in subst_all_res_closed_rec this tactic leads the proof
   search down the wrong path whenever it doesn't solve the goal immediately;
   using "solve" is sort of what eauto's proof search and backtracking would do
   anyway: if applying this lemma and searching further doesn't help, backtrack. *)
Ltac apply_env_Forall :=
  match goal with
  | H: Forall ?P ?env |- ?P _ => try solve [eapply (env_to_sigma_Forall _ _ _ H); eauto]
  end.

(* Seems to actually work fine, but this is needed too seldom for now, and can be expensive. *)
(* Hint Extern 5 => apply_Forall. *)
Lemma subst_par_nonTot_res_closed_rec:
  (forall v, forall i k env, Forall (vr_closed i k) env -> vr_closed (length env) k v ->
                   vr_closed i k (vr_subst_par (env_to_sigma env) v)) /\
  (forall T, forall i k env, Forall (vr_closed i k) env -> closed (length env) k T ->
                   closed i k (subst_par (env_to_sigma env) T)) /\
  (forall t, forall i k env, Forall (vr_closed i k) env -> tm_closed (length env) k t ->
                   tm_closed i k (tm_subst_par (env_to_sigma env) t)) /\
  (forall d, forall i k env, Forall (vr_closed i k) env -> dm_closed (length env) k d ->
                   dm_closed i k (dm_subst_par (env_to_sigma env) d)) /\
  (forall d, forall i k env, Forall (vr_closed i k) env -> dms_closed (length env) k d ->
                   dms_closed i k (dms_subst_par (env_to_sigma env) d)).
Proof.
  apply syntax_mutind; simpl; intros; inverts_closed;
    apply_env_Forall || eauto 7.
Qed.

Lemma vr_subst_par_nonTot_res_closed:
  (forall v i k env, Forall (vr_closed i k) env -> forall (Hcl: vr_closed (length env) k v),
        vr_closed i k (vr_subst_par (env_to_sigma env) v)).
Proof. unmut_lemma subst_par_nonTot_res_closed_rec. Qed.
Lemma subst_par_nonTot_res_closed:
  (forall T i k env, Forall (vr_closed i k) env -> forall (Hcl: closed (length env) k T),
        closed i k (subst_par (env_to_sigma env) T)).
Proof. unmut_lemma subst_par_nonTot_res_closed_rec. Qed.
Lemma tm_subst_par_nonTot_res_closed:
  (forall t i k env, Forall (vr_closed i k) env -> forall (Hcl: tm_closed (length env) k t),
        tm_closed i k (tm_subst_par (env_to_sigma env) t)).
Proof. unmut_lemma subst_par_nonTot_res_closed_rec. Qed.
Lemma dm_subst_par_nonTot_res_closed:
  (forall d i k env, Forall (vr_closed i k) env -> forall (Hcl: dm_closed (length env) k d),
        dm_closed i k (dm_subst_par (env_to_sigma env) d)).
Proof. unmut_lemma subst_par_nonTot_res_closed_rec. Qed.
Lemma dms_subst_par_nonTot_res_closed:
  (forall d i k env, Forall (vr_closed i k) env -> forall (Hcl: dms_closed (length env) k d),
        dms_closed i k (dms_subst_par (env_to_sigma env) d)).
Proof. unmut_lemma subst_par_nonTot_res_closed_rec. Qed.
Hint Resolve
     vr_subst_par_nonTot_res_closed
     subst_par_nonTot_res_closed
     tm_subst_par_nonTot_res_closed
     dm_subst_par_nonTot_res_closed
     dms_subst_par_nonTot_res_closed.

Fixpoint vr_subst_all (env: list vr) (v: vr) { struct v }: option vr :=
  match v with
    | VarF x => index x env
    | VarB x => ret (VarB x)
    | VObj dms =>
      dms' <- dms_subst_all env dms;
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
      T2' <- subst_all env T2;
      ret (TFun l T1' T2')
    | TMem l T1 T2  =>
      T1' <- subst_all env T1;
      T2' <- subst_all env T2;
      ret (TMem l T1' T2')
    | TBind T1    =>
      T1' <- subst_all env T1;
      ret (TBind T1')
    | TAnd T1 T2  =>
      T1' <- subst_all env T1;
      T2' <- subst_all env T2;
      ret (TAnd T1' T2')
    | TOr T1 T2   =>
      T1' <- subst_all env T1;
      T2' <- subst_all env T2;
      ret (TOr T1' T2')
    | TLater T1    =>
      T1' <- subst_all env T1;
      ret (TLater T1')
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
       T2' <- subst_all env T2;
       t2' <- tm_subst_all env t2;
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

Lemma subst_all_nonTot_res_closed_rec:
  (forall v, forall i k env, Forall (vr_closed i k) env -> vr_closed (length env) k v ->
          exists v', vr_subst_all env v = Some v' /\
                vr_closed i k v') /\
  (forall T, forall i k env, Forall (vr_closed i k) env -> closed (length env) k T ->
          exists T', subst_all env T = Some T' /\
                closed i k T') /\
  (forall t, forall i k env, Forall (vr_closed i k) env -> tm_closed (length env) k t ->
          exists t', tm_subst_all env t = Some t' /\
                tm_closed i k t') /\
  (forall d, forall i k env, Forall (vr_closed i k) env -> dm_closed (length env) k d ->
          exists d', dm_subst_all env d = Some d' /\
                dm_closed i k d') /\
  (forall d, forall i k env, Forall (vr_closed i k) env -> dms_closed (length env) k d ->
          exists d', dms_subst_all env d = Some d' /\
                dms_closed i k d').
Proof.
  apply syntax_mutind; simpl; intros; inverts_closed;
    repeat
      match goal with
      | Hind : context [ ?f _ ?s ] , Hcl : _ (length _) ?k ?s |- context [ match ?f ?env ?s with _ => _ end ] =>
        lets (? & -> & ?): Hind i k env ___
      end;
    eauto using index_Forall.
Qed.

Lemma vr_subst_all_nonTot_res_closed:
  (forall v i k env, Forall (vr_closed i k) env -> forall (Hcl: vr_closed (length env) k v),
          exists v', vr_subst_all env v = Some v' /\
                vr_closed i k v').
Proof. unmut_lemma subst_all_nonTot_res_closed_rec. Qed.
Lemma subst_all_nonTot_res_closed:
  (forall T i k env, Forall (vr_closed i k) env -> forall (Hcl: closed (length env) k T),
          exists T', subst_all env T = Some T' /\
                closed i k T').
Proof. unmut_lemma subst_all_nonTot_res_closed_rec. Qed.
Lemma tm_subst_all_nonTot_res_closed:
  (forall t i k env, Forall (vr_closed i k) env -> forall (Hcl: tm_closed (length env) k t),
          exists t', tm_subst_all env t = Some t' /\
                tm_closed i k t').
Proof. unmut_lemma subst_all_nonTot_res_closed_rec. Qed.
Lemma dm_subst_all_nonTot_res_closed:
  (forall d i k env, Forall (vr_closed i k) env -> forall (Hcl: dm_closed (length env) k d),
          exists d', dm_subst_all env d = Some d' /\
                dm_closed i k d').
Proof. unmut_lemma subst_all_nonTot_res_closed_rec. Qed.
Lemma dms_subst_all_nonTot_res_closed:
  (forall d i k env, Forall (vr_closed i k) env -> forall (Hcl: dms_closed (length env) k d),
          exists d', dms_subst_all env d = Some d' /\
                dms_closed i k d').
Proof. unmut_lemma subst_all_nonTot_res_closed_rec. Qed.
Hint Resolve
     vr_subst_all_nonTot_res_closed
     subst_all_nonTot_res_closed
     tm_subst_all_nonTot_res_closed
     dm_subst_all_nonTot_res_closed
     dms_subst_all_nonTot_res_closed.

Definition evalToSome env e v k j :=
  (exists t', tm_subst_all (map VObj env) e = Some t' /\ steps t' v j) /\ irred v /\ j <= k.

Notation dmEnv_to_sigma env := (env_to_sigma (map VObj env)).

Definition evalToSomePar env e v k j :=
  steps (tm_subst_par (dmEnv_to_sigma env) e) v j /\ irred v /\ j <= k.

Lemma evalToSomeRes_closed: forall env e v n k j l,
    evalToSome env e v n j ->
    tm_closed l 0 e ->
    length env = l ->
    Forall (dms_closed k 1) env ->
    tm_closed k 0 v.
Proof.
  unfold evalToSome; intros; subst;
    assert (exists t', tm_subst_all (map VObj env) e = Some t' /\ tm_closed k 0 t')
    by (eapply tm_subst_all_nonTot_res_closed; try rewrite map_length; eauto); ev;
      optFuncs_det;
      eauto using steps_closed.
Qed.
Hint Resolve evalToSomeRes_closed.

Lemma evalToSomeParRes_closed: forall env e v n k j l,
    evalToSomePar env e v n j ->
    tm_closed l 0 e ->
    length env = l ->
    Forall (dms_closed k 1) env ->
    tm_closed k 0 v.
Proof.
  unfold evalToSomePar; intros; subst; ev;
    eapply steps_closed; eauto;
      eapply tm_subst_par_nonTot_res_closed; try rewrite map_length; eauto.
Qed.
Hint Resolve evalToSomeParRes_closed.

(*******************)
(* Prove irreducible closed terms evaluate to themselves (vl_evalToSome_self).
   We must first prove that substitution leaves them unchnaged. *)

Definition vr_env_id_par xs := forall n, env_to_sigma xs n = VarF n.
(* Define what's an identity substitution, through the required property (rather than through an inductive type). *)
Definition vr_env_id xs := forall n, n < length xs -> index n xs = Some (VarF n).

(* Allow proving vr_env_id. These lemmas could probably be the constructors for
   an inductive characterization. *)
Lemma nil_vr_env_id: vr_env_id [].
Proof. unfold vr_env_id; simpl; easy. Qed.

Lemma nil_vr_env_id_par: vr_env_id_par [].
Proof. red. reflexivity. Qed.

Lemma cons_vr_env_id: forall env, vr_env_id env -> vr_env_id (VarF (length env) :: env).
Proof. unfold vr_env_id; simpl; intros; case_match; beq_nat; subst; auto. Qed.

Lemma cons_vr_env_id_par: forall env, vr_env_id_par env -> vr_env_id_par (VarF (length env) :: env).
Proof. unfold vr_env_id_par; simpl; intros; better_case_match; beq_nat; auto. Qed.

Hint Resolve nil_vr_env_id cons_vr_env_id.
Hint Resolve nil_vr_env_id_par cons_vr_env_id_par.

(* Prove that an identity substitution is also an identity when lifted to our
   language syntax. *)
Lemma subst_closed_id_rec:
  (forall v i l env, vr_env_id env ->
              l = length env ->
              vr_closed l i v ->
              vr_subst_all env v = Some v) /\
  (forall T i l env, vr_env_id env ->
              l = length env ->
              closed l i T ->
              subst_all env T = Some T) /\
  (forall t i l env, vr_env_id env ->
              l = length env ->
              tm_closed l i t ->
              tm_subst_all env t = Some t) /\
  (forall d i l env, vr_env_id env ->
              l = length env ->
              dm_closed l i d ->
              dm_subst_all env d = Some d) /\
  (forall d i l env, vr_env_id env ->
              l = length env ->
              dms_closed l i d ->
              dms_subst_all env d = Some d).
Proof.
  apply syntax_mutind; simpl; intros; subst; inverts_closed;
    repeat
      match goal with
      | Hind : context [ ?f _ ?s ], Hcl : _ (length _) ?i ?s  |- context [ match ?f ?env ?s with _ => _ end ] =>
        lets ->: Hind i env ___
      end;
    eauto.
Qed.

Lemma vr_subst_closed_id:
  forall v i l env, vr_env_id env ->
              l = length env ->
              vr_closed l i v ->
              vr_subst_all env v = Some v.
Proof. unmut_lemma subst_closed_id_rec. Qed.
Lemma subst_closed_id:
  forall T i l env, vr_env_id env ->
               l = length env ->
               closed l i T ->
               subst_all env T = Some T.
Proof. unmut_lemma subst_closed_id_rec. Qed.
Lemma tm_subst_closed_id:
  forall t i l env,
    vr_env_id env ->
    l = length env ->
    tm_closed l i t ->
    tm_subst_all env t = Some t.
Proof. unmut_lemma subst_closed_id_rec. Qed.
Lemma dm_subst_closed_id:
  forall d i l env, vr_env_id env ->
              l = length env ->
              dm_closed l i d ->
              dm_subst_all env d = Some d.
Proof. unmut_lemma subst_closed_id_rec. Qed.
Lemma dms_subst_closed_id:
  forall d i l env, vr_env_id env ->
              l = length env ->
              dms_closed l i d ->
              dms_subst_all env d = Some d.
Proof. unmut_lemma subst_closed_id_rec. Qed.
Hint Resolve vr_subst_closed_id subst_closed_id tm_subst_closed_id dm_subst_closed_id dms_subst_closed_id.

Lemma subst_par_closed_id_rec:
  (forall v i l env, vr_env_id_par env ->
              l = length env ->
              vr_closed l i v ->
              vr_subst_par (env_to_sigma env) v = v) /\
  (forall T i l env, vr_env_id_par env ->
              l = length env ->
              closed l i T ->
              subst_par (env_to_sigma env) T = T) /\
  (forall t i l env, vr_env_id_par env ->
              l = length env ->
              tm_closed l i t ->
              tm_subst_par (env_to_sigma env) t = t) /\
  (forall d i l env, vr_env_id_par env ->
              l = length env ->
              dm_closed l i d ->
              dm_subst_par (env_to_sigma env) d = d) /\
  (forall d i l env, vr_env_id_par env ->
              l = length env ->
              dms_closed l i d ->
              dms_subst_par (env_to_sigma env) d = d).
Proof.
  apply syntax_mutind;
    simpl; intros; subst; inverts_closed; try f_equal; eauto.
Qed.

Lemma vr_subst_par_closed_id:
  forall v i l env, vr_env_id_par env ->
              l = length env ->
              vr_closed l i v ->
              vr_subst_par (env_to_sigma env) v = v.
Proof. unmut_lemma subst_par_closed_id_rec. Qed.
Lemma subst_par_closed_id:
  forall T i l env, vr_env_id_par env ->
               l = length env ->
               closed l i T ->
               subst_par (env_to_sigma env) T = T.
Proof. unmut_lemma subst_par_closed_id_rec. Qed.
Lemma tm_subst_par_closed_id:
  forall t i l env,
    vr_env_id_par env ->
    l = length env ->
    tm_closed l i t ->
    tm_subst_par (env_to_sigma env) t = t.
Proof. unmut_lemma subst_par_closed_id_rec. Qed.
Lemma dm_subst_par_closed_id:
  forall d i l env, vr_env_id_par env ->
              l = length env ->
              dm_closed l i d ->
              dm_subst_par (env_to_sigma env) d = d.
Proof. unmut_lemma subst_par_closed_id_rec. Qed.
Lemma dms_subst_par_closed_id:
  forall d i l env, vr_env_id_par env ->
              l = length env ->
              dms_closed l i d ->
              dms_subst_par (env_to_sigma env) d = d.
Proof. unmut_lemma subst_par_closed_id_rec. Qed.
Hint Resolve vr_subst_par_closed_id subst_par_closed_id tm_subst_par_closed_id dm_subst_par_closed_id dms_subst_par_closed_id.

Lemma tm_subst_closed_id_nil: forall t i, tm_closed 0 i t -> tm_subst_all [] t = Some t.
Proof. eauto. Qed.
Hint Resolve tm_subst_closed_id_nil.

Lemma tm_subst_par_closed_id_nil: forall t i, tm_closed 0 i t -> tm_subst_par (env_to_sigma []) t = t.
Proof. eauto. Qed.
Hint Resolve tm_subst_par_closed_id_nil.

Hint Constructors steps.

Lemma vl_evalToSome_self: forall v n i, irred v -> tm_closed 0 i v -> evalToSome [] v v n 0.
Proof. unfold evalToSome; intuition eauto. Qed.

Lemma vl_evalToSomePar_self: forall v n i, irred v -> tm_closed 0 i v -> evalToSomePar [] v v n 0.
Proof.
  unfold evalToSomePar; intuition (try erewrite tm_subst_par_closed_id_nil; eauto).
Qed.

Lemma evalToSome_det: forall env e k j1 j2 {v1} {v2},
    evalToSome env e v1 k j1 ->
    evalToSome env e v2 k j2 ->
    v1 = v2 /\ j1 = j2.
Proof. unfold evalToSome; intros; ev; optFuncs_det; eapply steps_irred_det; eauto. Qed.
Hint Resolve evalToSome_det.

Lemma evalToSomePar_det: forall env e k j1 j2 {v1} {v2},
    evalToSomePar env e v1 k j1 ->
    evalToSomePar env e v2 k j2 ->
    v1 = v2 /\ j1 = j2.
Proof. unfold evalToSomePar; intros; ev; eauto. Qed.
Hint Resolve evalToSomePar_det.

Lemma subst_all_upgrade_rec:
  (forall v v' env vx i l, vr_subst_all env v = Some v' ->
                    vr_closed l i v ->
                    length env = l ->
                    vr_subst_all (vx :: env) v = Some v') /\
  (forall T T' env vx i l, subst_all env T = Some T' ->
                    closed l i T ->
                    length env = l ->
                    subst_all (vx :: env) T = Some T') /\
  (forall t t' env vx i l, tm_subst_all env t = Some t' ->
                    tm_closed l i t ->
                    length env = l ->
                    tm_subst_all (vx :: env) t = Some t') /\
  (forall d d' env vx i l, dm_subst_all env d = Some d' ->
                    dm_closed l i d ->
                    length env = l ->
                    dm_subst_all (vx :: env) d = Some d') /\
  (forall d d' env vx i l, dms_subst_all env d = Some d' ->
                    dms_closed l i d ->
                    length env = l ->
                    dms_subst_all (vx :: env) d = Some d').
Proof.
  Ltac case_match_hp :=
    match goal with
    | H : context [ match ?x with _ => _ end ] |- _ =>
      destruct x eqn:?
    end.
  apply syntax_mutind; simpl; intros; inverts_closed; injectHyps;
    try solve [trivial | case_match; beq_nat; subst; omega || trivial];
    repeat case_match_hp; injectHyps; try discriminate;
      repeat match goal with
             | Hind : context [ ?f (_ :: _) ?s ] |- context [ match ?f (_ :: _) ?s with _ => _ end ] =>
               lets -> : Hind ___; eauto
             end.
Qed.

Lemma vr_subst_all_upgrade:
  forall v v' env vx i l, vr_subst_all env v = Some v' ->
                   vr_closed l i v ->
                   length env = l ->
                   vr_subst_all (vx :: env) v = Some v'.
Proof. unmut_lemma subst_all_upgrade_rec. Qed.
Lemma subst_all_upgrade:
  forall T T' env vx i l, subst_all env T = Some T' ->
                   closed l i T ->
                   length env = l ->
                   subst_all (vx :: env) T = Some T'.
Proof. unmut_lemma subst_all_upgrade_rec. Qed.
Lemma tm_subst_all_upgrade:
  forall t t' env vx i l, tm_subst_all env t = Some t' ->
                   tm_closed l i t ->
                   length env = l ->
                   tm_subst_all (vx :: env) t = Some t'.
Proof. unmut_lemma subst_all_upgrade_rec. Qed.
Lemma dm_subst_all_upgrade:
  forall d d' env vx i l, dm_subst_all env d = Some d' ->
                   dm_closed l i d ->
                   length env = l ->
                   dm_subst_all (vx :: env) d = Some d'.
Proof. unmut_lemma subst_all_upgrade_rec. Qed.
Lemma dms_subst_all_upgrade:
  forall d d' env vx i l, dms_subst_all env d = Some d' ->
                   dms_closed l i d ->
                   length env = l ->
                   dms_subst_all (vx :: env) d = Some d'.
Proof. unmut_lemma subst_all_upgrade_rec. Qed.

Hint Resolve vr_subst_all_upgrade subst_all_upgrade tm_subst_all_upgrade dm_subst_all_upgrade dms_subst_all_upgrade.

Lemma subst_par_upgrade_rec:
  (forall v v' env vx i l, vr_subst_par (env_to_sigma env) v = v' ->
                    vr_closed l i v ->
                    length env = l ->
                    vr_subst_par (env_to_sigma (vx :: env)) v = v') /\
  (forall T T' env vx i l, subst_par (env_to_sigma env) T = T' ->
                    closed l i T ->
                    length env = l ->
                    subst_par (env_to_sigma (vx :: env)) T = T') /\
  (forall t t' env vx i l, tm_subst_par (env_to_sigma env) t = t' ->
                    tm_closed l i t ->
                    length env = l ->
                    tm_subst_par (env_to_sigma (vx :: env)) t = t') /\
  (forall d d' env vx i l, dm_subst_par (env_to_sigma env) d = d' ->
                    dm_closed l i d ->
                    length env = l ->
                    dm_subst_par (env_to_sigma (vx :: env)) d = d') /\
  (forall d d' env vx i l, dms_subst_par (env_to_sigma env) d = d' ->
                    dms_closed l i d ->
                    length env = l ->
                    dms_subst_par (env_to_sigma (vx :: env)) d = d').
Proof.
  apply syntax_mutind; simpl; intros; inverts_closed; injectHyps; subst.
  all: try solve [f_equal; eauto | case_match; beq_nat; subst; omega || trivial ].
Qed.

Lemma vr_subst_par_upgrade:
  forall v v' env vx i l, vr_subst_par (env_to_sigma env) v = v' ->
                   vr_closed l i v ->
                   length env = l ->
                   vr_subst_par (env_to_sigma (vx :: env)) v = v'.
Proof. unmut_lemma subst_par_upgrade_rec. Qed.
Lemma subst_par_upgrade:
  forall T T' env vx i l, subst_par (env_to_sigma env) T = T' ->
                   closed l i T ->
                   length env = l ->
                   subst_par (env_to_sigma (vx :: env)) T = T'.
Proof. unmut_lemma subst_par_upgrade_rec. Qed.
Lemma tm_subst_par_upgrade:
  forall t t' env vx i l, tm_subst_par (env_to_sigma env) t = t' ->
                   tm_closed l i t ->
                   length env = l ->
                   tm_subst_par (env_to_sigma (vx :: env)) t = t'.
Proof. unmut_lemma subst_par_upgrade_rec. Qed.
Lemma dm_subst_par_upgrade:
  forall d d' env vx i l, dm_subst_par (env_to_sigma env) d = d' ->
                   dm_closed l i d ->
                   length env = l ->
                   dm_subst_par (env_to_sigma (vx :: env)) d = d'.
Proof. unmut_lemma subst_par_upgrade_rec. Qed.
Lemma dms_subst_par_upgrade:
  forall d d' env vx i l, dms_subst_par (env_to_sigma env) d = d' ->
                   dms_closed l i d ->
                   length env = l ->
                   dms_subst_par (env_to_sigma (vx :: env)) d = d'.
Proof. unmut_lemma subst_par_upgrade_rec. Qed.

Hint Resolve vr_subst_par_upgrade subst_par_upgrade tm_subst_par_upgrade dm_subst_par_upgrade dms_subst_par_upgrade.

Lemma subst_env: forall v v' env, tm_subst_all [] v = Some v' ->
                             tm_closed 0 0 v ->
                             tm_subst_all env v = Some v'.
Proof.
  specialize tm_subst_all_upgrade with (i := 0); induction env; intuition eauto.
Qed.
Hint Resolve subst_env.

Lemma subst_par_env: forall v v' env, tm_subst_par (env_to_sigma []) v = v' ->
                             tm_closed 0 0 v ->
                             tm_subst_par (env_to_sigma env) v = v'.
Proof.
  specialize tm_subst_par_upgrade with (i := 0); induction env; intuition eauto.
Qed.
Hint Resolve subst_par_env.
