Require Import tactics.
Require Export dot_infrastructure_lemmas.

Require Export Arith.EqNat.
Require Export Arith.Le.

Inductive tm : Set :=
| tvar : id -> tm
| tabs : tm -> tm
| tapp : tm -> tm -> tm.

Inductive vl : Set :=
(* a closure for a lambda abstraction *)
| vabs : list vl (*H*) -> tm -> vl.

Inductive ty : Set :=
| TFun : ty -> ty -> ty
| TBase : ty.
                   
Notation tenv := (list ty).
Notation venv := (list vl).

Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.

Print indexr.
(* de Bruijn levels! *)
Inductive has_type: tenv -> tm -> ty -> Prop :=
| t_var : forall gamma x T,
    indexr x gamma = Some T ->
    has_type gamma (tvar x) T
| t_abs : forall gamma t S T,
    has_type (S :: gamma) t T ->
    has_type gamma (tabs t) (TFun S T)
| t_app : forall gamma f t S T,
    has_type gamma f (TFun S T) ->
    has_type gamma t S ->
    has_type gamma (tapp f t) T
.
Hint Constructors has_type.

Example ex1: has_type [TBase] (tvar 0) TBase. eauto. Qed.
Example ex2: has_type [TFun TBase TBase] (tabs (tvar 1)) (TFun TBase TBase). eauto. Qed.

Hint Extern 5 => match goal with
                | |- indexr _ _ = _ => progress cbn; eauto
                end.

Example ex__apply: has_type [TFun TBase TBase] (tabs (tabs (tapp (tvar 1) (tvar 2))))
                          (TFun (TFun TBase TBase) (TFun TBase TBase)). eauto 6. Qed.

(* Adapted from dot_monads.v *)
Require Import dot_monads.

Fixpoint tevalSM (t: tm) (n: nat) (env: venv): option (option vl * nat) :=
  match n with
  | 0 => None
  | S n =>
    match t with
    | tvar x       => ret (indexr x env, 0)
    (* | ttyp T       => ret (vty env T) *)
    | tabs y     => ret (vabs env y)
    | tapp tf ta   =>
      va <- tevalSM ta n env;
      vf <- tevalSM tf n env;
      match vf with
      (* | vty _ _ => error *)
      | vabs env2 tbody =>
        logStep 1 (tevalSM tbody n (va :: env2))
      end
    (* | tunpack tx ty => *)
    (*   vx <- tevalSM tx n env; *)
    (*   logStep 1 (tevalSM ty n (vx::env)) *)
    end
  end.

Fixpoint tevalS (t: tm) (n: nat) (env: venv): option (option vl * nat) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | tvar x       => Some (indexr x env, 0)
        (* | ttyp T       => Some (Some (vty env T), 0) *)
        | tabs y     => Some (Some (vabs env y), 0)
        | tapp ef ex   =>
          match tevalS ex n env with
            | None => None
            | Some (None, k1) => Some (None, k1)
            | Some (Some vx, k1) =>
              match tevalS ef n env with
                | None => None
                | Some (None, k2) => Some (None, k1 + k2)
                (* | Some (Some (vty _ _), k2) => Some (None, k1 + k2) *)
                | Some (Some (vabs env2 ey), k2) =>
                  logStep (k1 + k2 + 1) (tevalS ey n (vx::env2))
              end
          end
        (* | tunpack ex ey => *)
        (*   match tevalS ex n env with *)
        (*     | None => None *)
        (*     | Some (None, k) => Some (None, k) *)
        (*     | Some (Some vx, k1) => *)
        (*       logStep (k1 + 1) (tevalS ey n (vx::env)) *)
        (*   end *)
      end
  end.

Theorem evalMs_equiv: forall n env t, tevalSM t n env = tevalS t n env.
Proof.
  intros; revert env t; induction n; simpl_unfold_monad; unfold logStep; try reflexivity;
    intros;
    repeat
      (try better_case_match;
       injectHyps;
       repeat fequalSafe;
       repeat rewrite IHn in *;
       try (reflexivity || discriminate || omega)).
Qed.
Definition tevalSnmOpt env e optV k nm := forall n, n > nm -> tevalS e n env = Some (optV, k).
Definition tevalSnm env e v k nm := tevalSnmOpt env e (Some v) k nm.
Definition tevalSnOpt env e optV k := exists nm, tevalSnmOpt env e optV k nm.
Definition tevalSn env e v k := tevalSnOpt env e (Some v) k.

Hint Unfold tevalSnOpt tevalSnm tevalSn.
(* Hint Unfold tevalSnmOpt. *)
Ltac unfold2tevalSnmOpt := unfold tevalSn, tevalSnOpt, tevalSnm in *.

Lemma tevalSnmOpt_det: forall env t optV1 optV2 j1 j2 nm1 nm2,
    tevalSnmOpt env t optV1 j1 nm1 ->
    tevalSnmOpt env t optV2 j2 nm2 ->
    optV1 = optV2 /\ j1 = j2.
Proof.
  unfold tevalSnmOpt; intros * H1 H2; ev;
  remember (max (S nm1) (S nm2)) as nm;
  assert (nm > nm1) by (subst; eauto using Nat.le_max_l, Nat.le_max_r);
  assert (nm > nm2) by (subst; eauto using Nat.le_max_l, Nat.le_max_r).
  lets Hopt1 : H1 nm ___; eauto.
  lets Hopt2 : H2 nm ___; eauto.
  rewrite Hopt2 in Hopt1.
  injection Hopt1; intros; split_conj; eauto.
Qed.
Hint Resolve tevalSnmOpt_det.

(* Convince Coq that if n > m then n = S n' for some n', then there's enough
   fuel to perform one evaluation step. *)
Lemma n_to_Sn: forall n m, n > m -> exists n', n = S n'.
  intros; destruct n; [ exfalso; omega | eauto].
Qed.
Hint Unfold gt ge lt.
Ltac n_is_succ :=
  unfold gt, ge, lt in *;
  match goal with
  | [H : S ?m <= ?n |- _] =>
    apply n_to_Sn in H; let n' := fresh n in destruct H as [n' ->]
  end.
Tactic Notation "n_is_succ'" simple_intropattern(P) :=
  unfold gt, ge, lt in *;
  match goal with
  | [H : S ?m <= ?n |- _] =>
    apply n_to_Sn in H; destruct H as P
  end.

Ltac step_eval := n_is_succ; simpl in *.

(*******************)
(* Logical relation. *)

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Equations.Equations.

(*******************)
(* Define language infrastructure. *)

Definition vl_prop := vl -> Prop.
Hint Unfold vl_prop.

Fixpoint tsize (T: ty): nat :=
  match T with
  | TBase => 1
  | TFun T1 T2 => 1 + tsize T1 + tsize T2
  end.
Definition tsize_rel (T1 T2: ty) := tsize T1 < tsize T2.
Hint Extern 1 (tsize_rel _ _) => unfold tsize_rel; eauto.

Module strong_norm.
  Equations expr_sem0 (A : vl_prop) (t : tm) (env: venv): Prop :=
    expr_sem0 A t env :=
    exists v j,
      tevalSn env t v j /\ A v.

  (* Non-step-indexed reducibility *)
  Equations vtp0 (T: ty) (v : vl) : Prop :=
    vtp0 T t by rec T tsize_rel :=
      vtp0 TBase v := False;
                        vtp0 (TFun T1 T2) (vabs env body) := forall v, vtp0 T1 v -> expr_sem0 (fun v => vtp0 T2 v) body (v :: env).
  Next Obligation. Qed.
  Next Obligation. Qed.

  Example ex0 : vtp0 (TFun TBase TBase) (vabs [] (tvar 0)).
  Proof.
    simp vtp0; intros; simp expr_sem0; unfold2tevalSnmOpt; unfold tevalSnmOpt.
    repeat eexists; intros; try step_eval; eauto.
    Unshelve. exact 0.
  Qed.
End strong_norm.

Module LR_Type_Soundness.
(* Only expr_sem0 changes here. *)

(* Maybe make both normal definitions, or at least Program Definitions? Let's limit equations weird rules? *)
Definition expr_sem0 (A : vl_prop) (t : tm) (env: venv): Prop :=
  forall v j,
    tevalSn env t v j -> A v.

(* Non-step-indexed unary logical relation. *)
Equations vtp0 (T: ty) (v : vl) : Prop :=
  vtp0 T t by rec T tsize_rel :=
  vtp0 TBase v := False;
  vtp0 (TFun T1 T2) (vabs env body) := forall v, vtp0 T1 v -> expr_sem0 (fun v => vtp0 T2 v) body (v :: env).
Next Obligation. Qed.
Next Obligation. Qed.

Example ex0 : vtp0 (TFun TBase TBase) (vabs [] (tvar 0)).
Proof. simp vtp0; unfold expr_sem0; eauto. Qed.

Inductive R_env : venv -> tenv -> Set :=
  (* (env: venv) (G: tenv) : Set := *)
| R_nil :
    R_env [] []
| R_cons : forall T v env G,
    R_env env G ->
    vtp0 T v ->
    R_env (v :: env) (T :: G)
.

Lemma wf_length : forall vs ts,
                    R_env vs ts ->
                    (length vs = length ts).
Proof.
  intros * H; induction H; simpl; congruence.
Qed.

Hint Constructors R_env.

Program Definition etp0 T e env :=
  @expr_sem0 (fun v => vtp0 T v) e env.

(* Semantic typing *)
Definition sem_type (G : tenv) (T : ty) (e: tm) :=
  forall env,
    R_env env G ->
    etp0 T e env.

Lemma etp_vtp: forall e v j nm T env,
    tevalSnm env e v j nm -> etp0 T e env -> vtp0 T v.
Proof. unfold etp0 in *; intros; simp expr_sem0 in *; eauto. Qed.
Hint Resolve etp_vtp.

Ltac eval_det :=
  unfold2tevalSnmOpt; ev;
  match goal with
  | H1 : tevalSnmOpt _ _ _ _ _, H2 : tevalSnmOpt _ _ _ _ _ |- _ =>
    lets (? & ?) : tevalSnmOpt_det H1 H2 ___
  end; injectHyps.

Lemma vtp_etp: forall e v j nm T env,
    tevalSnm env e v j nm -> vtp0 T v -> etp0 T e env.
Proof. unfold etp0, expr_sem0 in *; intros; intros; eval_det; eauto. Qed.
Hint Resolve vtp_etp.

Lemma teval_var: forall env x,
  exists optV, tevalSnOpt env (tvar x) optV 0 /\ indexr x env = optV.
Proof.
  unfold2tevalSnmOpt; unfold tevalSnmOpt; eexists;
    split_conj; [exists 1 (* For nm *); intros; step_eval|idtac]; trivial.
Qed.
Hint Resolve teval_var.

Lemma fund_t_abs: forall G T1 T2 t,
  sem_type (T1 :: G) T2 t ->
  sem_type G (TFun T1 T2) (tabs t).
Proof.
  unfold sem_type; simpl; intros; intuition eauto.
  (* XXX needed: Lemma for syntactic values. *)
  (* Also needed: a way to swap goals that actually works! *)
  eapply vtp_etp with (nm := 0).
  - unfold2tevalSnmOpt; unfold tevalSnmOpt; intros; step_eval; trivial.
  - unfold etp0 in *; simp vtp0; eauto.
Qed.

(* XXX Most of the proof would be simplified by having appSubtermsEval. Prove them in mutual recursion? *)
Lemma tevalS_mono: forall n e env optV, tevalS e n env = Some optV -> forall m, m >= n -> tevalS e m env = Some optV.
Proof.
  induction n; intros * Heval * Hmn; try solve [inverse Heval].
  lets [m' ->]: n_to_Sn Hmn.
  generalize dependent optV.
  generalize dependent n.
  destruct e; auto; intros.
  -
    assert (m' >= n) as Hmn' by omega.
    simpl in *; unfold logStep in *.
    Ltac tevalS_det n m' IHn := match goal with
    | H1: tevalS ?e n ?env = Some ?r1, H2 : tevalS ?e m' ?env = ?r2 |- _ =>
      let H := fresh "H" in
      assert (tevalS e m' env = Some r1) as H by (eapply IHn; eauto);
        rewrite H in *; clear H; injectHyps; try discriminate
    end.
    repeat (better_case_match; subst; try discriminate; injectHyps; eauto); repeat tevalS_det n m' IHn; eauto.
Qed.

Lemma tevalS_mono_old: forall n e env optV, tevalS e n env = Some optV -> forall m, m >= n -> tevalS e m env = Some optV.
Proof.
  induction n; intros * Heval * Hmn; try solve [inverse Heval].
  lets [m' ->]: n_to_Sn Hmn.
  generalize dependent optV.
  generalize dependent n.
  destruct e; auto; intros.
  -
    assert (m' >= n) as Hmn' by omega.
    simpl in *; unfold logStep in *.

    assert (exists r, tevalS e2 n env = Some r) as [[optV2 j2] Hevaln2]. {
      (* This is the job of inv_mbind or similar? *)
      repeat better_case_match; subst; try discriminate; injectHyps; eauto.
    }

    (* Here auto uses the induction hypothesis! *)
    assert (tevalS e2 m' env = tevalS e2 n env) as -> by (rewrite Hevaln2; auto).
    rewrite Hevaln2 in *.

    (* Under the hypotheses, tevalS e1 can fail! We can dispose of that case easily: *)
    better_case_match; auto; subst.

    assert (exists r, tevalS e1 n env = Some r) as [[optV1 j1] Hevaln1]. {
      repeat better_case_match; subst; try discriminate; injectHyps; eauto.
    }
    (* Here auto uses the induction hypothesis! *)
    assert (tevalS e1 m' env = tevalS e1 n env) as -> by (rewrite Hevaln1; auto).
    rewrite Hevaln1 in *.

    unfold logStep in *.
    do 2 (better_case_match; auto).

    assert (exists optV0 j0, tevalS t n (v :: l) = Some (optV0, j0)) as [optV0 [j0 Hevaln0]]. {
      repeat better_case_match; subst; try discriminate; injectHyps; eauto.
    }
    assert (tevalS t m' (v :: l) = tevalS t n (v :: l)) as -> by (rewrite Hevaln0; auto).
    rewrite Hevaln0 in *; injectHyps; auto.
Qed.

Lemma appSubtermsEval: forall env t1 t2 v j,
    tevalSn env (tapp t1 t2) v j ->
    exists env1 tf j1 v2 j2 j3, tevalSn env t1 (vabs env1 tf) j1 /\ tevalSn env t2 v2 j2 /\ tevalSn (v2 :: env1) tf v j3.
Proof.
  unfold2tevalSnmOpt; unfold tevalSnmOpt in *.
  intros * [nm Hev].
  lets Hev2 : Hev (S nm) __; eauto. clear Hev.
  simpl in Hev2. unfold logStep in *.
  repeat better_case_match; subst; try discriminate; injectHyps.
  repeat eexists; firstorder eauto using tevalS_mono.
Qed.

Lemma fund_t_app: forall G T1 T2 t1 t2, sem_type G (TFun T1 T2) t1 -> sem_type G T1 t2 -> sem_type G T2 (tapp t1 t2).
Proof.
  unfold sem_type; simpl; intros * Hfun Harg * Henv.
  unfold etp0, expr_sem0 in *.
  intros * HappEv.

  pose proof appSubtermsEval _ _ _ _ _ HappEv as (env1 & tf & j1 & v2 & j2 & j3 & Heval1 & Heval2 & HevalV).

  specialize (Hfun env Henv _ _ Heval1).
  specialize (Harg env Henv _ _ Heval2).
  simp vtp0 in Hfun.
  (* unfold expr_sem0 in Hfun. *)
  eapply Hfun; eauto.
Qed.

Ltac lenG_to_lenEnv :=
  try match goal with
  | H: R_env ?env ?G |- _ =>
    replace (length G) with (length env) in * by (eauto using wf_length)
  end.

Lemma R_env_to_vtp0: forall G env x T v, indexr x G = Some T -> indexr x env = Some v -> R_env env G -> vtp0 T v.
Proof.
  intros * HT Hv Henv. induction Henv; simpl in *;
  [ discriminate |
    lenG_to_lenEnv;
    repeat (better_case_match; beq_nat); injectHyps; subst; eauto].
Qed.

Lemma fund_t_var: forall G x T, indexr x G = Some T -> sem_type G T (tvar x).
Proof.
  unfold sem_type, etp0, expr_sem0; unfold2tevalSnmOpt; intros.
  pose proof (teval_var env x); eval_det; subst.
  eapply R_env_to_vtp0; eauto. (* Or *)
  (* eauto 3 using R_env_to_vtp0. *)
Qed.

(* Fundamental property. Proved by induction on typing derivations. *)
Theorem fundamental: forall G t T, has_type G t T -> sem_type G T t.
Proof. intros * Htp; induction Htp; eauto using fund_t_var, fund_t_abs, fund_t_app. Qed.

End LR_Type_Soundness.
