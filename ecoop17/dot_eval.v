Require Import tactics.
Require Import dot_base.
Require Import dot_monads.

(* ### Evaluation (Big-Step Semantics) ### *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
Can use do-notation to clean up syntax.
*)
Fixpoint teval (t: tm) (n: nat) (env: venv): option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | tvar x       => Some (indexr x env)
        | ttyp T       => Some (Some (vty env T))
        | tabs T y     => Some (Some (vabs env T y))
        | tapp ef ex   =>
          match teval ex n env with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval ef n env with
                | None => None
                | Some None => Some None
                | Some (Some (vty _ _)) => Some None
                | Some (Some (vabs env2 _ ey)) =>
                  teval ey n (vx::env2)
              end
          end
        | tunpack ex ey =>
          match teval ex n env with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              teval ey n (vx::env)
          end
      end
  end.

Fixpoint tevalM (t: tm) (n: nat) (env: venv): option (option vl) :=
  match n with
  | 0 => None
  | S n =>
    match t with
    | tvar x       => ret (indexr x env)
    | ttyp T       => ret (vty env T)
    | tabs T y     => ret (vabs env T y)
    (* Fails equivalence with teval *)
    (* | tapp tf ta   => *)
    (*   vf <- tevalM tf n env; *)
    (*     match vf with *)
    (*     | vty _ _ => error *)
    (*     | vabs env2 _ tbody => *)
    (*       va <- tevalM ta n env; *)
    (*       tevalM tbody n (va :: env2) *)
    (*     end *)
    | tapp tf ta   =>
      va <- tevalM ta n env;
      vf <- tevalM tf n env;
      match vf with
      | vty _ _ => error
      | vabs env2 _ tbody =>
        tevalM tbody n (va :: env2)
      end
    | tunpack tx ty =>
      vx <- tevalM tx n env;
      tevalM ty n (vx::env)
    end
  end.

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

Theorem evals_equiv: forall n env t, tevalM t n env = teval t n env.
Proof.
  intros; revert env t; induction n; simpl_unfold_monad; try reflexivity;
    intros;
    repeat
      (try case_match;
       repeat rewrite IHn;
       try reflexivity).
Qed.

Definition tevaln env e v := exists nm, forall n, n > nm -> teval e n env = Some (Some v).

Fixpoint tevalSM (t: tm) (n: nat) (env: venv): option (option vl * nat) :=
  match n with
  | 0 => None
  | S n =>
    match t with
    | tvar x       => ret (indexr x env, 0)
    | ttyp T       => ret (vty env T)
    | tabs T y     => ret (vabs env T y)
    | tapp tf ta   =>
      va <- tevalSM ta n env;
      vf <- tevalSM tf n env;
      match vf with
      | vty _ _ => error
      | vabs env2 _ tbody =>
        logStep 1 (tevalSM tbody n (va :: env2))
      end
    | tunpack tx ty =>
      vx <- tevalSM tx n env;
      logStep 1 (tevalSM ty n (vx::env))
    end
  end.

Fixpoint tevalS (t: tm) (n: nat) (env: venv): option (option vl * nat) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | tvar x       => Some (indexr x env, 0)
        | ttyp T       => Some (Some (vty env T), 0)
        | tabs T y     => Some (Some (vabs env T y), 0)
        | tapp ef ex   =>
          match tevalS ex n env with
            | None => None
            | Some (None, k1) => Some (None, k1)
            | Some (Some vx, k1) =>
              match tevalS ef n env with
                | None => None
                | Some (None, k2) => Some (None, k1 + k2)
                | Some (Some (vty _ _), k2) => Some (None, k1 + k2)
                | Some (Some (vabs env2 _ ey), k2) =>
                  logStep (k1 + k2 + 1) (tevalS ey n (vx::env2))
              end
          end
        | tunpack ex ey =>
          match tevalS ex n env with
            | None => None
            | Some (None, k) => Some (None, k)
            | Some (Some vx, k1) =>
              logStep (k1 + 1) (tevalS ey n (vx::env))
            (* | res => res *)
          end
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
Definition tevalSnOpt env e optV k := exists nm, tevalSnmOpt env e optV k nm.
Definition tevalSnm env e v k nm := tevalSnmOpt env e (Some v) k nm.
Definition tevalSn env e v k := tevalSnOpt env e (Some v) k.
Definition tevalSn' env e v k := exists nm, tevalSnm env e v k nm.
Hint Unfold tevalSnmOpt tevalSnOpt tevalSnm tevalSn tevalSn'.

Lemma tevalSnEqv: forall env e v k, tevalSn env e v k = tevalSn' env e v k.
Proof. reflexivity. Qed.

(* Currently unused tactics and proof sketches on evaluation and its monotonicity. *)

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

(* Lemma tevalSnOpt_det: forall env t optV1 optV2 j1 j2, *)
(*     tevalSnOpt env t optV1 j1 -> *)
(*     tevalSnOpt env t optV2 j2 -> *)
(*     optV1 = optV2 /\ j1 = j2. *)
(* Proof. *)
(*   unfold tevalSnOpt; intros; ev; eauto using tevalSnmOpt_det. *)
(* Qed. *)

(* Ltac eval_det := *)
(*   match goal with *)
(*   | H1 : tevalSnmOpt _ _ _ _ _, H2 : tevalSnmOpt _ _ _ _ _ |- _ => *)
(*     lets (? & ?) : tevalSnmOpt_det H1 H2 ___ *)
(*   end. *)

(* Older variant: *)
(* Ltac eval_det := *)
(*   match goal with *)
(*   | H1 : tevalSnOpt _ _ ?a 0, H2 : tevalSnOpt _ _ ?b 0 |- _ => *)
(*     lets ? : tevalSnOpt_det H1 H2 ___ *)
(*   end; ev. *)

(* Require Import dot_monads. *)

(* XXX This tactic would belong in dot_monads.v, but it's only used here, and not working too well. *)

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
(*   repeat inv_mbind; injectHyps. *)

(* First try *)

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

(* Second try *)
(* Lemma tevalS_mono: forall n e env optV, tevalS e n env = Some optV -> forall m, m >= n -> tevalS e m env = Some optV. *)
(* Proof. *)
(*   induction n; intros * Heval * Hmn; try solve [inverse Heval]. *)
(*   lets [m' ->]: n_to_Sn Hmn. *)
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

(*     do 3 better_case_match; auto. *)
(*     unfold logStep in *. *)

(*     assert (exists optV0 j0, tevalS t0 n (v :: l) = Some (optV0, j0)) as [optV0 [j0 Hevaln0]] by admit. *)
(*     assert (tevalS t0 m' (v :: l) = tevalS t0 n (v :: l)) as -> by (rewrite Hevaln0; auto). *)
(*     rewrite Hevaln0 in *; injectHyps; auto. *)
(*   - *)
(*     assert (exists optV1, tevalS e1 n env = Some optV1) as [[optV1 j1] Hevaln1] by admit. *)
(*     simpl in *. *)
(*     assert (tevalS e1 m' env = tevalS e1 n env) as -> by (rewrite Hevaln1; auto). *)
(*     rewrite Hevaln1 in *. *)

(*     case_match; auto. *)
(*     unfold logStep in *. *)

(*     assert (exists optV2, tevalS e2 n (v::env) = Some optV2) as [[optV2 j2] Hevaln2] by admit. *)
(*     assert (tevalS e2 m' (v::env) = tevalS e2 n (v::env)) as -> by (rewrite Hevaln2; auto). *)
(*     rewrite Hevaln2 in *; injectHyps; auto. *)
(* Admitted. *)

(* Possible TODO: if such lemmas ever become relevant: prove as exercise that if
   `eval (tapp e1 e2)` succeeds, evaluating e1 and e2 succeeds. That should be
   an exercise on some tactic like inv_mbind. *)
