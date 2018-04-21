Require Import dot_base.
Require Import dot_monads.
Require Import tactics.

(* ### Evaluation (Big-Step Semantics) ### *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
Could use do-notation to clean up syntax.
*)
(* TODO: Step-index this semantics, following the step-indexing by Rompf. *)
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
        step 1 (tevalSM tbody n (va :: env2))
      end
    | tunpack tx ty =>
      vx <- tevalSM tx n env;
      step 1 (tevalSM ty n (vx::env))
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
                  step (k1 + k2 + 1) (tevalS ey n (vx::env2))
              end
          end
        | tunpack ex ey =>
          match tevalS ex n env with
            | None => None
            | Some (None, k) => Some (None, k)
            | Some (Some vx, k1) =>
              step (k1 + 1) (tevalS ey n (vx::env))
            (* | res => res *)
          end
      end
  end.

Theorem evalMs_equiv: forall n env t, tevalSM t n env = tevalS t n env.
Proof.
  intros; revert env t; induction n; simpl_unfold_monad; unfold step; try reflexivity;
    intros;
    repeat
      (try case_match;
       try injections_some;
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

Require Import LibTactics.
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

Lemma tevalSnOpt_det: forall env t optV1 optV2 j1 j2,
    tevalSnOpt env t optV1 j1 ->
    tevalSnOpt env t optV2 j2 ->
    optV1 = optV2 /\ j1 = j2.
Proof.
  unfold tevalSnOpt; intros; ev; eauto using tevalSnmOpt_det.
Qed.

Ltac eval_det :=
  match goal with
  | H1 : tevalSnOpt _ _ ?a 0, H2 : tevalSnOpt _ _ ?b 0 |- _ =>
    lets ? : tevalSnOpt_det H1 H2 ___
  end; ev.

