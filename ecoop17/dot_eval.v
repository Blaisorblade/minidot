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
Fixpoint teval(n: nat)(env: venv)(t: tm): option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | tvar x       => Some (indexr x env)
        | ttyp T       => Some (Some (vty env T))
        | tabs T y     => Some (Some (vabs env T y))
        | tapp ef ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vty _ _)) => Some None
                | Some (Some (vabs env2 _ ey)) =>
                  teval n (vx::env2) ey
              end
          end
        | tunpack ex ey =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              teval n (vx::env) ey 
          end
      end
  end.

Fixpoint tevalM (t: tm)(n: nat)(env: venv): option (option vl) :=
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

Theorem evals_equiv: forall n env t, tevalM t n env = teval n env t.
Proof.
  intros; revert env t; induction n; simpl_unfold_monad; try reflexivity;
    intros; 
    repeat
      (try case_match;
       repeat rewrite IHn;
       try reflexivity).
Qed.

(* XXX rename *)
Definition m A := (option (option A * nat)).

Definition timeout {A} : m A := None.

Check @bind.

Definition step {A} (k : nat) (x: m A) : m A :=
  match x with
  | None => None
  | Some (v, k') => Some (v, k + k')
  end.

(* Axiom fun_extensionality: *)
(*   forall (A B: Type) (f g: A -> B), *)
(*     (forall x, f x = g x) -> f = g. *)

Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* Definition opt_bind {A B : Type} (a : option A) (f : A -> option B) : option B := *)
(*   match a with *)
(*     | Some x => f x *)
(*     | None => None *)
(*   end. *)

(* Definition mbind {A B} (x: m A) (f: A -> m B) : m B := *)
(*   match x with *)
(*   | Some (v, n) => *)
(*     step n (opt_bind v f) *)
(*   | None => None *)
(*   end. *)

Fixpoint tevalM2 (t: tm)(n: nat)(env: venv): option (option vl * nat) :=
  match n with
  | 0 => None
  | S n => 
    match t with
    | tvar x       => ret (indexr x env, 0)
    | ttyp T       => ret (vty env T)
    | tabs T y     => ret (vabs env T y)
    | tapp tf ta   =>
      va <- tevalM2 ta n env;
      vf <- tevalM2 tf n env;
      match vf with
      | vty _ _ => error
      | vabs env2 _ tbody =>
        step 1 (tevalM2 tbody n (va :: env2))
      end
    | tunpack tx ty =>
      vx <- tevalM2 tx n env;
      step 1 (tevalM2 ty n (vx::env))
    end
  end.

Fixpoint teval' (t: tm)(n: nat)(env: venv){struct n}: option (option vl * nat) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | tvar x       => Some (indexr x env, 0)
        | ttyp T       => Some (Some (vty env T), 0)
        | tabs T y     => Some (Some (vabs env T y), 0)
        | tapp ef ex   =>
          match teval' ex n env with
            | None => None
            | Some (None, k1) => Some (None, k1)
            | Some (Some vx, k1) =>
              match teval' ef n env with
                | None => None
                | Some (None, k2) => Some (None, k1 + k2)
                | Some (Some (vty _ _), k2) => Some (None, k1 + k2)
                | Some (Some (vabs env2 _ ey), k2) =>
                  step (k1 + k2 + 1) (teval' ey n (vx::env2))
              end
          end
        | tunpack ex ey =>
          match teval' ex n env with
            | None => None
            | Some (None, k) => Some (None, k)
            | Some (Some vx, k1) =>
              step (k1 + 1) (teval' ey n (vx::env))
            (* | res => res *)
          end
      end
  end.

Theorem evalMs_equiv: forall n env t, tevalM2 t n env = teval' t n env.
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
