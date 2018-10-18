(* Define simple monads that are useful for evaluation. w*)
Require Import tactics.

Class MonadError (M : Type -> Type) :=
  {
    error : forall {A}, M A;
    ret : forall {A} (a : A), M A;
    bind : forall {A B} (m : M A) (f : A -> M B), M B;
    left_unit : forall {A B} a (f : A -> M B), bind (ret a) f = f a;
    right_unit: forall {A} (m: M A), bind m ret = m;
    assoc : forall {A B C} (m: M A) (f : A -> M B) (g: B -> M C),
        bind m (fun x => bind (f x) g) = bind (bind m f) g
  }.

Notation "A >>= F" :=
  (bind A F)
    (at level 42, left associativity).

Notation "X '<-' A ';' B" :=
  (bind A (fun X => B))
    (at level 81, A at level 100, B at level 200, right associativity).

Program Instance monadOption : MonadError option :=
  {
    error := fun {A} => None;
    ret := fun {A} x => Some x;
    bind := fun {A B} m f =>
              match m with
              | None => None
              | Some a => f a
              end;
  }.

Solve Obligations with program_simplify;
  repeat case_match; reflexivity.

Ltac simpl_unfold_monad :=
  repeat (unfold ret, bind, error in *; simpl in *).

Definition optOpt A := option (option A).
Program Instance monadOptionOption : MonadError optOpt :=
  {
    error := fun {A} => ret None;
    ret := fun {A} x => @ret option _ _ (ret x);
    bind := (fun {A B} m f =>
              match m with
              | None => None
              | Some None => Some None
              | Some (Some a) => f a
              end)
  }.
Solve Obligations with program_simplify;
  repeat case_match; reflexivity.

(* XXX rename *)
Definition m A := (option (option A * nat)).

Definition timeout {A} : m A := None.

Definition logStep {A} (k : nat) (x: m A) : m A :=
  match x with
  | None => None
  | Some (v, k') => Some (v, k + k')
  end.

Definition optOptNat A := option (option A * nat).
Program Instance monadOptionOptionNat : MonadError optOptNat :=
  {
    error := fun {A} => ret (None, 0);
    ret := fun {A} x => ret (ret x, 0);
    bind := fun {A B} m f =>
              match m with
              | None => None
              | Some (None, k1) => ret (None, k1)
              | Some (Some a, k1) =>
                @bind option _ _ _
                      (f a)
                      (fun ob =>
                         match ob with
                           (b, k2) => ret (b, k1 + k2)
                         end
                      )
                (* ob <- f a; *)
                (* match ob with *)
                (*   (b, k2) => ret (b, k1 + k2) *)
                (* end *)
              end;
  }.
(* Proof. *)
(*   all: intros; *)
(*   simpl; *)
(*   repeat case_match; try reflexivity; *)
(*     repeat fequalSafe; injectHyps; *)
(*       reflexivity || omega || discriminate. *)
(* Defined. *)
Solve Obligations with program_simplify;
  repeat case_match; try reflexivity;
    repeat fequalSafe; injectHyps;
      reflexivity || omega || discriminate.


  (* refine (fun {A B} m f => *)
  (*             match m with *)
  (*             | None => None *)
  (*             | Some (None, k1) => ret (None, k1) *)
  (*             | Some (Some a, k1) => *)
  (*               ob <- f a; *)
  (*               match ob with *)
  (*                 (b, k2) => ret (b, k1 + k2) *)
  (*               end *)
  (*             end). *)
(* Program Instance monadOptionOptionNat : MonadError (* m *) (fun A => option ((option A) * nat)) := *)
(*   { *)
(*     error := fun {A} => ret (None, 0); *)
(*     ret := fun {A} x => ret (ret x, 0); *)
(*     bind := fun {A B} m f => *)
(*               match m with *)
(*               | None => None *)
(*               | Some (None, k1) => ret (None, k1) *)
(*               | Some (Some a, k1) => *)
(*                 @bind option _ _ _ *)
(*                       (f a) *)
(*                       (fun ob => *)
(*                          match ob with *)
(*                            (b, k2) => ret (b, k1 + k2) *)
(*                          end *)
(*                       ) *)
(*                 (* ob <- f a; *) *)
(*                 (* match ob with *) *)
(*                 (*   (b, k2) => ret (b, k1 + k2) *) *)
(*                 (* end *) *)
(*               end; *)
(*   }. *)
(*   (* refine (fun {A B} m f => *) *)
(*   (*             match m with *) *)
(*   (*             | None => None *) *)
(*   (*             | Some (None, k1) => ret (None, k1) *) *)
(*   (*             | Some (Some a, k1) => *) *)
(*   (*               ob <- f a; *) *)
(*   (*               match ob with *) *)
(*   (*                 (b, k2) => ret (b, k1 + k2) *) *)
(*   (*               end *) *)
(*   (*             end). *) *)

(* Lemma inv_succ_opt_bind: forall {X Y} (p : option X) (r : Y) f, *)
(*     (match p with None => None | Some x => f x end = Some r) -> *)
(*     exists v, p = Some v /\ f v = Some r. *)
(* Proof. intros; better_case_match_ex; eauto. Qed. *)

Lemma inv_succ_optP_bind: forall {X Y Z} (p : option (X * Y)) (r : Z) f,
    (match p with None => None | Some x => f x end = Some r) ->
    exists v1 v2, p = Some (v1, v2) /\ f (v1, v2) = Some r.
Proof. intros; better_case_match; discriminate || ev; eauto. Qed.

Tactic Notation "inv_mbind" simple_intropattern(P) := match goal with | H : _ = Some _ |- _ => eapply inv_succ_optP_bind in H as (? & P & ? & ?); injectHyps end.