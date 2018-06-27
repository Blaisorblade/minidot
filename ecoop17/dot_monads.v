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

Program Instance monadOptionOption : MonadError (fun A => option (option A)) :=
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

Definition step {A} (k : nat) (x: m A) : m A :=
  match x with
  | None => None
  | Some (v, k') => Some (v, k + k')
  end.

Program Instance monadOptionOptionNat : MonadError (* m *) (fun A => option ((option A) * nat)) :=
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

Solve Obligations with program_simplify;
  repeat case_match; try reflexivity;
    repeat fequalSafe; injectHyps;
      reflexivity || omega || discriminate.
