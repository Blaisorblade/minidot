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
Solve Obligations with
    intros; simpl; repeat case_match; reflexivity.

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
  (* refine (fun {A} x => ret (ret x)). *)
  (* refine (fun {A B} m f => *)
  (*             match m with *)
  (*             | None => None *)
  (*             | Some None => Some None *)
  (*             | Some (Some a) => f a *)
  (*             end). *)
  (* This definition typechecks but fails! *)
  (* - refine (fun {A B} m f => bind m (fun m' => bind m' (fun a => f a))). *)
Solve Obligations with
    intros; simpl_unfold_monad; repeat case_match; reflexivity.

Program Instance monadOptionOptionNat : MonadError (* m *) (fun A => option ((option A) * nat)) :=
  {
    error := fun {A} => ret (None, 0);
    ret := fun {A} x => ret (ret x, 0);
    (* ret := fun {A} x => Some (Some x); *)
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

Solve Obligations with
    intros; simpl_unfold_monad; repeat case_match;
    try injections_some; repeat fequalSafe;
      try (reflexivity || omega || discriminate).
