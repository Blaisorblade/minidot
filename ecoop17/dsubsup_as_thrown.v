Require Import dsubsup_as.

Module MutualCBVFails.

  Inductive term :=
  | app (s t : term)
  | val (v : value)
  with value :=
  | var (x : var)
  | lam (b : {bind value in term}).

End MutualCBVFails.

Module MutualCBVWorks.
  Inductive term_of {T} :=
  | app (s t : term_of)
  | val (v : T).

  Inductive value :=
  | var (x : var)
  | lam (b : {bind value in @term_of value}).

  Section MMapTermOf.
    Variable (A B : Type).
    Variable (MMap_A_B : MMap A B).
    Variable (MMapLemmas_A_B : MMapLemmas A B).
    Variable (MMapExt_A_B : MMapExt A B).

    Global Instance mmap_term_of : MMap A (@term_of B). derive. Defined.
    Global Instance mmapLemmas_term_of : MMapLemmas A (@term_of B). derive. Qed.
    Global Instance mmapExt_term_of : MMapExt A (@term_of B). derive. Defined.
  End MMapTermOf.

  Instance Ids_value : Ids value. derive. Defined.
  Instance Rename_value : Rename value. derive. Defined.
  Instance Subst_value : Subst value. derive. Defined.
  Instance SubstLemmas_value : SubstLemmas value. derive. Qed.
  Print Ids_value.
  Print Rename_value.

  Definition test : value :=
    lam (app (val (var 0)) (val (var 1))).
  Compute test.[ren (+1)].
End MutualCBVWorks.

(* Definition mmap_gen_ty_of : forall {A B}, (A -> B) -> @ty_of A -> @ty_of B := fun f T => *)
Class Lens s t a b := lens : (a -> b) -> s -> t.
(* Definition mmap_gen_ty_of {A B} (f : A -> B) : @ty_of A -> @ty_of B := *)
Instance lens_ty_of : forall {a b}, Lens (@ty_of a) (@ty_of b) a b := fun {a b} f =>
  fix go T :=
    match T with
    | TTop => TTop
    | TBot => TBot
    | TAll a b => TAll (go a) (go b)
    | TSel x => TSel x
    | TMem s u => TMem (go s) (go u)
    | TBind T => TBind (go T)
    | TAnd A B => TAnd (go A) (go B)
    end.

  (* (MMap_A_B : MMap A B). *)
  (* (* Global Instance mmap_ty_of : MMap A (@ty_of B). derive. Defined. *) *)
  (* Global Instance mmap_gen_ty_of : MMapGen A (@ty_of B). *)
Section mmap_ty_of.
  Variable (A B : Type).
  Variable (MMap_A_B : MMap A B).
  (* Global Instance mmap_ty_of : MMap A (@ty_of B). derive. Defined. *)
  Global Instance mmap_ty_of_bad : MMap A (@ty_of B).  derive. Defined.
  Print mmap_ty_of_bad.
  Set Printing Implicit.
  Print mmap_ty_of_bad.
  (* Global Instance mmap_ty_of : MMap A (@ty_of B) := @mmap_gen_ty_of A A. (@ty_of B). *)
  (* unfold MMap. *)
  (* derive. Defined. *)
  (* refine (fun f => _). *)
  (* intro T. *)
  (* destruct  *)
  Print mmap_ty_of.


  Variable (MMapLemmas_A_B : MMapLemmas A B).
  Variable (MMapExt_A_B : MMapExt A B).

Compute (MMap A (@ty_of B)).
  Global Instance mmapLemmas_ty_of : MMapLemmas A (@ty_of B). derive. Qed.
  Global Instance mmapExt_ty_of : MMapExt A (@ty_of B). derive. Defined.
End mmap_ty_of.

Check @mmap. (* @mmap : forall A B : Type, MMap A B -> (A -> A) -> B -> B *)
Check @rename. 
(* @rename : forall term : Type, Rename term -> (var -> var) -> term -> term *)
(* Instance Rename_ty2: Rename ty := *)
(*   fix dummy (xi : var -> var) (s : ty) {struct s} : ty := *)
(*   match s as t return (annot ty t) with *)
(*   | TTop => TTop *)
(*   | TBot => TBot *)
(*   | TAll _b s0 => TAll (mmap (rename xi) _b) (rename xi s0) *)
(*   | TSel v => TSel (xi v) *)
(*   | TMem s1 s2 => TMem (rename xi s1) (rename xi s2) *)
(*   | TBind _b => TBind (mmap (rename xi) _b) *)
(*   | TAnd s1 s2 => TAnd (rename xi s1) (rename xi s2) *)
(*   end. *)
(*      (* : Rename ty *) *)