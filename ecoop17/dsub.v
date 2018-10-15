(* WIP on some mixture of D<: and Lillibridge's calculus, but for strong
   normalization of impredicative translucent sums. *)
Require Export tactics.
Require Export dot_infrastructure_lemmas.
Require Export dot_monads.

Require Export Arith.EqNat.
Require Export Arith.Le.

(* term variables occurring in types *)
Inductive var : Set :=
| varF : id -> var (* free *)
| varB : id -> var (* locally-bound variable *)
.

Inductive closed_var: nat(*B*) -> nat(*F*) -> var -> Prop :=
| closed_varB : forall i j x,
    j > x -> closed_var i j (varF x)
| closed_varF : forall i j x,
    i > x -> closed_var i j (varB x).

Hint Constructors var closed_var.

Ltac inverts_closed_var :=
  match goal with
  | H : closed_var _ _ _ |- _ => inverts H
  end.

Definition open_var_rec (k: nat) (u: var) (v: var) : var :=
  match v with
  | varF x => varF x
  | varB i => if beq_nat k i then u else (varB i)
  end.

Lemma closed_var_upgrade_both: forall t i i1 k k1, closed_var i k t -> i <= i1 -> k <= k1 -> closed_var i1 k1 t.
Proof. intros; inverts_closed_var; eauto. Qed.
Hint Extern 5 (closed_var _ _ _) => try_once closed_var_upgrade_both.

(** Types. Work-in-progress mixture of D<: and Lillibridge's calculus. The goal is to limit the amount of constructors. *)
Inductive ty : Set :=
| TNat : ty
(* (z: S) -> T^z *)
| TAll : ty -> ty -> ty
(* x.Type *)
| TSel : var -> ty
(* x.Type = T (from bounding transformation) *)
| TSelA : var -> ty -> ty
(* Existentials Exists X. U^X are encodable in D<: as:
iota {x: {type T} /\ U^x}
we first add this directly.
 *)
(* Single-field version of Lillibridge's opaque sum *)
| TBind  : ty -> ty (* Recursive binder: iota{ z => {Type} /\ T^z },
                       where z is locally bound in T *)
(* Single-field version of Lillibridge's transparent sum *)
| TSBind : ty -> ty -> ty
                       (* iota {z : {Type = T} /\ U^z}*)
(* Beware that T may not refer to z. Enabling such references would enable encoding
   proper recursive types and break strong normalization (Wang and Rompf 2017,
   Sec. 4.2); for that, we'd need to enforce (strong?) positivity or
   guardedness.
   In our model, values inhabiting such types would have to be recursive, which we don't support.
 *)
.

Inductive closed_ty: nat(*B*) -> nat(*F*) -> ty -> Prop :=
| cl_nat: forall i j,
    closed_ty i j TNat
| cl_all: forall i j T1 T2,
    closed_ty i j T1 ->
    closed_ty (S i) j T2 ->
    closed_ty i j (TAll T1 T2)
| cl_sel: forall i j x,
    closed_var i j x ->
    closed_ty i j (TSel x)
| cl_sela: forall i j x T,
    closed_var i j x ->
    closed_ty i j T ->
    closed_ty i j (TSelA x T)
| cl_bind: forall i j U,
    closed_ty (S i) j U ->
    closed_ty i j (TBind U)
| cl_sbind: forall i j T U,
    closed_ty i j T ->
    closed_ty (S i) j U ->
    closed_ty i j (TSBind T U)
.

Hint Constructors ty closed_ty.

(* Search ((?A -> ?B) -> list ?A -> list ?B). *)
(* Search ((?A -> ?B) -> option ?A -> option ?B). *)
Fixpoint open_ty_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
  | TNat        => TNat
  | TAll T1 T2  => TAll (open_ty_rec k u T1) (open_ty_rec (S k) u T2)
  | TSel x  => TSel (open_var_rec k u x)
  | TSelA x T => TSelA (open_var_rec k u x) (open_ty_rec k u T)
  | TBind U => TBind (open_ty_rec (S k) u U)
  | TSBind T U => TSBind (open_ty_rec k u T) (open_ty_rec (S k) u U)
  end.

Notation open := (open_ty_rec 0).

Ltac inverts_closed_ty :=
  lazymatch goal with
  | H : closed_ty _ _ ?T  |- _ =>
    tryif is_var T then fail else inverts H
  end.

(** Tactic to split lemmas proven using mutual induction into their separate parts. *)
(* Ltac unmut_lemma H := destruct H; ev; eauto. *)

Lemma closed_ty_upgrade_both:
  forall T i i1 k k1, closed_ty i k T -> i <= i1 -> k <= k1 -> closed_ty i1 k1 T.
Proof. induction T; intros; inverts_closed_ty; eauto. Qed.

Hint Extern 5 (closed_ty _ _ _) => try_once closed_ty_upgrade_both.

(* XXX True facts, not the statements we care about. Drop. *)
(* Lemma closed_var_open: forall i j k x y, *)
(*   closed_var i j x -> closed_var i (S j) y -> closed_var i (S j) (open_var_rec k y x). *)
(* Proof. intros * Hx Hy; inverts Hx; simpl; better_case_match_ex; eauto. Qed. *)
(* Lemma closed_open: forall T i j k x, *)
(*   closed_ty i j T -> closed_var i (S j) x -> closed_ty i (S j) (open_ty_rec k x T). *)
(* Proof. *)
(*   induction T; intros; inverts_closed_ty; simpl; eauto using closed_var_open, closed_var_upgrade_both. *)
(* Qed. *)

Lemma closed_var_open: forall v i j x,
  closed_var (S i) j v -> closed_var i j x -> closed_var i j (open_var_rec i x v).
Proof. intros * Hv Hx; inverts Hv; simpl; better_case_match_ex; eauto. Qed.
Hint Resolve closed_var_open.

Lemma closed_ty_open:
  forall T i j x, closed_ty (S i) j T -> closed_var i j x -> closed_ty i j (open_ty_rec i x T).
Proof. induction T; intros; inverts_closed_ty; simpl; eauto. Qed.
Hint Resolve closed_ty_open.

Inductive tm : Set :=
| tvar : id -> tm
| tabs : tm -> tm
(* Recursive function *)
| trec : tm -> tm
| tapp : tm -> tm -> tm
| tlet : tm -> tm -> tm
| tnat : nat -> tm
(* An encoded existential *)
| tpack : ty -> tm -> tm
| tproj : tm -> tm
.
Hint Constructors tm.

Reserved Notation "'venv'".
Inductive vl : Set :=
(* a closure for a lambda abstraction *)
| vabs : venv -> tm -> vl
(* a closure for a recursive function *)
| vrec : venv -> tm -> vl
| vnat: nat -> vl
| vpack : venv -> ty -> vl -> vl
where
"'venv'" := (list vl).
Hint Constructors vl.

Notation tenv := (list ty).

Hint Extern 5 => match goal with
                | |- indexr _ _ = _ => progress cbn
                end.

(* de Bruijn levels! *)
Inductive stp: tenv -> ty -> ty -> Prop :=
| s_bind : forall G T U,
    stp G (TSBind T U) (TBind U)
| s_tsela1 : forall x T G,
    stp G (TSelA x T) T
| s_tsela2 : forall x T G,
    stp G T (TSelA x T)
| s_tsel1 : forall x T U G,
    indexr x G = Some (TSBind T U) ->
    stp G (TSel (varF x)) T
| s_tsel2 : forall x T U G,
    indexr x G = Some (TSBind T U) ->
    stp G T (TSel (varF x))
.
(** Beware stp does not satisfy regularity! *)

(** [ann] indexes derivation to indicate whether kind annotations in TSel are required or not. *)
Inductive ann := Ann | NoAnn.

(** The boolean says if this is recursive. *)
Inductive has_type: bool -> ann -> tenv -> tm -> ty -> Prop :=
| t_var : forall b a G x T,
    indexr x G = Some T ->
    has_type b a G (tvar x) T
| t_abs : forall b a G t S T,
    has_type b a (S :: G) t T ->
    has_type b a G (tabs t) (TAll S T)
| t_rec : forall b a G t S T,
    has_type b a (S :: TAll S T :: G) t T ->
    has_type true a G (trec t) (TAll S T)
| t_app : forall b a G f t S T,
    has_type b a G f (TAll S T) ->
    has_type b a G t S ->
    has_type b a G (tapp f t) T
| t_let : forall b a G e1 e2 S T,
    has_type b a G e1 S ->
    has_type b a (S :: G) e2 T ->
    has_type b a G (tlet e1 e2) T
| t_nat: forall b a G n, has_type b a G (tnat n) TNat
| t_pack_transparent : forall b a G T U t,
    has_type b a (TSBind T U :: G) t (open (varF (length G)) U) ->
    has_type b a G (tpack T t) (TSBind T U)
(* | t_pack_opaque : forall b a G T U t, *)
(*     has_type b a (TSBind T U :: G) t U -> *)
(*     has_type b a G (tpack T t) (TBind U) *)
| t_sub : forall T b a G t U,
    stp G T U ->
    has_type b a G t T ->
    has_type b a G t U
| t_proj: forall b a G x T T',
    has_type b a G (tvar x) (TBind T) ->
    open (varF x) T = T' ->
    has_type b a G (tproj (tvar x)) T'
| t_sel_sing : forall b G x t T U,
    indexr x G = Some (TSBind T U) ->
    (* This premise is more general but even less syntax-directed. *)
    (* has_type b a G t T -> *)
    has_type b NoAnn G t T ->
    has_type b NoAnn G t (TSel (varF x))
| t_sel_ann : forall b G x t T U,
    indexr x G = Some (TSBind T U) ->
    (* This premise is more general but even less syntax-directed. *)
    (* has_type b a G t T -> *)
    has_type b Ann G t T ->
    has_type b Ann G t (TSelA (varF x) T)
.

Hint Constructors has_type ann.
Hint Resolve s_bind.
Hint Resolve s_tsela1 s_tsela2 s_tsel1 s_tsel2: tsel_red.

(* *)
Hint Extern 5 => match goal with | |- context [open _ _] => progress cbn end.
Example ex_pack3: has_type false NoAnn [] (tpack TNat (tnat 0)) (TBind (TSel (varB 0))).
eauto 6.
Qed.
Example ex_pack3expl: has_type false NoAnn [] (tpack TNat (tnat 0)) (TSBind TNat (TSel (varB 0))).
eauto 6.
Qed.

Notation "'{_:' A '/\' B '}'" := (TSBind A B).
Notation "x '.T'" := (TSel x) (at level 20).
Notation "x '.T' '::' U" := (TSelA x U) (at level 10).

Example ex_pack3expla: has_type false Ann [] (tpack TNat (tnat 0)) (TSBind TNat (TSelA (varB 0) TNat)).
eauto 4 with tsel_red.
(* Restart. *)
(* (* info eauto: *) *)
(* simple apply t_pack_transparent. *)
(* simple eapply t_sub. *)
(* simpl. *)
(* simple apply s_tsela2. *)
(* simple apply t_nat. *)
(* Restart. *)
(* eauto 6. *)
(* Restart. *)
(* (* info eauto: *) *)
(* simple apply t_pack_transparent. *)
(* cbn. *)
(* simple eapply t_sel_ann. *)
(* cbn. *)
(* simple apply @eq_refl. *)
(* simple apply t_nat. *)
Qed.

Example ex_pack3a: has_type false Ann [] (tpack TNat (tnat 0)) (TBind (TSelA (varB 0) TNat)). eauto 6. Qed.

Example ex_projpacka: has_type false Ann [] (tlet (tpack TNat (tnat 0)) (tproj (tvar 0))) TNat.
solve [eauto 8 using ex_pack3expla with tsel_red].
(* Restart. *)
(* eapply t_let. *)
(* exact ex_pack3expla. *)
(* eauto 7 with tsel_red. *)
(* Restart. *)
(* eapply t_let. *)
(* exact ex_pack3expla. *)

(* (* info eauto: *) *)
(* simple eapply t_sub. *)
(* simple apply s_tsela1. *)
(* simple eapply t_proj. *)
(* simple eapply t_sub. *)
(* simple apply s_bind. *)
(* simple apply t_var. *)
(* cbn. *)
(* simple apply @eq_refl. *)
(* cbn. *)
(* simple apply @eq_refl. *)
Qed.

(* Bad *)
Example ex_projpackbad: has_type false Ann [] (tlet (tpack TNat (tnat 0)) (tproj (tvar 0))) (TSelA (varF 0) TNat).
solve [eauto 6 using ex_pack3expla].
(* Restart. *)

(* (* info eauto: *) *)
(* simple eapply t_let. *)
(* exact ex_pack3expla. *)
(* simple eapply t_proj. *)
(* simple eapply t_sub. *)
(* simple apply s_bind. *)
(* simple apply t_var. *)
(* cbn. *)
(* simple apply @eq_refl. *)
(* simple apply @eq_refl. *)
Qed.

Example ex_projpack: has_type false NoAnn [] (tlet (tpack TNat (tnat 0)) (tproj (tvar 0))) TNat.
solve [eauto 9 using ex_pack3expl, (s_tsel1 0)].
(* Restart. *)
(* (* solve [eauto 8 using ex_pack3expl with tsel_red]. *) *)
(* (* Fail solve [eauto 9 using ex_pack3expl with tsel_red]. *) *)
(* eapply t_let. *)
(* eapply ex_pack3expl. *)
(* (* eauto with tsel_red. *) *)

(* eapply t_sub. *)
(* eapply (s_tsel1 0); eauto. *)
(* eauto. *)
Qed.

Example ex_pack2_bad: has_type false NoAnn [] (tpack TNat (tnat 0)) (TBind TNat). eauto. Qed.
(* XXX Fishy. *)
Example ex_pack2: has_type false NoAnn [] (tpack TNat (tnat 0)) (TBind (TSel (varF 0))). eauto 8. Qed.
Example clo_ex3: closed_ty 0 0 (TBind (TSel (varB 0))). eauto. Qed.
Example clo_ex2: closed_ty 0 0 (TBind (TSel (varF 0))). eauto. Fail Qed. Abort.

(* Example ex_pack1: exists T, has_type false NoAnn [] (tpack TNat (tnat 0)) T. eauto 10. Qed. *)
(* Print ex_pack1. *)

Example ex1: has_type false NoAnn [TNat] (tvar 0) TNat. eauto. Qed.
Example ex2: has_type false NoAnn [TAll TNat TNat] (tabs (tvar 1)) (TAll TNat TNat). eauto. Qed.

Example ex__apply: has_type false NoAnn [TAll TNat TNat] (tabs (tabs (tapp (tvar 1) (tvar 2))))
                          (TAll (TAll TNat TNat) (TAll TNat TNat)). eauto 7. Qed.

Lemma has_type_nonrec_to_rec: forall t G T a (Ht: has_type false a G t T), has_type true a G t T.
Proof. intros; induction Ht; eauto. Qed.

Fixpoint tsize_ty (T: ty): nat :=
  match T with
  | TNat => 1
  | TAll T1 T2 => 1 + tsize_ty T1 + tsize_ty T2
  | TSel x => 1
  | TSelA x T => 1 + tsize_ty T
  | TBind U => 1 + tsize_ty U
  | TSBind T U => 1 + tsize_ty T + tsize_ty U
  end.

Definition tsize_ty_rel := fun T1 T2 => tsize_ty T1 < tsize_ty T2.
Hint Unfold tsize_ty_rel.

Definition tsize_ty_rel2 := MR lt tsize_ty.

Lemma tsize_ty_eq: tsize_ty_rel = (fun T1 T2 => tsize_ty T1 < tsize_ty T2).
Proof. reflexivity. Qed.

Lemma wf_tsize_ty_rel : well_founded tsize_ty_rel.
Proof. apply (measure_wf lt_wf). Qed.
Hint Resolve wf_tsize_ty_rel.

Lemma open_preserves_size: forall T v j,
    tsize_ty (open_ty_rec j v T) = tsize_ty T.
Proof. induction T; intros; simpl; eauto. Qed.
Hint Extern 5 (_ < tsize_ty _) =>
  rewrite open_preserves_size.

Require Import Equations.Equations.
(* Instance wflt: WellFounded lt. typeclass. Qed. *)
Equations annot_ty (G: tenv) (T: ty) : option ty :=
  annot_ty G T by rec T tsize_ty_rel :=
    annot_ty G TNat := ret TNat;
    annot_ty G (TAll T U) :=
      T' <- (annot_ty G T);
      U' <- (annot_ty (T :: G) (open (varF (length G)) U));
      (* U' <- (annot_ty (T :: G) U); *)
      ret (TAll T' U');
    annot_ty G (TSelA x T) :=
      T' <- (annot_ty G T);
      ret (TSelA x T');
    annot_ty G (TSBind T U) :=
      T' <- (annot_ty G T);
      U' <- (annot_ty (TSBind T U :: G) (open (varF (length G)) U));
      ret (TSBind T' U');
    annot_ty G (TBind U) :=
      U' <- (annot_ty (TBind U :: G) (open (varF (length G)) U));
      ret (TBind U');
    annot_ty G (TSel (varF x)) :=
      T0 <- indexr x G;
      match T0 with
      | TSBind T _ =>
        (* Here we could just return T, TSelA is needed when we have bounded types *)
        ret (TSelA (varF x) T)
      | _ =>
        ret (TSel (varF x))
      end;
    annot_ty G (TSel (varB x)) := None.
Solve All Obligations with program_simpl.

Lemma tsize_ind : forall T (P: ty -> Prop),
    (forall T,
        (forall T', tsize_ty_rel T' T -> P T') -> P T) ->
    P T.
Proof. intros; eapply well_founded_ind; eauto. Qed.

Lemma indexr_exists : forall X vs n,
                       n < length vs ->
                       exists (T:X), indexr n vs = Some T.
Proof. induction vs; simpl; intros; try omega; better_case_match_ex; eauto. Qed.
Hint Resolve indexr_exists.

Lemma closed_annot_total:
  forall T G, closed_ty 0 (length G) T -> exists T', annot_ty G T = Some T'.
Proof.
  induction T using tsize_ind; intros; destruct T; inverts_closed_ty; try inverts_closed_var; simp annot_ty in *; eauto; try omega;
  try solve [repeat lazymatch goal with
  | |- context [annot_ty ?G ?T] =>
    let T' := fresh "T" in
    lets [T' ->] : H T G __; simpl; eauto
  end].
  - edestruct indexr_exists as [T' ->]; eauto; simpl; better_case_match_ex; omega || eauto.
Qed.
(* XXX but we never *close* those damn types. *)
Hint Resolve closed_annot_total.

Fixpoint annot_tenv (G: tenv) : option tenv :=
  match G with
  | [] => ret []
  | T :: G =>
    G' <- annot_tenv G;
    T' <- annot_ty G' T;
    ret (T' :: G')
  end.


Lemma has_type_noann_to_ann: forall t G T b (Ht: has_type b NoAnn G t T),
    closed_ty 0 (length G) T ->
    exists G' T', annot_tenv G = Some G' /\ annot_ty G' T = Some T' /\
    has_type b Ann G' t T'.
    (* exists G' T', has_type b Ann G' t T'. *)
Proof.
  (* intros; induction Ht; ev; eauto 10. *)
  (* ev; repeat eexists; try constructors; eauto. *)
  (* admit. *)
  (* eapply closed_annot_total. *)
  (*      eapply H. *)
  (*      ev; eexists. eapply t_rec. eapply H. *)
  (*      all: ev; eexists; constructors; eauto 10. eapply H. eexists. eauto. Qed. *)
Abort.

Definition rename (sigma: id -> id): tm -> tm :=
  fix go (t: tm) {struct t}: tm :=
    match t with
    | tvar n => tvar (sigma n)
    | tabs t => tabs (go t)
    | trec t => trec (go t)
    | tapp t1 t2 => tapp (go t1) (go t2)
    | tlet t1 t2 => tlet (go t1) (go t2)
    | tnat n => tnat n
    | tpack T t => tpack T (* XXX*) (go t)
    | tproj t => tproj (go t)
    end.
Definition wk n' := rename (fun n => n + n').

Lemma indexr_succ_wk: forall {X} i (G G': list X) r, indexr i G = Some r -> indexr (i + length G') (G ++ G') = Some r.
Proof.
  intros; induction G; simpl in *; try discriminate;
  rewrite app_length; repeat better_case_match_ex; eauto; omega.
Qed.

(* Require Import Setoid. *)
(* (* Stolen from https://github.com/coq/coq/issues/3814, and dangerous, but enable setoid_rewrite using equalities on the goal. *) *)
(* Instance subrelation_eq_impl : subrelation eq impl. congruence. Qed. *)
(* Instance subrelation_eq_flip_impl : subrelation eq (flip impl). congruence. Qed. *)

(** Simplifies next proof. *)
Lemma indexr_fail_eq: forall {X} i (G: list X), (indexr i G = None) <-> (i >= length G).
Proof.
  intros.
  split; intros; gen i; induction G; simpl; intros; eauto.
  - better_case_match_ex; assert (i >= length G) by eauto; omega.
  - better_case_match_ex; eauto 2; omega.
Qed.

(* Unused *)
Lemma indexr_fail_wk: forall {X} i (G G': list X), indexr i G = None -> indexr (i + length G') (G ++ G') = None.
Proof.
  (* Really manual proof: *)
  intros * H.
  (** Translate the problem to an inequality on lengths. *)
  eapply indexr_fail_eq; eapply indexr_fail_eq in H.
  (** Then solve it. *)
  rewrite app_length; omega.
Qed.

Lemma indexr_wk: forall {X} i (G G': list X) r, indexr i G = r -> indexr (i + length G') (G ++ G') = r.
  destruct r; eauto using indexr_succ_wk, indexr_fail_wk. Qed.
Hint Resolve indexr_wk.

Lemma indexr_wk_eq: forall {X} i (G G': list X), indexr i G = indexr (i + length G') (G ++ G').
  intros; erewrite indexr_wk; eauto.
Qed.

(* Lemma wk_has_type: forall t b a G T, has_type b a G t T -> forall G', has_type b a (G ++ G') (wk (length G') t) T. *)
(* Proof. *)
(*   intros * Ht; induction Ht; simpl; *)
(*     (* Construct a new typing derivation (typing is *not* syntax-directed, so econstructor is good enough for this. )*) *)
(*     econstructor; *)
(*     (* Rearrange goals in context to match the inductive hypothesis. *) *)
(*     repeat rewrite app_comm_cons; eauto using indexr_succ_wk. *)
(* Qed. *)

(*******************************)
(** Evaluation and properties. *)

(* Adapted from dot_eval.v *)

(* Fixpoint tevalSM (t: tm) (n: nat) (env: venv): option (option vl * nat) := *)
(*   match n with *)
(*   | 0 => None *)
(*   | S n => *)
(*     match t with *)
(*     | tvar x       => ret (indexr x env, 0) *)
(*     (* | ttyp T       => ret (vty env T) *) *)
(*     | tabs y     => ret (vabs env y) *)
(*     | trec y     => ret (vrec env y) *)
(*     | tnat n     => ret (vnat n) *)
(*     | tapp tf ta   => *)
(*       va <- tevalSM ta n env; *)
(*       vf <- tevalSM tf n env; *)
(*       match vf with *)
(*       | vabs env2 tbody => *)
(*         tevalSM tbody n (va :: env2) *)
(*       | vrec env2 tbody => *)
(*         logStep 1 (tevalSM tbody n (va :: vf :: env2)) *)
(*       | _ => error *)
(*       end *)
(*     | tlet t1 t2 => *)
(*       v1 <- tevalSM t1 n env; *)
(*       (* Omit counting an extra step, since this let is not recursive! *) *)
(*       tevalSM t2 n (v1 :: env) *)
(*     (* | tunpack tx ty => *) *)
(*     (*   vx <- tevalSM tx n env; *) *)
(*     (*   logStep 1 (tevalSM ty n (vx::env)) *) *)
(*     end *)
(*   end. *)

(* Fixpoint tevalS (t: tm) (n: nat) (env: venv): option (option vl * nat) := *)
(*   match n with *)
(*     | 0 => None *)
(*     | S n => *)
(*       match t with *)
(*         | tvar x       => Some (indexr x env, 0) *)
(*         (* | ttyp T       => Some (Some (vty env T), 0) *) *)
(*         | tabs y     => Some (Some (vabs env y), 0) *)
(*         | trec y     => Some (Some (vrec env y), 0) *)
(*         | tnat n     => Some (Some (vnat n), 0) *)
(*         | tapp ef ex   => *)
(*           match tevalS ex n env with *)
(*             | None => None *)
(*             | Some (None, k1) => Some (None, k1) *)
(*             | Some (Some vx, k1) => *)
(*               match tevalS ef n env with *)
(*                 | None => None *)
(*                 | Some (None, k2) => Some (None, k1 + k2) *)
(*                 | Some (Some vf, k2) => *)
(*                   match vf with *)
(*                   | vabs env2 ey => logStep (k1 + k2) (tevalS ey n (vx::env2)) *)
(*                   | vrec env2 ey => logStep (k1 + k2 + 1) (tevalS ey n (vx::vf::env2)) *)
(*                   | _ => Some (None, k1 + k2) *)
(*                   end *)
(*               end *)
(*           end *)
(*         | tlet e1 e2 => *)
(*           match tevalS e1 n env with *)
(*           | None => None *)
(*           | Some (None, k1) => Some (None, k1) *)
(*           | Some (Some v1, k1) => *)
(*             (* logStep (k1 + 1) *) *)
(*             logStep k1 (tevalS e2 n (v1 :: env)) *)
(*           end *)

(*         (* | tunpack ex ey => *) *)
(*         (*   match tevalS ex n env with *) *)
(*         (*     | None => None *) *)
(*         (*     | Some (None, k) => Some (None, k) *) *)
(*         (*     | Some (Some vx, k1) => *) *)
(*         (*       logStep (k1 + 1) (tevalS ey n (vx::env)) *) *)
(*         (*   end *) *)
(*       end *)
(*   end. *)

(* Theorem evalMs_equiv: forall n env t, tevalSM t n env = tevalS t n env. *)
(* Proof. *)
(*   intros; revert env t; induction n; simpl_unfold_monad; unfold logStep; try reflexivity; *)
(*     intros; *)
(*     repeat progress *)
(*       (try better_case_match_ex; *)
(*        repeat fequalSafe; *)
(*        repeat rewrite IHn in *; *)
(*        try abstract (reflexivity || discriminate || omega)). *)
(* Qed. *)
(* (** Define "evaluation with enough fuel". *)
(*     We can show that adding more fuel to evaluation that doesn't time out gives *)
(*     the same result. But we can also build that in our assumptions. *)
(*  *) *)
(* Definition tevalSnmOpt env e optV k nm := forall n, n > nm -> tevalS e n env = Some (optV, k). *)
(* Definition tevalSnm env e v k nm := tevalSnmOpt env e (Some v) k nm. *)
(* Definition tevalSnOpt env e optV k := exists nm, tevalSnmOpt env e optV k nm. *)
(* Definition tevalSn env e v k := tevalSnOpt env e (Some v) k. *)

(* Hint Transparent tevalSnOpt tevalSnm tevalSn. *)
(* Ltac unfold2tevalSnmOpt := unfold tevalSn, tevalSnOpt, tevalSnm in *. *)
(* Ltac unfoldTeval := unfold2tevalSnmOpt; unfold tevalSnmOpt in *. *)

(* Ltac n_is_succ_hp := *)
(*   ev; match goal with *)
(*   | H : forall n, n > ?nm -> _ |- _ => *)
(*     let H2 := fresh "H" in *)
(*     lets ? : H (S nm) __; eauto; clear H; simpl in H2; try unfold logStep in H2 *)
(*   end. *)

(* (** [tevalSnmOpt] (expanded) is monotonic relative to [nm]. This does not *)
(*     follow from properties of [tevalS], but by construction of [tevalSnmOpt]. *) *)
(* Lemma tevalS_kripke_mono: forall env e optV k nm1, *)
(*     (forall n, n > nm1 -> tevalS e n env = Some (optV, k)) -> *)
(*     forall nm2, nm2 >= nm1 -> *)
(*     forall n, n > nm2 -> tevalS e n env = Some (optV, k). *)
(* Proof. eauto. Qed. *)
(* Hint Resolve tevalS_kripke_mono. *)

(* (** [tevalSnmOpt] is monotonic relative to [nm]. This does not follow from *)
(*     properties of [tevalS], but by construction of [tevalSnmOpt]. *) *)
(* Lemma tevalSnmOpt_mono: forall env e optV k nm1, *)
(*     tevalSnmOpt env e optV k nm1 -> *)
(*     forall nm2, nm2 >= nm1 -> *)
(*     tevalSnmOpt env e optV k nm2. *)
(* Proof. intros; unfoldTeval; eauto using tevalS_kripke_mono. Qed. *)

(* Lemma max_bigger_both: forall n1 n2, max n1 n2 >= n1 /\ max n1 n2 >= n2. *)
(*   intuition eauto using Nat.le_max_l, Nat.le_max_r. *)
(* Qed. *)

(* Ltac alignTevalAssumptions := *)
(*   unfoldTeval; *)
(*   match goal with *)
(*   | H1 : forall n, n > ?nm1 -> tevalS ?t n ?env = Some ?t1 , H2 : forall n, n > ?nm2 -> tevalS ?t n ?env = Some ?t2 |- _ => *)
(*     let nm := fresh "nm" in *)
(*     remember (max (nm1) (nm2)) as nm; *)
(*     assert (nm >= nm1 /\ nm >= nm2) as (? & ?) by (subst; eauto using max_bigger_both); *)
(*     assert (tevalSnmOpt env t (fst t1) (snd t1) nm) by (simpl; unfoldTeval; eauto); *)
(*     assert (tevalSnmOpt env t (fst t2) (snd t2) nm) by (simpl; unfoldTeval; eauto); *)
(*     clear H1 H2; *)
(*     unfoldTeval *)
(*   end. *)

(* Lemma tevalS_det: forall optV1 optV2 env t j1 j2 nm1 nm2, *)
(*   (forall n : nat, n > nm1 -> tevalS t n env = Some (optV1, j1)) -> *)
(*   (forall n : nat, n > nm2 -> tevalS t n env = Some (optV2, j2)) -> *)
(*   optV1 = optV2 /\ j1 = j2. *)
(* Proof. *)
(*   intros; alignTevalAssumptions; *)
(*     repeat n_is_succ_hp; optFuncs_det; eauto. *)
(* Qed. *)

(* (* Experiment on different way of writing tevalS_det: can we make auto happier about injecting p1 = p2 than splitting it? *) *)
(* Lemma tevalS_det2: forall optV1 optV2 env t j1 j2 nm1 nm2, *)
(*   (forall n : nat, n > nm1 -> tevalS t n env = Some (optV1, j1)) -> *)
(*   (forall n : nat, n > nm2 -> tevalS t n env = Some (optV2, j2)) -> *)
(*   (optV1, j1) = (optV2, j2). *)
(* Proof. *)
(*   intros; alignTevalAssumptions; *)
(*     repeat n_is_succ_hp; optFuncs_det; eauto. *)
(* Qed. *)

(* Tactic Notation "try_once_tac" constr(T) tactic(tac) := *)
(*   match goal with *)
(*   | H : usedLemma T |- _ => fail 1 *)
(*   | _ => markUsed T; tac *)
(*   end. *)

(* Definition injectHyps_marker := 0. *)
(* Hint Extern 5 => try_once_tac injectHyps_marker injectHyps. *)
(* (* Hint Extern 5 => optFuncs_det. *) *)

(* (* XXX this used tevalS_detp, the next uses _det, seems _detp might not be that useful here yet... *) *)
(* Lemma tevalS_det_optV: forall optV1 optV2 env t j1 j2 nm1 nm2, *)
(*   (forall n : nat, n > nm1 -> tevalS t n env = Some (optV1, j1)) -> *)
(*   (forall n : nat, n > nm2 -> tevalS t n env = Some (optV2, j2)) -> *)
(*   optV1 = optV2. *)
(* Proof. intros. lets ?: tevalS_det2 optV1 optV2 ___; eauto. Qed. *)

(* (* Hint Extern 5 => ev. *) *)

(* Lemma tevalS_det_j: forall optV1 optV2 env t j1 j2 nm1 nm2, *)
(*   (forall n : nat, n > nm1 -> tevalS t n env = Some (optV1, j1)) -> *)
(*   (forall n : nat, n > nm2 -> tevalS t n env = Some (optV2, j2)) -> *)
(*   j1 = j2. *)
(* Proof. intros; lets ?: tevalS_det optV1 optV2 ___; ev; eauto. Qed. *)

(* Hint Resolve tevalS_det_optV tevalS_det_j. *)

(* Lemma tevalSnmOpt_det_optV: forall env t optV1 optV2 j1 j2 nm1 nm2, *)
(*     tevalSnmOpt env t optV1 j1 nm1 -> *)
(*     tevalSnmOpt env t optV2 j2 nm2 -> *)
(*     optV1 = optV2. *)
(* Proof. (* firstorder eauto. (* Or: *) *) intros; unfoldTeval; eauto. Qed. *)

(* Lemma tevalSnmOpt_det_j: forall env t optV1 optV2 j1 j2 nm1 nm2, *)
(*     tevalSnmOpt env t optV1 j1 nm1 -> *)
(*     tevalSnmOpt env t optV2 j2 nm2 -> *)
(*     j1 = j2. *)
(* Proof. unfoldTeval; eauto. Qed. *)

(* Hint Resolve tevalSnmOpt_det_optV tevalSnmOpt_det_j. *)

(* Lemma tevalSnmOpt_det: forall env t optV1 optV2 j1 j2 nm1 nm2, *)
(*     tevalSnmOpt env t optV1 j1 nm1 -> *)
(*     tevalSnmOpt env t optV2 j2 nm2 -> *)
(*     optV1 = optV2 /\ j1 = j2. *)
(* Proof. eauto. Qed. *)

(* (* Convince Coq that if n > m then n = S n' for some n', then there's enough *)
(*    fuel to perform one evaluation step. *) *)
(* Lemma n_to_Sn: forall n m, n > m -> exists n', n = S n'. *)
(*   intros; destruct n; [ exfalso; omega | eauto]. *)
(* Qed. *)
(* Hint Unfold gt ge lt. *)
(* Hint Transparent gt ge lt. *)

(* Tactic Notation "n_is_succ'" simple_intropattern(P) := *)
(*   unfold gt, ge, lt in *; *)
(*   match goal with *)
(*   | [H : S ?m <= ?n |- _] => lets [P ->]: n_to_Sn H *)
(*   end. *)

(* Ltac n_is_succ := let n' := fresh "n" in n_is_succ' n'. *)

(* Ltac step_eval := n_is_succ; simpl in *. *)
(* (* Hint Extern 5 => step_eval. *) *)

(* Lemma inv_tevalS: forall t n env r, tevalS t n env = Some r -> exists n', n = S n'. *)
(* Proof. intros; destruct n; discriminate || eauto. Qed. *)

(* Ltac inv_tevalS := *)
(*   lazymatch goal with *)
(*   | H : tevalS _ ?n _ = Some _ |- _ => *)
(*     let n' := fresh n in *)
(*     lets (n' & ->) : inv_tevalS H *)
(*   end. *)


(* Lemma teval_var: forall env x, *)
(*   exists optV, tevalSnOpt env (tvar x) optV 0 /\ indexr x env = optV. *)
(* Proof. unfoldTeval; eexists; split_conj; try exists 0; intros; try step_eval; trivial. Qed. *)
(* Hint Resolve teval_var. *)

(* Ltac eval_det := *)
(*   unfold2tevalSnmOpt; ev; *)
(*   match goal with *)
(*   | H1 : tevalSnmOpt _ _ _ _ _, H2 : tevalSnmOpt _ _ _ _ _ |- _ => *)
(*     lets (? & ?) : tevalSnmOpt_det H1 H2 ___ *)
(*   end; injectHyps. *)

(* (** Fuel monotonicity: If evaluation does not time out, increasing fuel preserves the result. *)
(*  **** Proof sketch. *)
(*       By induction on the available fuel [n] in the initial evaluation and case *)
(*       analysis on terms. *)

(*       In the inductive step, recursive calls happen with fuel [n - 1], hence by *)
(*       the induction hypothesis they satisfy fuel monotonicity, the recursive *)
(*       calls with more fuel give the same result, hence overall evaluation with *)
(*       more fuel gives the same result. *)
(*  *) *)
(* Lemma tevalS_mono: forall n e env optV, tevalS e n env = Some optV -> forall m, m >= n -> tevalS e m env = Some optV. *)
(* Proof. *)
(*   (** [tevalS_det] applies the induction hypothesis to recursive calls. *) *)
(*   Ltac tevalS_det n m' IHn := *)
(*     match goal with *)
(*     | H1: tevalS ?e n ?env = Some ?r1, H2 : tevalS ?e m' ?env = ?r2 |- _ => *)
(*       let H := fresh "H" in *)
(*       assert (tevalS e m' env = Some r1) as H by (eapply IHn; auto 1); *)
(*       rewrite H in *; clear H *)
(*     end. *)

(*   induction n; intros * Heval * Hmn; try solve [inverse Heval]; *)
(*   n_is_succ' m'; *)

(*   generalize dependent optV; generalize dependent n; destruct e; *)
(*     intros; simpl in *; unfold logStep in *; *)
(*     trivial; *)

(*   repeat (better_case_match_ex; try tevalS_det n m' IHn); trivial. *)
(* Qed. *)
(* Hint Resolve tevalS_mono. *)

(* (**********************) *)
(* (** Logical relation. *) *)

(* Require Import Coq.Relations.Relation_Operators. *)
(* (* Require Export Coq.Wellfounded.Lexicographic_Product. *) *)

(* (*******************) *)
(* (* Define language infrastructure. *) *)

(* Definition vl_prop := vl -> Prop. *)
(* Hint Unfold vl_prop. *)

(* Module Type vtp_arg. *)
(*   Parameter vtp : ty -> vl_prop. *)
(*   Parameter expr_sem : vl_prop -> tm -> venv -> Prop. *)
(* End vtp_arg. *)

(* Module Envs (VTP: vtp_arg). *)
(*   Import VTP. *)

(*   (* Copy-pasted and modularizable. *) *)
(*   Inductive R_env : venv -> tenv -> Set := *)
(*   | R_nil : *)
(*       R_env [] [] *)
(*   | R_cons : forall T v env G, *)
(*       R_env env G -> *)
(*       vtp T v -> *)
(*       R_env (v :: env) (T :: G). *)
(*   Hint Constructors R_env. *)

(*   Lemma wf_length : forall vs ts, *)
(*       R_env vs ts -> *)
(*       (length vs = length ts). *)
(*   Proof. intros * H; induction H; simpl; congruence. Qed. *)

(*   Ltac lenG_to_lenEnv := *)
(*     try match goal with *)
(*         | H: R_env ?env ?G |- _ => *)
(*           replace (length G) with (length env) in * by (eauto using wf_length) *)
(*         end. *)

(*   Lemma R_env_to_indexr_success: forall G env x T, indexr x G = Some T -> R_env env G -> exists v, indexr x env = Some v. *)
(*     intros * HT Henv; induction Henv; simpl in *; *)
(*       tryfalse; *)
(*       lenG_to_lenEnv; better_case_match_ex; eauto. *)
(*   Qed. *)
(*   Hint Resolve R_env_to_indexr_success. *)

(*   Lemma R_env_to_vtp: forall G env x T v, indexr x G = Some T -> indexr x env = Some v -> R_env env G -> vtp T v. *)
(*   Proof. *)
(*     intros * HT Hv Henv; induction Henv; simpl in *; *)
(*       [ discriminate | *)
(*         lenG_to_lenEnv; *)
(*         repeat (better_case_match; beq_nat); eauto]. *)
(*   Qed. *)
(*   Hint Resolve R_env_to_vtp. *)
(*   (* Copy-pasted and modularizable, until at least here. *) *)

(*   Definition etp T e env := *)
(*     expr_sem (fun v => vtp T v) e env. *)

(*   (* Semantic typing *) *)
(*   Definition sem_type (G : tenv) (T : ty) (e: tm) := *)
(*     forall env, *)
(*       R_env env G -> *)
(*       etp T e env. *)

(*   Definition sem_vl_subtype (G : tenv) (T1 T2: ty) := *)
(*     (* wf G T1 /\ *) *)
(*     (* wf G T2 /\ *) *)
(*     (* forall env, *) *)
(*     (*   R_env env G -> *) *)
(*     forall v, vtp T1 v -> vtp T2 v. *)

(*   Definition sem_subtype (G : tenv) (T1 T2: ty) := *)
(*     (* wf G T1 /\ *) *)
(*     (* wf G T2 /\ *) *)
(*     sem_vl_subtype G T1 T2 /\ *)
(*     forall env, *)
(*       R_env env G -> *)
(*       forall e, etp T1 e env -> etp T2 e env. *)

(*   Lemma subtype_to_vl_subtype : forall G T1 T2, *)
(*       sem_subtype G T1 T2 -> sem_vl_subtype G T1 T2. *)
(*   Proof. unfold sem_subtype; tauto. Qed. *)
(*   Hint Resolve subtype_to_vl_subtype. *)

(* End Envs. *)
