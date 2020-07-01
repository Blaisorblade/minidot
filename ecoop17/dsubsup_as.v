Require Export Autosubst.Autosubst.

(* Follow ideas from https://github.com/uds-psl/autosubst/issues/4 on D_{<:>}. *)

(* Inductive ty_of {T}: Type := *)
(* | TTop : ty_of *)
(* | TBot : ty_of *)
(* (* (z: T) -> T^z *) *)
(* | TAll : ty_of -> {bind T in ty_of} -> ty_of *)
(* (* x.Type *) *)
(* | TSel : T -> ty_of *)
(* (* { Type: S..U } *) *)
(* | TMem : ty_of (*S*) -> ty_of (*U*) -> ty_of *)
(* | TBind  : {bind T in ty_of} -> ty_of (* Recursive binder: { z => T^z }, *)
(*                          where z is locally bound in T *) *)
(* | TAnd : ty_of -> ty_of -> ty_of (* Intersection Type: T1 /\ T2 *) *)
(* . *)
(* (* Set Printing Implicit. *) *)
(* (* Print ty_of. *) *)

(* Reserved Notation "'ty'". *)

(* Inductive vl : Type := *)
(* (* x -- free variable, matching concrete environment *) *)
(* | vvar : var -> vl *)
(* (* { Type = T } *) *)
(* | vtyp : ty -> vl *)
(* (* lambda x:T.t *) *)
(* | vabs : ty -> {bind vl in tm} -> vl *)
(* with tm : Type := *)
(* | tvl : vl -> tm *)
(* (* t t *) *)
(* | tapp : tm -> tm -> tm *)
(* where "'ty'" := (@ty_of vl). *)

Inductive ty: Type :=
| TTop : ty
| TBot : ty
(* (z: T) -> T^z *)
| TAll : ty -> {bind vl in ty} -> ty
(* x.Type *)
| TSel : vl -> ty
(* { Type: S..U } *)
| TMem : ty (*S*) -> ty (*U*) -> ty
| TBind  : {bind vl in ty} -> ty (* Recursive binder: { z => T^z },
                         where z is locally bound in T *)
| TAnd : ty -> ty -> ty (* Intersection Type: T1 /\ T2 *)
with vl : Type :=
(* x -- free variable, matching concrete environment *)
| vvar : var -> vl
(* { Type = T } *)
| vtyp : ty -> vl
(* lambda x:T.t *)
| vabs : ty -> {bind vl in tm} -> vl
with tm : Type :=
| tvl : vl -> tm
(* t t *)
| tapp : tm -> tm -> tm
.

Notation tvar x := (tvl (vvar x)).
Notation ttyp T := (tvl (vtyp T)).
Notation tabs T t := (tvl (vabs T t)).

Eval simpl in (tabs TTop (tvar 0)).

Set Printing Implicit.
(* Instance Rename_vl_bad: Rename vl. derive. Defined. *)
(* Print Rename_vl_bad. *)
(* Program Definition man_rename_vl := *)
(*   fix govl (xi: var -> var) (s: vl) {struct s}: vl := *)
(*   match s with *)
(*   | vvar v => vvar (xi v) *)
(*   | vtyp t => vtyp (@rename ty _ xi t) *)
(*   | vabs tau t => vabs (@rename ty _ xi tau) (@rename tm _ (upren xi) t) *)
(*   end *)
(* with gotm (xi: var -> var) (s: tm) {struct s}: tm := *)
(*   (* man_rename_tm (xi: var -> var) (s: tm) {struct s}: tm := *) *)
(*   match s with *)
(*   | tvl v => tvl (govl xi v) *)
(*   | tapp s1 s2 => tapp (gotm xi s1) (gotm xi s2) *)
(*   end for govl. *)
(* Next Obligation. Admitted. *)
(* Next Obligation. Admitted. *)
(* Next Obligation. Admitted. *)

(* with man_rename_ty (xi: var -> var) (s: ty) {struct s}: ty := *)
(*   match s with *)
(*   | TTop => TTop *)
(*   | TBot => TBot *)
(*   | TAll s1 s2 => *)
(*       TAll *)
(*         (man_rename_ty xi s1) *)
(*         (man_rename_ty (* xi *) (upren xi) s2) *)
(*   | TSel v => TSel (man_rename_vl xi v) *)
(*   | TMem s1 s2 => TMem (man_rename_ty xi s1) (man_rename_ty xi s2) *)
(*   | TBind s1 => *)
(*       TBind (man_rename_ty (* xi *) (upren xi) s1) *)
(*   | TAnd s1 s2 => TAnd (man_rename_ty xi s1) (man_rename_ty xi s2) *)
(*   end. *)

Fixpoint man_rename_vl (xi: var -> var) (s: vl) {struct s}: vl :=
  match s with
  | vvar v => vvar (xi v)
  | vtyp t => vtyp (@rename ty man_rename_ty xi t)
  | vabs tau t => vabs (@rename ty man_rename_ty xi tau) (@rename tm man_rename_tm (upren xi) t)
  end
with man_rename_tm (xi: var -> var) (s: tm) {struct s}: tm :=
  match s with
  | tvl v => tvl (@rename vl man_rename_vl xi v)
  | tapp s1 s2 => tapp (@rename tm man_rename_tm xi s1) (@rename tm man_rename_tm xi s2)
  end
with man_rename_ty (xi: var -> var) (s: ty) {struct s}: ty :=
  match s with
  | TTop => TTop
  | TBot => TBot
  | TAll s1 s2 =>
      TAll
        (@rename ty man_rename_ty xi s1)
        (@rename ty man_rename_ty (* xi *) (upren xi) s2)
  | TSel v => TSel (@rename vl man_rename_vl xi v)
  | TMem s1 s2 => TMem (@rename ty man_rename_ty xi s1) (@rename ty man_rename_ty xi s2)
  | TBind s1 =>
      TBind (@rename ty man_rename_ty (* xi *) (upren xi) s1)
  | TAnd s1 s2 => TAnd (@rename ty man_rename_ty xi s1) (@rename ty man_rename_ty xi s2)
  end.

Instance Rename_vl: Rename vl := man_rename_vl.
Instance Rename_ty: Rename ty := man_rename_ty.
Instance Rename_tm: Rename tm := man_rename_tm.
Instance Ids_vl: Ids vl. derive. Defined.

Fixpoint man_subst_vl (xi: var -> vl) (s: vl) {struct s}: vl :=
  match s with
  | vvar v => xi v
  | vtyp t => vtyp (@hsubst vl ty man_subst_ty xi t)
  | vabs tau t => vabs (@hsubst vl ty man_subst_ty xi tau) (@hsubst vl tm man_subst_tm (up xi) t)
  end
with man_subst_tm (xi: var -> vl) (s: tm) {struct s}: tm :=
  match s with
  | tvl v => tvl (@subst vl man_subst_vl xi v)
  | tapp s1 s2 => tapp (@hsubst vl tm man_subst_tm xi s1) (@hsubst vl tm man_subst_tm xi s2)
  end
with man_subst_ty (xi: var -> vl) (s: ty) {struct s}: ty :=
  match s with
  | TTop => TTop
  | TBot => TBot
  | TAll s1 s2 =>
      TAll
        (@hsubst vl ty man_subst_ty xi s1)
        (@hsubst vl ty man_subst_ty (* xi *) (up xi) s2)
  | TSel v => TSel (@subst vl man_subst_vl xi v)
  | TMem s1 s2 => TMem (@hsubst vl ty man_subst_ty xi s1) (@hsubst vl ty man_subst_ty xi s2)
  | TBind s1 =>
      TBind (@hsubst vl ty man_subst_ty (* xi *) (up xi) s1)
  | TAnd s1 s2 => TAnd (@hsubst vl ty man_subst_ty xi s1) (@hsubst vl ty man_subst_ty xi s2)
  end.

Instance Subst_vl: Subst vl := man_subst_vl.
Instance HSubst_ty: HSubst vl ty := man_subst_ty.
Instance HSubst_tm: HSubst vl tm := man_subst_tm.

(* Instance RenameLemmas_vl: RenLemma vl. derive. Qed. *)
(* Instance RenameLemmas_ty: RenameLemmas ty. derive. Qed. *)
(* Instance RenameLemmas_tm: RenameLemmas tm. derive. Qed. *)

Instance Ids_tm: Ids tm := fun x => tvar x.
(* XXX Ids_ty is nonsense, but is needed to let one state SubstLemmas_vl_rec and see where it'd fail. *)
Instance Ids_ty: Ids ty := fun x => TSel (vvar x).
(* SubstLemmas_vl: *)
(* SubstLemmas_tm:  *)
Print HSubstLemmas.
Eval cbn in (HSubstLemmas vl tm).
Lemma SubstLemmas_vl_rec : SubstLemmas vl /\ HSubstLemmas vl tm /\ HSubstLemmas vl ty.
repeat constructor. intros.
- induction s; simpl; try reflexivity.
  admit.
  
  f_equal.
  admit.
  asimpl.
  simpl in *. unfold rename, up, upren.
  unfold ren.
  unfold Ids_vl. simpl.
  asimpl.
   +
     Set Printing Notations.
     Unset Printing Notations.
  ttyp (mmap (rename xi) t) = ttyp t..[ren xi]
  ttyp (mmap (rename xi) t) = ttyp (mmap (subst (ren xi)) t)
     admit.
   + f_equal.
     * admit.
     * unfold upren, up.
derive. Qed.

(* fix go (xi : var -> var) (s : vl): vl := *)
(*   match s with *)
(*   | vvar v => vvar (xi v) *)
(*   | vtyp t => vtyp (rename xi t) *)
(*   | vabs tau t => vabs (rename xi tau) (@rename tm Rename_tm (upren xi) _) *)
(*   end. *)
(* with  *)

(* Instance Rename_ty_bad: Rename ty. derive. Defined. *)
(* Print Rename_ty_bad. *)

(* Instance Rename_ty: Rename ty := *)
(* fix go (xi : var -> var) (s : ty) {struct s} : ty := *)
(*   match s with *)
(*   | TTop => TTop *)
(*   | TBot => TBot *)
(*   | TAll s1 s2 => *)
(*       TAll *)
(*         (go xi s1) *)
(*         (go (* xi *) (upren xi) s2) *)
(*   | TSel v => TSel (xi v) *)
(*   | TMem s1 s2 => TMem (go xi s1) (go xi s2) *)
(*   | TBind s1 => *)
(*       TBind (go (* xi *) (upren xi) s1) *)
(*   | TAnd s1 s2 => TAnd (go xi s1) (go xi s2) *)
(*   end. *)

(* Instance Rename_tm: Rename tm. derive. Defined. *)
(* Print Rename_tm. *)
(* Unset Printing Implicit. *)
(* Print Rename_tm. *)

(* Instance Rename_tm: Rename tm := *)
(* fix go (xi : var -> var) (s : tm) {struct s} : tm := *)
(*   match s with *)
(*   | tvar v => tvar (xi v) *)
(*   | ttyp t => ttyp (rename xi t) *)
(*   | tabs tau t => tabs (rename xi tau) (@rename tm go (upren xi) t) *)
(*   | tapp s1 s2 => tapp (go xi s1) (go xi s2) *)
(*   end. *)


(* Instance Subst_tm : Subst tm. derive. Defined. *)
(* Set Printing Implicit. *)
(* Unset Printing Notations. *)
(* Print Subst_tm. *)

Instance Subst_tm : Subst tm :=
(* fix dummy (sigma : var -> tm) (s : tm) {struct s} : tm := *)
(*   match s as t return (@annot Type tm tm t) with *)
(*   | tvar v => sigma v *)
(*   | ttyp t => ttyp t..[sigma] *)
(*   | tabs t _b => tabs t..[sigma] _b.[@up tm Ids_tm Rename_tm sigma] *)
(*   | tapp s1 s2 => tapp s1.[sigma] s2.[sigma] *)
(*   end. *)

(* fix dummy (sigma : var -> tm) (s : tm) {struct s} : tm := *)
(*   match s as t return (@annot Type tm tm t) with *)
(*   | tvar v => sigma v *)
(*   | ttyp t => ttyp t..[sigma] *)
(*   | tabs t _b => tabs t..[sigma] _b.[@up tm Ids_tm Rename_tm sigma] *)
(*   | tapp s1 s2 => tapp s1.[sigma] s2.[sigma] *)
(*   end. *)

fix go (sigma : forall _ : var, tm) (s : tm) {struct s} : tm :=
  match s with
  | tvar v => sigma v
  | ttyp tau =>
      ttyp
        (@mmap tm ty (@MMap_const tm ty) (go sigma) tau)
        (* (subst sigma tau) *)
  | tabs tau t =>
      tabs (@mmap tm ty (@MMap_const tm ty) (go sigma) tau)
        (go (up sigma) t)
  | tapp s1 s2 => tapp (go sigma s1) (go sigma s2)
  end.

Instance SubstLemmas_tm : SubstLemmas tm.
constructor; intros.
- induction s; simpl; try reflexivity.
   +
     Set Printing Notations.
     Unset Printing Notations.
  ttyp (mmap (rename xi) t) = ttyp t..[ren xi]
  ttyp (mmap (rename xi) t) = ttyp (mmap (subst (ren xi)) t)
     admit.
   + f_equal.
     * admit.
     * unfold upren, up.
derive. Qed.


(* Rename_tm =  *)
(* fix dummy (xi : var -> var) (s : tm) {struct s} : tm := *)
(*   match s as t return (annot tm t) with *)
(*   | tvar v => tvar (xi v) *)
(*   | ttyp t => ttyp (mmap (rename xi) t) *)
(*   | tabs t _b => tabs (mmap (rename xi) t) (rename (upren xi) _b) *)
(*   | tapp s1 s2 => tapp (rename xi s1) (rename xi s2) *)
(*   end *)
(*      : Rename tm *)


(* Older attempt, won't work. *)
(* Inductive ty : Type := *)
(* | TTop : ty *)
(* | TBot : ty *)
(* (* (z: T) -> T^z *) *)
(* | TAll : ty -> {bind tm in ty} -> ty *)
(* (* x.Type *) *)
(* | TSel : var -> ty *)
(* (* { Type: S..U } *) *)
(* | TMem : ty(*S*) -> ty(*U*) -> ty *)
(* | TBind  : {bind tm in ty} -> ty (* Recursive binder: { z => T^z }, *)
(*                          where z is locally bound in T *) *)
(* | TAnd : ty -> ty -> ty (* Intersection Type: T1 /\ T2 *) *)
(* with tm : Type := *)
(* (* x -- free variable, matching concrete environment *) *)
(* | tvar : var -> tm *)
(* (* { Type = T } *) *)
(* | ttyp : ty -> tm *)
(* (* lambda x:T.t *) *)
(* | tabs : ty -> {bind tm in tm} -> tm *)
(* (* t t *) *)
(* | tapp : tm -> tm -> tm *)
(* . *)
