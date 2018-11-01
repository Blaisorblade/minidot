(*
DOT storeless
T ::= Bot | Top | T1 /\ T2 | T1 \/ T2 |
      { def m(x: S): U^x } | { type A: S..U } | p.A | { z => T^z }
t ::= p | t.m(t)
d ::= { def m(x: S): U^x = t^x } | { type A = T }
v ::= { z => d^z... }
p ::= x | v
*)

(* in small-step *)
Require Export SfLib.
Require Import Omega.

Require Export Arith.EqNat.
Require Export Arith.Lt.

From iris Require Import base_logic.lib.saved_prop.

Definition id := nat.
Definition lb := nat.

Inductive vr : Type :=
  | VarF: id(*absolute position in context, from origin, invariant under context extension*) -> vr
  | VarB: id(*bound variable, de Bruijn, locally nameless style -- see open *) -> vr
  | VObj: dms(*self is bound, de Bruijn, var*) -> vr
with ty : Type :=
  | TBot   : ty
  | TTop   : ty
  | TFun   : lb -> ty -> ty -> ty
  | TMem   : lb -> ty -> ty -> ty
  | TSel   : vr -> lb -> ty
  | TBind  : ty -> ty
  | TAnd   : ty -> ty -> ty
  | TOr    : ty -> ty -> ty
  (* Beware: TLater was added later to this code, and there aren't enough typing
     rules involving it; it's only meant for use in the semantic typing/logical
     relation defined later. *)
  | TLater : ty -> ty
with  tm : Type :=
  | tvar  : vr -> tm
  | tapp  : tm -> lb -> tm -> tm

with dm : Type :=
  | dfun : ty -> ty -> tm -> dm
  | dty  : ty -> dm

(* we need our own list-like structure for stuctural recursion, e.g. in subst_tm *)
with dms : Type :=
  | dnil : dms
  | dcons : dm -> dms -> dms
.

Fixpoint dms_to_list (ds: dms) : list dm :=
  match ds with
    | dnil => []
    | dcons d ds => d :: dms_to_list ds
  end.

Definition tenv := list ty.

Hint Unfold tenv.

Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.

Inductive vr_closed: nat(*i:abstract*) -> nat(*k:bound*) -> vr -> Prop :=
| clv_abs: forall i k x,
    i > x ->
    vr_closed i k (VarF x)
| clv_bound: forall i k x,
    k > x ->
    vr_closed i k (VarB x)
| clv_obj: forall i k ds,
    dms_closed i (S k) ds ->
    vr_closed i k (VObj ds)
with closed: nat -> nat -> ty -> Prop :=
| cl_bot: forall i k,
    closed i k TBot
| cl_top: forall i k,
    closed i k TTop
| cl_fun: forall i k l T1 T2,
    closed i k T1 ->
    closed i (S k) T2 ->
    closed i k (TFun l T1 T2)
| cl_mem: forall i k l T1 T2,
    closed i k T1 ->
    closed i k T2 ->
    closed i k (TMem l T1 T2)
| cl_sel: forall i k v1 l,
    vr_closed i k v1 ->
    closed i k (TSel v1 l)
| cl_bind: forall i k T1,
    closed i (S k) T1 ->
    closed i k (TBind T1)
| cl_and: forall i k T1 T2,
    closed i k T1 ->
    closed i k T2 ->
    closed i k (TAnd T1 T2)
| cl_or: forall i k T1 T2,
    closed i k T1 ->
    closed i k T2 ->
    closed i k (TOr T1 T2)
| cl_later: forall i k T1,
    closed i k T1 ->
    closed i k (TLater T1)
with tm_closed: nat -> nat -> tm -> Prop :=
| clt_var: forall i k v1,
    vr_closed i k v1 ->
    tm_closed i k (tvar v1)
| clt_app: forall i k t1 l t2,
    tm_closed i k t1 ->
    tm_closed i k t2 ->
    tm_closed i k (tapp t1 l t2)
with dm_closed: nat -> nat -> dm -> Prop :=
| cld_fun: forall i k T1 T2 t2,
    closed i k T1 ->
    closed i (S k) T2 ->
    tm_closed i (S k) t2 ->
    dm_closed i k (dfun T1 T2 t2)
| cld_ty: forall i k T1,
    closed i k T1 ->
    dm_closed i k (dty T1)
with dms_closed: nat -> nat -> dms -> Prop :=
| clds_nil: forall i k,
    dms_closed i k dnil
| clds_cons: forall i k d1 ds2,
    dm_closed i k d1 ->
    dms_closed i k ds2 ->
    dms_closed i k (dcons d1 ds2)
.

Fixpoint vr_open (k: nat) (u: vr) (v: vr) { struct v }: vr :=
  match v with
    | VarF x => VarF x
    | VarB x => if beq_nat k x then u else VarB x
    | VObj dms => VObj (dms_open (S k) u dms)
  end
with open (k: nat) (u: vr) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TBot        => TBot
    | TSel v1 l     => TSel (vr_open k u v1) l
    | TFun l T1 T2  => TFun l (open k u T1) (open (S k) u T2)
    | TMem l T1 T2  => TMem l (open k u T1) (open k u T2)
    | TBind T1    => TBind (open (S k) u T1)
    | TAnd T1 T2  => TAnd (open k u T1) (open k u T2)
    | TOr T1 T2   => TOr (open k u T1) (open k u T2)
    | TLater T1   => TLater (open k u T1)
  end
with tm_open (k: nat) (u: vr) (t: tm) { struct t }: tm :=
   match t with
     | tvar v => tvar (vr_open k u v)
     | tapp t1 l t2 => tapp (tm_open k u t1) l (tm_open k u t2)
   end
with dm_open (k: nat) (u: vr) (d: dm) { struct d }: dm :=
   match d with
     | dfun T1 T2 t2 => dfun (open k u T1) (open (S k) u T2) (tm_open (S k) u t2)
     | dty T1 => dty (open k u T1)
   end
with dms_open (k: nat) (u: vr) (ds: dms) { struct ds }: dms :=
   match ds with
     | dnil => dnil
     | dcons d ds => dcons (dm_open k u d) (dms_open k u ds)
   end.

Fixpoint vr_subst (u : vr) (v : vr) {struct v} : vr :=
  match v with
    | VarF i  => if beq_nat i 0 then u else VarF (i-1)
    | VarB i  => VarB i
    | VObj ds => VObj (dms_subst u ds)
  end
with subst (u : vr) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TMem l T1 T2 => TMem l (subst u T1) (subst u T2)
    | TSel v1 l    => TSel (vr_subst u v1) l
    | TFun l T1 T2 => TFun l (subst u T1) (subst u T2)
    | TBind T2     => TBind (subst u T2)
    | TAnd T1 T2   => TAnd (subst u T1) (subst u T2)
    | TOr T1 T2    => TOr (subst u T1) (subst u T2)
    | TLater T1    => TLater (subst u T1)
  end
with tm_subst (u : vr) (t : tm) { struct t } : tm :=
   match t with
     | tvar v => tvar (vr_subst u v)
     | tapp t1 l t2 => tapp (tm_subst u t1) l (tm_subst u t2)
   end
with dm_subst (u : vr) (d : dm) { struct d } : dm :=
   match d with
     | dfun T1 T2 t2 => dfun (subst u T1) (subst u T2) (tm_subst u t2)
     | dty T1 => dty (subst u T1)
   end
with dms_subst (u : vr) (ds : dms) { struct ds } : dms :=
   match ds with
     | dnil => dnil
     | dcons d ds => dcons (dm_subst u d) (dms_subst u ds)
   end.

Definition subst_dms (u:dms) (ds: dms) := dms_open 0 (VObj u) ds.
Definition subst_dm (x:dms) (D: dm) := dm_open 0 (VObj x) D.
Definition subst_tm (x:dms) (t: tm) := tm_open 0 (VObj x) t.
Definition subst_ty (x:dms) (T: ty) := open 0 (VObj x) T.
Definition substt (x:dms) (T: ty) := (subst (VObj x) T).
Hint Immediate substt.

Hint Constructors ty.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.

Hint Resolve ex_intro.


Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.





Lemma index_max : forall X vs n (T: X),
                       index n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs.
  Case "nil". intros. inversion H.
  Case "cons".
  intros. inversion H.
  case_eq (beq_nat n (length vs)); intros E.
  SCase "hit".
  rewrite E in H1. inversion H1. subst.
  eapply beq_nat_true in E.
  unfold length. unfold length in E. rewrite E. eauto.
  SCase "miss".
  rewrite E in H1.
  assert (n < length vs). eapply IHvs. apply H1.
  compute. eauto.
Qed.

Lemma index_exists : forall X vs n,
                       n < length vs ->
                       exists (T:X), index n vs = Some T.
Proof.
  intros X vs. induction vs.
  Case "nil". intros. inversion H.
  Case "cons".
  intros. inversion H.
  SCase "hit".
  assert (beq_nat n (length vs) = true) as E. eapply beq_nat_true_iff. eauto.
  simpl. subst n. rewrite E. eauto.
  SCase "miss".
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff. omega.
  simpl. rewrite E. eapply IHvs. eauto.
Qed.


Lemma index_extend : forall X vs n a (T: X),
                       index n vs = Some T ->
                       index n (a::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply index_max. eauto.
  assert (n <> length vs). omega.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff; eauto.
  unfold index. unfold index in H. rewrite H. rewrite E. reflexivity.
Qed.

Lemma plus_lt_contra: forall a b,
  a + b < b -> False.
Proof.
  intros a b H. induction a.
  - simpl in H. apply lt_irrefl in H. assumption.
  - simpl in H. apply IHa. omega.
Qed.

Lemma index_extend_mult: forall {X} G0 G2 x0 (T:X),
    index x0 G0 = Some T ->
    index x0 (G2++G0) = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl. assumption.
  - simpl.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E.
      apply index_max in H. subst.
      rewrite app_length in H. apply plus_lt_contra in H. inversion H.
    + apply IHG2. assumption.
Qed.

Scheme vr_mut := Induction for vr Sort Prop
with   ty_mut := Induction for ty Sort Prop
with   tm_mut := Induction for tm Sort Prop
with   dm_mut := Induction for dm Sort Prop
with   dms_mut := Induction for dms Sort Prop.
Combined Scheme syntax_mutind from vr_mut, ty_mut, tm_mut, dm_mut, dms_mut.

Scheme vr_cl_mut := Induction for vr_closed Sort Prop
with   ty_cl_mut := Induction for closed Sort Prop
with   tm_cl_mut := Induction for tm_closed Sort Prop
with   dm_cl_mut := Induction for dm_closed Sort Prop
with   dms_cl_mut := Induction for dms_closed Sort Prop.
Combined Scheme closed_mutind from vr_cl_mut, ty_cl_mut, tm_cl_mut, dm_cl_mut, dms_cl_mut.

Lemma closed_upgrade_gh_rec:
  (forall i k v1, vr_closed i k v1 -> forall i1, i <= i1 -> vr_closed i1 k v1) /\
  (forall i k T1, closed i k T1 -> forall i1, i <= i1 -> closed i1 k T1) /\
  (forall i k t1, tm_closed i k t1 -> forall i1, i <= i1 -> tm_closed i1 k t1) /\
  (forall i k d1, dm_closed i k d1 -> forall i1, i <= i1 -> dm_closed i1 k d1) /\
  (forall i k ds1, dms_closed i k ds1 -> forall i1, i <= i1 -> dms_closed i1 k ds1).
Proof.
  apply closed_mutind; intros; econstructor; eauto. omega.
Qed.

Lemma closed_upgrade_gh: forall i i1 k T1,
  closed i k T1 -> i <= i1 -> closed i1 k T1.
Proof.
  intros. eapply (proj1 (proj2 closed_upgrade_gh_rec)); eauto.
Qed.

Lemma closed_upgrade_rec:
  (forall i k v1, vr_closed i k v1 -> forall k1, k <= k1 -> vr_closed i k1 v1) /\
  (forall i k T1, closed i k T1 -> forall k1, k <= k1 -> closed i k1 T1) /\
  (forall i k t1, tm_closed i k t1 -> forall k1, k <= k1 -> tm_closed i k1 t1) /\
  (forall i k d1, dm_closed i k d1 -> forall k1, k <= k1 -> dm_closed i k1 d1) /\
  (forall i k ds1, dms_closed i k ds1 -> forall k1, k <= k1 -> dms_closed i k1 ds1).
Proof.
  apply closed_mutind; intros; econstructor; eauto;
  try solve [omega];
  try solve [eapply H; omega];
  try solve [eapply H0; omega];
  try solve [eapply H1; omega].
Qed.

Lemma closed_upgrade: forall i k k1 T1,
  closed i k T1 -> k <= k1 -> closed i k1 T1.
Proof.
  intros. eapply (proj1 (proj2 closed_upgrade_rec)); eauto.
Qed.

Lemma closed_open_rec:
  (forall v1, forall j k v, vr_closed k (j+1) v1 -> vr_closed k j v -> vr_closed k j (vr_open j v v1)) /\
  (forall T1, forall j k v, closed k (j+1) T1 -> vr_closed k j v -> closed k j (open j v T1)) /\
  (forall t1, forall j k v, tm_closed k (j+1) t1 -> vr_closed k j v -> tm_closed k j (tm_open j v t1)) /\
  (forall d1, forall j k v, dm_closed k (j+1) d1 -> vr_closed k j v -> dm_closed k j (dm_open j v d1)) /\
  (forall ds1, forall j k v, dms_closed k (j+1) ds1 -> vr_closed k j v -> dms_closed k j (dms_open j v ds1)).
Proof.
  apply syntax_mutind; intros;
  try solve [
        try inversion H; try inversion H0; try inversion H1; try inversion H2;
        subst; simpl; econstructor;
        try (eapply H; eauto); try (eapply H0; eauto); try (eapply H1; eauto);
        eauto;
        try solve [omega];
        try solve [eapply (proj1 closed_upgrade_rec); eauto]
      ].
  - inversion H; subst. simpl.
    case_eq (beq_nat j i); intros E; eauto.
    econstructor. eapply beq_nat_false_iff in E. omega.
Qed.

Lemma closed_open: forall j k v T, closed k (j+1) T -> vr_closed k j v -> closed k j (open j v T).
Proof.
  intros. eapply (proj1 (proj2 closed_open_rec)); eauto.
Qed.

Lemma beq_nat_true_eq: forall A, beq_nat A A = true.
Proof. intros. eapply beq_nat_true_iff. eauto. Qed.



Lemma closed_no_open_rec:
  (forall l j v, vr_closed l j v -> forall vx, v = vr_open j vx v) /\
  (forall l j T, closed l j T -> forall vx, T = open j vx T) /\
  (forall l j t, tm_closed l j t -> forall vx, t = tm_open j vx t) /\
  (forall l j d, dm_closed l j d -> forall vx, d = dm_open j vx d) /\
  (forall l j ds, dms_closed l j ds -> forall vx, ds = dms_open j vx ds).
Proof.
  apply closed_mutind; intros; eauto; simpl;
  try (rewrite <- H); try (rewrite <- H0); try (rewrite <- H1); eauto.
  - simpl.
    assert (k <> x) as A. omega.
    eapply beq_nat_false_iff in A. rewrite A. reflexivity.
Qed.

Lemma closed_no_open: forall T x l j,
  closed l j T ->
  T = open j (VarF x) T.
Proof.
  intros. eapply (proj1 (proj2 closed_no_open_rec)); eauto.
Qed.

Lemma closed_no_subst_rec:
  (forall v j, vr_closed 0 j v -> forall vx, vr_subst vx v = v) /\
  (forall T j, closed 0 j T -> forall vx, subst vx T = T) /\
  (forall t j, tm_closed 0 j t -> forall vx, tm_subst vx t = t) /\
  (forall d j, dm_closed 0 j d -> forall vx, dm_subst vx d = d) /\
  (forall ds j, dms_closed 0 j ds -> forall vx, dms_subst vx ds = ds).
Proof.
  apply syntax_mutind; intros;
  try inversion H; try inversion H0; try inversion H1; try inversion H2;
  subst; simpl; f_equal;
  try solve [erewrite H; eauto];
  try solve [erewrite H0; eauto];
  try solve [erewrite H1; eauto];
  eauto; try omega.
Qed.

Lemma closed_no_subst: forall T k TX,
   closed 0 k T ->
   subst TX T = T.
Proof.
  intros. eapply (proj1 (proj2 closed_no_subst_rec)); eauto.
Qed.

Lemma closed_subst_rec:
  (forall v j n V, vr_closed (n+1) j v -> vr_closed n 0 V -> vr_closed n j (vr_subst V v)) /\
  (forall T j n V, closed (n+1) j T -> vr_closed n 0 V -> closed n j (subst V T)) /\
  (forall t j n V, tm_closed (n+1) j t -> vr_closed n 0 V -> tm_closed n j (tm_subst V t)) /\
  (forall d j n V, dm_closed (n+1) j d -> vr_closed n 0 V -> dm_closed n j (dm_subst V d)) /\
  (forall ds j n V, dms_closed (n+1) j ds -> vr_closed n 0 V -> dms_closed n j (dms_subst V ds)).
Proof.
  apply syntax_mutind; intros;
  try inversion H; try inversion H0; try inversion H1; try inversion H2;
  subst; simpl; try econstructor;
  try solve [eapply H; eauto];
  try solve [eapply H0; eauto];
  try solve [eapply H1; eauto];
  eauto; try omega;
  try solve [case_eq (beq_nat i 0); intros E; [
    (eapply (proj1 closed_upgrade_rec); eauto; omega) |
    (econstructor; eapply beq_nat_false_iff in E; omega) ]].
Qed.

Lemma closed_subst: forall j n V T, closed (n+1) j T -> vr_closed n 0 V -> closed n j (subst V T).
Proof.
  intros. eapply (proj1 (proj2 closed_subst_rec)); eauto.
Qed.

Lemma subst_open_distribute: forall k j0 vx v,
  vr_closed k j0 vx ->
  (forall v0 j, j0 <= j -> vr_subst vx (vr_open j v v0) = vr_open j (vr_subst vx v) (vr_subst vx v0)) /\
  (forall T0 j, j0 <= j -> subst vx (open j v T0) = open j (vr_subst vx v) (subst vx T0)) /\
  (forall t0 j, j0 <= j -> tm_subst vx (tm_open j v t0) = tm_open j (vr_subst vx v) (tm_subst vx t0)) /\
  (forall d0 j, j0 <= j -> dm_subst vx (dm_open j v d0) = dm_open j (vr_subst vx v) (dm_subst vx d0)) /\
  (forall ds0 j, j0 <= j -> dms_subst vx (dms_open j v ds0) = dms_open j (vr_subst vx v) (dms_subst vx ds0)).
Proof.
  intros k j0 vx v HCx.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - case_eq (beq_nat i 0); intros E; simpl; eauto.
    eapply (proj1 closed_no_open_rec).
    eapply (proj1 closed_upgrade_rec). eauto. omega.
  - case_eq (beq_nat j i); intros E; simpl; eauto.
Qed.

Lemma subst_open_commute0_rec:
  (forall v0 j TX, vr_closed 0 (j+1) v0 -> (vr_subst TX (vr_open j (VarF 0) v0)) = vr_open j TX v0) /\
  (forall T0 j TX, closed 0 (j+1) T0 -> (subst TX (open j (VarF 0) T0)) = open j TX T0) /\
  (forall t0 j TX, tm_closed 0 (j+1) t0 -> (tm_subst TX (tm_open j (VarF 0) t0)) = tm_open j TX t0) /\
  (forall d0 j TX, dm_closed 0 (j+1) d0 -> (dm_subst TX (dm_open j (VarF 0) d0)) = dm_open j TX d0) /\
  (forall ds0 j TX, dms_closed 0 (j+1) ds0 -> (dms_subst TX (dms_open j (VarF 0) ds0)) = dms_open j TX ds0).
Proof.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - inversion H; subst. omega.
  - inversion H; subst.
    case_eq (beq_nat j i); intros E; simpl; eauto.
Qed.

Lemma subst_open_commute0: forall T0 j TX,
  closed 0 (j+1) T0 ->
  (subst TX (open j (VarF 0) T0)) = open j TX T0.
Proof.
  intros. eapply (proj1 (proj2 subst_open_commute0_rec)); eauto.
Qed.

Lemma subst_open_commute1_rec: forall x x0,
  vr_closed 0 0 (VObj x) ->
  vr_closed 0 0 (VObj x0) ->
  (forall v0 j, (vr_open j (VObj x0) (vr_subst (VObj x) v0)) = (vr_subst (VObj x) (vr_open j (VObj x0) v0))) /\
  (forall T0 j, (open j (VObj x0) (subst (VObj x) T0)) = (subst (VObj x) (open j (VObj x0) T0))) /\
  (forall t0 j, (tm_open j (VObj x0) (tm_subst (VObj x) t0)) = (tm_subst (VObj x) (tm_open j (VObj x0) t0))) /\
  (forall d0 j, (dm_open j (VObj x0) (dm_subst (VObj x) d0)) = (dm_subst (VObj x) (dm_open j (VObj x0) d0))) /\
  (forall ds0 j, (dms_open j (VObj x0) (dms_subst (VObj x) ds0)) = (dms_subst (VObj x) (dms_open j (VObj x0) ds0))).
Proof.
  intros x x0 HCx HCx0.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - case_eq (beq_nat i 0); intros E; simpl; eauto.
    erewrite <- (proj2 (proj2 (proj2 (proj2 closed_no_open_rec)))).
    reflexivity.
    inversion HCx; subst.
    eapply (proj2 (proj2 (proj2 (proj2 closed_upgrade_rec)))); eauto.
    omega.
  - case_eq (beq_nat j i); intros E; simpl; eauto.
    erewrite (proj2 (proj2 (proj2 (proj2 closed_no_subst_rec)))).
    reflexivity.
    inversion HCx0; subst.
    eassumption.
Qed.

Lemma subst_open_commute1: forall x x0,
  vr_closed 0 0 (VObj x) ->
  vr_closed 0 0 (VObj x0) -> forall j T0,
 (open j (VObj x0) (subst (VObj x) T0))
 = (subst (VObj x) (open j (VObj x0) T0)).
Proof.
  intros x x0 Hx Hx0. intros.
  eapply (proj1 (proj2 (subst_open_commute1_rec x x0 Hx Hx0))); eauto.
Qed.

Lemma subst_closed_id: forall x k T2,
  closed 0 k T2 ->
  substt x T2 = T2.
Proof. intros. eapply closed_no_subst. eauto. Qed.

Lemma closed_subst0: forall i k x T2,
  vr_closed i 0 (VObj x) ->
  closed (i + 1) k T2 ->
  closed i k (substt x T2).
Proof. intros. eapply closed_subst. eauto. eauto. Qed.

Lemma closed_subst1: forall i k x T2,
  closed i k T2 -> i <> 0 ->
  vr_closed (i-1) 0 (VObj x) ->
  closed (i-1) k (substt x T2).
Proof.
  intros. eapply closed_subst.
  assert ((i - 1 + 1) = i) as R. omega.
  rewrite R. eauto. eauto.
Qed.

Lemma index_subst: forall GH TX T0 T3 x,
  index (length (GH ++ [TX])) (T0 :: GH ++ [TX]) = Some T3 ->
  index (length GH) (map (substt x) (T0 :: GH)) = Some (substt x T3).
Proof.
  intros GH. induction GH; intros; inversion H.
  - eauto.
  - rewrite beq_nat_true_eq in H1. inversion H1. subst. simpl.
    rewrite map_length. rewrite beq_nat_true_eq. eauto.
Qed.

Lemma index_subst1: forall GH TX T3 x x0,
  index x0 (GH ++ [TX]) = Some T3 -> x0 <> 0 ->
  index (x0-1) (map (substt x) GH) = Some (substt x T3).
Proof.
  intros GH. induction GH; intros; inversion H.
  - eapply beq_nat_false_iff in H0. rewrite H0 in H2. inversion H2.
  - simpl.
    assert (beq_nat (x0 - 1) (length (map (substt x) GH)) = beq_nat x0 (length (GH ++ [TX]))). {
      case_eq (beq_nat x0 (length (GH ++ [TX]))); intros E.
      eapply beq_nat_true_iff. rewrite map_length. eapply beq_nat_true_iff in E. subst x0.
      rewrite app_length. simpl. omega.
      eapply beq_nat_false_iff. eapply beq_nat_false_iff in E.
      rewrite app_length in E. simpl in E. rewrite map_length.
      destruct x0. destruct H0. reflexivity. omega.
    }
    rewrite H1. case_eq (beq_nat x0 (length (GH ++ [TX]))); intros E; rewrite E in H2.
    inversion H2. subst. eauto. eauto.
Qed.

Lemma index_hit0: forall (GH:tenv) TX T2,
 index 0 (GH ++ [TX]) = Some T2 -> T2 = TX.
Proof.
  intros GH. induction GH; intros; inversion H.
  - eauto.
  - rewrite app_length in H1. simpl in H1.
    remember (length GH + 1) as L. destruct L. omega. eauto.
Qed.

Lemma subst_open_rec: forall k x,
  (vr_closed k 0 (VObj x)) ->
  (forall v j n, (vr_subst (VObj x) (vr_open j (VarF (n+1)) v)) = (vr_open j (VarF n) (vr_subst (VObj x) v))) /\
  (forall T j n, (subst (VObj x) (open j (VarF (n+1)) T)) = (open j (VarF n) (subst (VObj x) T))) /\
  (forall t j n, (tm_subst (VObj x) (tm_open j (VarF (n+1)) t)) = (tm_open j (VarF n) (tm_subst (VObj x) t))) /\
  (forall d j n, (dm_subst (VObj x) (dm_open j (VarF (n+1)) d)) = (dm_open j (VarF n) (dm_subst (VObj x) d))) /\
  (forall ds j n, (dms_subst (VObj x) (dms_open j (VarF (n+1)) ds)) = (dms_open j (VarF n) (dms_subst (VObj x) ds))).
Proof.
  intros k x Hx.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - case_eq (beq_nat i 0); intros E; simpl; eauto.
    f_equal.
    erewrite <- (proj2 (proj2 (proj2 (proj2 closed_no_open_rec)))).
    reflexivity. inversion Hx; subst.
    eapply (proj2 (proj2 (proj2 (proj2 closed_upgrade_rec)))). eauto. omega.
  - case_eq (beq_nat j i); intros E; simpl; eauto.
    assert (beq_nat (n + 1) 0 = false) as E1. {
      apply beq_nat_false_iff. omega.
    }
    rewrite E1.
    f_equal. omega.
Qed.

Lemma subst_open: forall k x, vr_closed k 0 (VObj x) ->
  forall TX n j,
  (substt x (open j (VarF (n+1)) TX)) =
  (open j (VarF n) (substt x TX)).
Proof.
  intros k x Hx. intros. eapply (proj1 (proj2 (subst_open_rec k x Hx))); eauto.
Qed.

Lemma subst_open3: forall k x, vr_closed k 0 (VObj x) -> forall TX0 (GH:tenv) TX,
  (substt x (open 0 (VarF (length (GH ++ [TX]))) TX0)) =
  (open 0 (VarF (length GH)) (substt x TX0)).
Proof. intros. rewrite app_length. simpl. eapply subst_open. eauto. Qed.

Lemma subst_open4: forall k x, vr_closed k 0 (VObj x) -> forall T0 (GH:tenv) TX,
  substt x (open 0 (VarF (length (GH ++ [TX]))) T0) =
  open 0 (VarF (length (map (substt x) GH))) (substt x T0).
Proof. intros. rewrite map_length. eapply subst_open3. eauto. Qed.

Lemma subst_open5: forall k x, vr_closed k 0 (VObj x) -> forall (GH:tenv) T0 xi,
  xi <> 0 -> substt x (open 0 (VarF xi) T0) =
  open 0 (VarF (xi-1)) (substt x T0).
Proof.
  intros. remember (xi-1) as n. assert (xi=n+1) as R. omega. rewrite R.
  eapply subst_open. eauto.
Qed.

Lemma subst_open_commute0b_rec: forall k x,
  (vr_closed k 0 (VObj x)) ->
  (forall v1 n, vr_subst (VObj x) (vr_open n (VarF 0) v1) = vr_open n (VObj x) (vr_subst (VObj x) v1)) /\
  (forall T1 n, subst (VObj x) (open n (VarF 0) T1) = open n (VObj x) (subst (VObj x) T1)) /\
  (forall t1 n, tm_subst (VObj x) (tm_open n (VarF 0) t1) = tm_open n (VObj x) (tm_subst (VObj x) t1)) /\
  (forall d1 n, dm_subst (VObj x) (dm_open n (VarF 0) d1) = dm_open n (VObj x) (dm_subst (VObj x) d1)) /\
  (forall ds1 n, dms_subst (VObj x) (dms_open n (VarF 0) ds1) = dms_open n (VObj x) (dms_subst (VObj x) ds1)).
Proof.
  intros k x Hx.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - case_eq (beq_nat i 0); intros E; simpl; eauto.
    erewrite <- (proj2 (proj2 (proj2 (proj2 closed_no_open_rec)))).
    reflexivity.
    inversion Hx; subst.
    eapply (proj2 (proj2 (proj2 (proj2 closed_upgrade_rec)))); eauto.
    omega.
  - case_eq (beq_nat n i); intros E; simpl; eauto.
Qed.

Lemma subst_open_commute0b: forall k x,
  (vr_closed k 0 (VObj x)) -> forall T1 n,
  substt x (open n (VarF 0) T1) = open n (VObj x) (substt x T1).
Proof.
  unfold substt.
  intros k x Hx. intros.
  eapply (proj1 (proj2 (subst_open_commute0b_rec k x Hx))); eauto.
Qed.

Lemma subst_open_commute_z_rec: forall k x,
  (vr_closed k 0 (VObj x)) ->
  (forall v1 z n, vr_subst (VObj x) (vr_open n (VarF (z + 1)) v1) = vr_open n (VarF z) (vr_subst (VObj x) v1)) /\
  (forall T1 z n, subst (VObj x) (open n (VarF (z + 1)) T1) = open n (VarF z) (subst (VObj x) T1)) /\
  (forall t1 z n, tm_subst (VObj x) (tm_open n (VarF (z + 1)) t1) = tm_open n (VarF z) (tm_subst (VObj x) t1)) /\
  (forall d1 z n, dm_subst (VObj x) (dm_open n (VarF (z + 1)) d1) = dm_open n (VarF z) (dm_subst (VObj x) d1)) /\
  (forall ds1 z n, dms_subst (VObj x) (dms_open n (VarF (z + 1)) ds1) = dms_open n (VarF z) (dms_subst (VObj x) ds1)).
Proof.
  intros k x Hx.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - case_eq (beq_nat i 0); intros E; simpl; eauto.
    erewrite <- (proj2 (proj2 (proj2 (proj2 closed_no_open_rec)))).
    reflexivity.
    inversion Hx; subst.
    eapply (proj2 (proj2 (proj2 (proj2 closed_upgrade_rec)))); eauto.
    omega.
  - case_eq (beq_nat n i); intros E; simpl; eauto.
    assert (beq_nat (z + 1) 0 = false) as E1. {
      eapply beq_nat_false_iff. omega.
    }
    rewrite E1. f_equal. omega.
Qed.

Lemma subst_open_commute_z: forall k x,
 (vr_closed k 0 (VObj x)) -> forall T1 z n,
 subst (VObj x) (open n (VarF (z + 1)) T1) =
 open n (VarF z) (subst (VObj x) T1).
Proof.
  intros k x Hx. intros.
  eapply (proj1 (proj2 (subst_open_commute_z_rec k x Hx))); eauto.
Qed.

Lemma length_subst_dms: forall ds x,
  (length (dms_to_list ds))=(length (dms_to_list (subst_dms x ds))).
Proof.
  intros. induction ds; eauto.
  simpl. rewrite IHds. reflexivity.
Qed.

Lemma length_dms_subst: forall ds x,
  (length (dms_to_list ds))=(length (dms_to_list (dms_subst x ds))).
Proof.
  intros. induction ds; eauto.
  simpl. rewrite IHds. reflexivity.
Qed.

Lemma length_open_dms: forall ds x,
  (length (dms_to_list ds))=(length (dms_to_list (dms_open 0 (VObj x) ds))).
Proof.
  intros. induction ds; eauto.
  simpl. rewrite IHds. reflexivity.
Qed.

Lemma length_dms_open: forall ds v,
  (length (dms_to_list ds))=(length (dms_to_list (dms_open 0 v ds))).
Proof.
  intros. induction ds; eauto.
  simpl. rewrite IHds. reflexivity.
Qed.

Lemma index_subst_dms: forall ds ds0 D ds1 x,
  dms_to_list ds = ds0 ++ dms_to_list (dcons D ds1) ->
  index (length (dms_to_list ds1)) (dms_to_list (subst_dms x ds)) = Some (subst_dm x D).
Proof.
  intros. generalize dependent ds1. generalize dependent ds. induction ds0; intros.
  - simpl in H. destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite <- length_open_dms. rewrite beq_nat_true_eq. reflexivity.
  - destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite false_beq_nat. eapply IHds0. eauto.
    rewrite <- length_open_dms. rewrite H2. rewrite app_length. simpl.
    omega.
Qed.

Lemma index_dms_open: forall ds ds0 D ds1 v,
  dms_to_list ds = ds0 ++ dms_to_list (dcons D ds1) ->
  index (length (dms_to_list ds1)) (dms_to_list (dms_open 0 v ds)) = Some (dm_open 0 v D).
Proof.
  intros. generalize dependent ds1. generalize dependent ds. induction ds0; intros.
  - simpl in H. destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite <- length_dms_open. rewrite beq_nat_true_eq. reflexivity.
  - destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite false_beq_nat. eapply IHds0. eauto.
    rewrite <- length_dms_open. rewrite H2. rewrite app_length. simpl.
    omega.
Qed.

Lemma index_dms: forall ds ds0 D ds1,
  dms_to_list ds = ds0 ++ dms_to_list (dcons D ds1) ->
  index (length (dms_to_list ds1)) (dms_to_list ds) = Some D.
Proof.
  intros. generalize dependent ds1. generalize dependent ds. induction ds0; intros.
  - simpl in H. destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite beq_nat_true_eq. reflexivity.
  - destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite false_beq_nat. eapply IHds0. eauto.
    rewrite H2. rewrite app_length. simpl.
    omega.
Qed.

Lemma index_dms_open_eq: forall l x D Dx,
  vr_closed 0 0 (VObj x) ->
  index l (dms_to_list (subst_dms x x)) = Some D ->
  index l (dms_to_list (dms_open 0 (VarF 0) x)) = Some Dx ->
  dm_subst (VObj x) Dx = D.
Proof.
  intros l x D Dx HC HI HIx.
  remember HC as HCx. clear HeqHCx.
  remember x as x0. rewrite -> Heqx0 in *.
  rewrite <- Heqx0 in HI at 1. rewrite <- Heqx0 in HC. rewrite <- Heqx0.
  clear Heqx0.
  remember x as dsb.
  remember (length (dms_to_list dsb)) as n.
  assert (n = length (dms_to_list (subst_dms x0 dsb))) as Heqn'. {
    subst. rewrite <- length_subst_dms. reflexivity.
  }
  assert (exists dsa,
            dms_to_list x = dms_to_list dsa ++ dms_to_list dsb /\
            dms_to_list (subst_dms x0 x) = dms_to_list (subst_dms x0 dsa) ++ dms_to_list (subst_dms x0 dsb)) as Hds. {
    exists dnil. simpl. subst. eauto.
  }
  destruct Hds as [dsa [Hds Hds']]. clear Heqdsb.
  remember (dms_to_list dsa) as la. clear Heqla.
  remember (dms_to_list (subst_dms x0 dsa)) as la'. clear Heqla'. clear dsa.
  generalize dependent Dx. generalize dependent D.
  generalize dependent la'. generalize dependent la. generalize dependent x.
  generalize dependent l. generalize dependent n.
  inversion HCx; subst. rename H2 into HCdsb. clear HCx.
  induction dsb; intros.
  - simpl in *. inversion HI.
  - simpl in HI. simpl in HIx.
    rewrite <- length_dms_open in HI. rewrite <- length_dms_open in HIx.
    inversion HCdsb; subst.
    case_eq (beq_nat l (length (dms_to_list dsb))); intros E;
    rewrite E in HI; rewrite E in HIx.
    + inversion HI. inversion HIx.
      rewrite (proj1 (proj2 (proj2 (proj2 (subst_open_distribute 0 0 (VObj x0) (VarF 0) HC))))).
      simpl.
      erewrite (proj1 (proj2 (proj2 (proj2 closed_no_subst_rec)))). reflexivity.
      eauto. omega.
    + eapply IHdsb with (x:=x) (la:=la ++ [d]) (la':=la' ++ [(subst_dm x0 d)]); eauto.
      rewrite <- app_assoc. rewrite Hds. simpl. reflexivity.
      rewrite <- app_assoc. rewrite Hds'. simpl. reflexivity.
Qed.

Lemma index_subst_dms_eq: forall l ds D D',
  index l (dms_to_list ds) = Some D ->
  index l (dms_to_list (subst_dms ds ds)) = Some D' ->
  subst_dm ds D = D'.
Proof.
  intros l ds D D' HI HI'.
  remember ds as x. rewrite -> Heqx in *. rewrite <- Heqx in HI' at 1.
  rewrite <- Heqx.  clear Heqx.
  remember ds as dsb.
  remember (length (dms_to_list dsb)) as n.
  assert (n = length (dms_to_list (subst_dms x dsb))) as Heqn'. {
    subst. rewrite <- length_subst_dms. reflexivity.
  }
  assert (exists dsa,
            dms_to_list ds = dms_to_list dsa ++ dms_to_list dsb /\
            dms_to_list (subst_dms x ds) = dms_to_list (subst_dms x dsa) ++ dms_to_list (subst_dms x dsb)) as Hds. {
    exists dnil. simpl. subst. eauto.
  }
  destruct Hds as [dsa [Hds Hds']]. clear Heqdsb.
  remember (dms_to_list dsa) as la. clear Heqla.
  remember (dms_to_list (subst_dms x dsa)) as la'. clear Heqla'. clear dsa.
  generalize dependent D'. generalize dependent D.
  generalize dependent la'. generalize dependent la. generalize dependent ds.
  generalize dependent l. generalize dependent n.
  induction dsb; intros.
  - simpl in *. inversion HI.
  - simpl in HI. case_eq (beq_nat l (length (dms_to_list dsb))); intros E;
    rewrite E in HI; simpl in HI'; rewrite <- length_open_dms in HI'; rewrite E in HI'.
    + inversion HI. subst d. inversion HI'. reflexivity.
    + eapply IHdsb with (ds:=ds) (la:=la ++ [d]) (la':=la' ++ [(subst_dm x d)]); eauto.
      rewrite <-length_subst_dms. reflexivity.
      rewrite <- app_assoc. rewrite Hds. simpl. reflexivity.
      rewrite <- app_assoc. rewrite Hds'. simpl. reflexivity.
Qed.

Lemma index_dm_closed: forall i k l ds D,
  dms_closed i k ds ->
  index l (dms_to_list ds) = Some D ->
  dm_closed i k D.
Proof.
  intros. generalize dependent D. induction H; intros.
  - simpl in *. solve by inversion.
  - simpl in *.
    case_eq (beq_nat l (length (dms_to_list ds2))); intros E;
    rewrite -> E in *.
    + inversion H1. subst. assumption.
    + eapply IHdms_closed; eauto.
Qed.


Fixpoint tsize (T: ty) { struct T }: nat :=
  match T with
    | TTop        => 1
    | TBot        => 1
    | TSel _ l   => 1
    | TFun l T1 T2 => S (tsize T1 + tsize T2)
    | TMem l T1 T2 => S (tsize T1 + tsize T2)
    | TBind T1    => S (tsize T1)
    | TAnd T1 T2  => S (tsize T1 + tsize T2)
    | TOr T1 T2   => S (tsize T1 + tsize T2)
    | TLater T1   => S (tsize T1)
  end.

Lemma open_preserves_size: forall T v j,
  tsize T = tsize (open j v T).
Proof.
  intros T. induction T; intros; simpl; eauto.
Qed.


Ltac index_subst := match goal with
                      | H1: index ?x ?G = ?V1 , H2: index ?x ?G = ?V2 |- _ => rewrite H1 in H2; inversion H2; subst
                      | _ => idtac
                    end.

Ltac invty := match goal with
                | H1: TBot     = _ |- _ => inversion H1
                | H1: TSel _ _   = _ |- _ => inversion H1
                | H1: TMem _ _ _ = _ |- _ => inversion H1
                | H1: TFun _ _ _ = _ |- _ => inversion H1
                | H1: TBind  _ = _ |- _ => inversion H1
                | H1: TAnd _ _ = _ |- _ => inversion H1
                | H1: TOr _ _ = _ |- _ => inversion H1
                | _ => idtac
              end.

Lemma gh_match1: forall (GU:tenv) GH GL TX,
  GH ++ [TX] = GU ++ GL ->
  length GL > 0 ->
  exists GL1, GL = GL1 ++ [TX] /\ GH = GU ++ GL1.
Proof.
  intros GU. induction GU; intros.
  - eexists. simpl in H. eauto.
  - destruct GH. simpl in H.
    assert (length [TX] = 1). eauto.
    rewrite H in H1. simpl in H1. rewrite app_length in H1. omega.
    destruct (IHGU GH GL TX).
    simpl in H. inversion H. eauto. eauto.
    eexists. split. eapply H1. simpl. destruct H1. simpl in H. inversion H. subst. eauto.
Qed.

Lemma gh_match: forall (GH:tenv) GU GL TX T0,
  T0 :: GH ++ [TX] = GU ++ GL ->
  length GL = S (length (GH ++ [TX])) ->
  GU = [] /\ GL = T0 :: GH ++ [TX].
Proof.
  intros. edestruct gh_match1. rewrite app_comm_cons in H. eapply H. omega.
  assert (length (T0 :: GH ++ [TX]) = length (GU ++ GL)). rewrite H. eauto.
  assert (GU = []). destruct GU. eauto. simpl in H.
  simpl in H2. rewrite app_length in H2. simpl in H2. rewrite app_length in H2.
  simpl in H2. rewrite H0 in H2. rewrite app_length in H2. simpl in H2.
  omega.
  split. eauto. rewrite H3 in H1. simpl in H1. subst. simpl in H1. eauto.
Qed.

Lemma sub_env1: forall (GL:tenv) GU GH TX,
  GH ++ [TX] = GU ++ GL ->
  length GL = 1 ->
  GL = [TX].
Proof.
  intros.
  destruct GL. inversion H0. destruct GL.
  eapply app_inj_tail in H. destruct H. subst. eauto.
  inversion H0.
Qed.

Lemma dm_subst_self: forall k x ds l D,
  vr_closed 0 0 (VObj x) ->
  vr_closed k 0 (VObj ds) ->
  index l (dms_to_list (subst_dms ds ds)) = Some D ->
  index l (dms_to_list (subst_dms (dms_subst (VObj x) ds) (dms_subst (VObj x) ds))) = Some (dm_subst (VObj x) D).
Proof.
  intros k x ds l D HCx HCds HI.
  inversion HCds; subst. clear HCds. rename H2 into HCds.
  remember ds as ds0. rewrite -> Heqds0 in *.
  rewrite <- Heqds0 in HI at 1. rewrite <- Heqds0 at 1. clear Heqds0.
  generalize dependent D. generalize dependent ds0.
  induction HCds; intros.
  - simpl in *. solve by inversion.
  - simpl in *.
    rewrite <- length_dms_open in *. rewrite <- length_dms_subst in *.
    case_eq (beq_nat l (length (dms_to_list ds2))); intros E;
    rewrite -> E in *.
    + inversion HI; subst. f_equal.
      rewrite (proj1 (proj2 (proj2 (proj2 (subst_open_distribute 0 0 (VObj x) (VObj ds0) HCx))))).
      simpl. reflexivity. omega.
    + unfold subst_dms in *. specialize (IHHCds ds0 D HI). rewrite IHHCds.
      reflexivity.
Qed.

(* upgrade_gh interlude begin *)

Lemma index_at_index: forall {A} x0 GH0 GH1 (v:A),
  beq_nat x0 (length GH1) = true ->
  index x0 (GH0 ++ v :: GH1) = Some v.
Proof.
  intros. apply beq_nat_true in H. subst.
  induction GH0.
  - simpl. rewrite <- beq_nat_refl. reflexivity.
  - simpl.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. rewrite <- plus_Sn_m.
    rewrite false_beq_nat. assumption. omega.
Qed.

Lemma index_same: forall {A} x0 (v0:A) GH0 GH1 (v:A) (v':A),
  beq_nat x0 (length GH1) = false ->
  index x0 (GH0 ++ v :: GH1) = Some v0 ->
  index x0 (GH0 ++ v' :: GH1) = Some v0.
Proof.
  intros ? ? ? ? ? ? ? E H.
  induction GH0.
  - simpl. rewrite E. simpl in H. rewrite E in H. apply H.
  - simpl.
    rewrite app_length. simpl.
    case_eq (beq_nat x0 (length GH0 + S (length GH1))); intros E'.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite H. reflexivity.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite IHGH0. reflexivity. assumption.
Qed.

Lemma exists_GH1L: forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GH0 <= length GL ->
  exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ GH0.
Proof.
  intros X GU. induction GU; intros.
  - eexists. rewrite app_nil_l. split. reflexivity. simpl in H0. assumption.
  - induction GH1.

    simpl in H.
    assert (length (a :: GU ++ GL) = length GH0) as Contra. {
      rewrite H. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H. inversion H.
    specialize (IHGU GL GH1 GH0 H3 H0).
    destruct IHGU as [GH1L [IHA IHB]].
    exists GH1L. split. simpl. rewrite IHA. reflexivity. apply IHB.
Qed.

Lemma exists_GH0U: forall {X} (GH1: list X) (GH0: list X) (GU: list X) (GL: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GL < S (length GH0) ->
  exists GH0U, GH0 = GH0U ++ GL.
Proof.
  intros X GH1. induction GH1; intros.
  - simpl in H. exists GU. symmetry. assumption.
  - induction GU.

    simpl in H.
    assert (length GL = length (a :: GH1 ++ GH0)) as Contra. {
      rewrite H. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H. inversion H.
    specialize (IHGH1 GH0 GU GL H3 H0).
    destruct IHGH1 as [GH0U IH].
    exists GH0U. apply IH.
Qed.

(* splicing -- for stp_extend. *)

Definition splice_var n i := if le_lt_dec n i then (i+1) else i.
Hint Unfold splice_var.

Fixpoint vr_splice n (v : vr) {struct v} : vr :=
  match v with
    | VarF i => VarF (splice_var n i)
    | VarB i => VarB i
    | VObj ds => VObj (dms_splice n ds)
  end
with splice n (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TMem l T1 T2 => TMem l (splice n T1) (splice n T2)
    | TSel v1 l    => TSel (vr_splice n v1) l
    | TFun l T1 T2 => TFun l (splice n T1) (splice n T2)
    | TBind T2     => TBind (splice n T2)
    | TAnd T1 T2   => TAnd (splice n T1) (splice n T2)
    | TOr T1 T2    => TOr (splice n T1) (splice n T2)
    | TLater T1    => TLater (splice n T1)
  end
with tm_splice n (t : tm) {struct t} : tm :=
  match t with
    | tvar v => tvar (vr_splice n v)
    | tapp t1 l t2 => tapp (tm_splice n t1) l (tm_splice n t2)
  end
with dm_splice n (d : dm) {struct d} : dm :=
  match d with
    | dfun T1 T2 t2 => dfun (splice n T1) (splice n T2) (tm_splice n t2)
    | dty T1 => dty (splice n T1)
  end
with dms_splice n (ds : dms) {struct ds} : dms :=
  match ds with
    | dnil => dnil
    | dcons d ds => dcons (dm_splice n d) (dms_splice n ds)
  end
.

Lemma splice_open_distribute_rec:
  (forall v0 v j k, vr_splice k (vr_open j v v0) = vr_open j (vr_splice k v) (vr_splice k v0)) /\
  (forall T0 v j k, splice k (open j v T0) = open j (vr_splice k v) (splice k T0)) /\
  (forall t0 v j k, tm_splice k (tm_open j v t0) = tm_open j (vr_splice k v) (tm_splice k t0)) /\
  (forall d0 v j k, dm_splice k (dm_open j v d0) = dm_open j (vr_splice k v) (dm_splice k d0)) /\
  (forall ds0 v j k, dms_splice k (dms_open j v ds0) = dms_open j (vr_splice k v) (dms_splice k ds0)).
Proof.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - case_eq (beq_nat j i); intros E; simpl; eauto.
Qed.

Lemma splice_open_permute: forall {X} (G0:list X) T2 n j,
(open j (VarF (n + S (length G0))) (splice (length G0) T2)) =
(splice (length G0) (open j (VarF (n + length G0)) T2)).
Proof.
  intros.
  assert (VarF (n + S (length G0)) = vr_splice (length G0) (VarF (n + length G0))) as A. {
    simpl. unfold splice_var.
    case_eq (le_lt_dec (length G0) (n + length G0)); intros EL LE.
    f_equal. omega. omega.
  }
  rewrite A. symmetry.
  eapply (proj2 splice_open_distribute_rec).
Qed.

Lemma splice_open_permute0: forall {X} (G0:list X) T2 j,
(open j (VarF (S (length G0))) (splice (length G0) T2)) =
(splice (length G0) (open j (VarF (length G0)) T2)).
Proof.
  intros.
  change (VarF (length G0)) with (VarF (0 + (length G0))).
  rewrite <- splice_open_permute. reflexivity.
Qed.

Lemma index_splice_hi: forall G0 G2 x0 v1 T,
    index x0 (G2 ++ G0) = Some T ->
    length G0 <= x0 ->
    index (x0 + 1) (map (splice (length G0)) G2 ++ v1 :: G0) = Some (splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply index_max in H. simpl in H. omega.
  - simpl in H.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). {
        eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.
      }
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply index_extend. eapply H. eauto.
Qed.

Lemma index_splice_lo0: forall {X} G0 G2 x0 (T:X),
    index x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    index x0 G0 = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl in H. apply H.
  - simpl in H.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E. subst.
      rewrite app_length in H0. apply plus_lt_contra in H0. inversion H0.
    + rewrite E in H. apply IHG2. apply H. apply H0.
Qed.

Lemma index_splice_lo: forall G0 G2 x0 v1 T f,
    index x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    index x0 (map (splice f) G2 ++ v1 :: G0) = Some T.
Proof.
  intros.
  assert (index x0 G0 = Some T). eapply index_splice_lo0; eauto.
  eapply index_extend_mult. eapply index_extend. eauto.
Qed.

Lemma closed_splice_rec:
  (forall i k v1, vr_closed i k v1 -> forall n, vr_closed (S i) k (vr_splice n v1)) /\
  (forall i k T1, closed i k T1 -> forall n, closed (S i) k (splice n T1)) /\
  (forall i k t1, tm_closed i k t1 -> forall n, tm_closed (S i) k (tm_splice n t1)) /\
  (forall i k d1, dm_closed i k d1 -> forall n, dm_closed (S i) k (dm_splice n d1)) /\
  (forall i k ds1, dms_closed i k ds1 -> forall n, dms_closed (S i) k (dms_splice n ds1)).
Proof.
  apply closed_mutind; intros; econstructor; eauto;
  try solve [omega];
  try solve [eapply H; omega];
  try solve [eapply H0; omega];
  try solve [eapply H1; omega].
  unfold splice_var.
  case_eq (le_lt_dec n x); intros E LE; omega.
Qed.

Lemma closed_splice: forall i k T n,
  closed i k T ->
  closed (S i) k (splice n T).
Proof.
  intros.
  eapply (proj2 closed_splice_rec); eauto.
Qed.

Lemma map_splice_length_inc: forall G0 G2 v1,
   (length (map (splice (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma closed_inc_mult: forall i k T,
  closed i k T -> forall i' k',
  i' >= i -> k' >= k ->
  closed i' k' T.
Proof.
  intros.
  eapply closed_upgrade_gh.
  eapply closed_upgrade.
  eassumption.
  omega. omega.
Qed.

Lemma closed_inc: forall i k T,
  closed i k T ->
  closed (S i) k T.
Proof.
  intros. apply (closed_inc_mult i k T H (S i) k); omega.
Qed.

Lemma closed_splice_idem_rec:
  (forall i k v1, vr_closed i k v1 -> forall n, n >= i -> vr_splice n v1 = v1) /\
  (forall i k T1, closed i k T1 -> forall n, n >= i -> splice n T1 = T1) /\
  (forall i k t1, tm_closed i k t1 -> forall n, n >= i -> tm_splice n t1 = t1) /\
  (forall i k d1, dm_closed i k d1 -> forall n, n >= i -> dm_splice n d1 = d1) /\
  (forall i k ds1, dms_closed i k ds1 -> forall n, n >= i -> dms_splice n ds1 = ds1).
Proof.
  apply closed_mutind; intros; eauto; simpl;
  try (rewrite H); try (rewrite H0); try (rewrite H1); eauto.
  unfold splice_var.
  case_eq (le_lt_dec n x); intros E LE.
  omega. reflexivity.
Qed.

Lemma closed_splice_idem: forall i k T n,
                            closed i k T ->
                            n >= i ->
                            splice n T = T.
Proof.
  intros.
  eapply (proj2 closed_splice_idem_rec); eauto.
Qed.

Lemma length_dms_splice: forall ds n,
  (length (dms_to_list ds))=(length (dms_to_list (dms_splice n ds))).
Proof.
  intros. induction ds; eauto.
  simpl. rewrite IHds. reflexivity.
Qed.

Lemma dm_splice_self: forall k n ds l D,
  vr_closed k 0 (VObj ds) ->
  index l (dms_to_list (subst_dms ds ds)) = Some D ->
  index l (dms_to_list (subst_dms (dms_splice n ds) (dms_splice n ds))) = Some (dm_splice n D).
Proof.
  intros k n ds l D HCds HI.
  inversion HCds; subst. clear HCds. rename H2 into HCds.
  remember ds as ds0. rewrite -> Heqds0 in *.
  rewrite <- Heqds0 in HI at 1. rewrite <- Heqds0 at 1. clear Heqds0.
  generalize dependent D. generalize dependent ds0.
  induction HCds; intros.
  - simpl in *. solve by inversion.
  - simpl in *.
    rewrite <- length_dms_open in *. rewrite <- length_dms_splice in *.
    case_eq (beq_nat l (length (dms_to_list ds2))); intros E;
    rewrite -> E in *.
    + inversion HI; subst. f_equal.
      rewrite (proj1 (proj2 (proj2 (proj2 splice_open_distribute_rec)))).
      simpl. reflexivity.
    + unfold subst_dms in *. specialize (IHHCds ds0 D HI). rewrite IHHCds.
      reflexivity.
Qed.

Lemma dm_splice_self_dty: forall k n ds l T,
  vr_closed k 0 (VObj ds) ->
  index l (dms_to_list (subst_dms ds ds)) = Some (dty T) ->
  index l (dms_to_list (subst_dms (dms_splice n ds) (dms_splice n ds))) = Some (dty (splice n T)).
Proof.
  intros.
  assert (dty (splice n T) = dm_splice n (dty T)) as A by eauto.
  rewrite A.
  eapply dm_splice_self; eauto.
Qed.


(* Reduction semantics  *)
Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall f l x T1 T2 t12,
    index l (dms_to_list (subst_dms f f)) = Some (dfun T1 T2 t12) ->
    step (tapp (tvar (VObj f)) l (tvar (VObj x))) (subst_tm x t12)
| ST_App1 : forall t1 t1' l t2,
    step t1 t1' ->
    step (tapp t1 l t2) (tapp t1' l t2)
| ST_App2 : forall f t2 l t2',
    step t2 t2' ->
    step (tapp (tvar (VObj f)) l t2) (tapp (tvar (VObj f)) l t2')
.


