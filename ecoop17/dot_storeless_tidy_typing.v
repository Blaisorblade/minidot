Require Import dot_storeless_tidy.
Require Import Omega.

Inductive has_type : tenv -> tm -> ty -> nat -> Prop :=
  | T_VObj : forall GH ds ds' T T' TO n1,
      dms_has_type (T'::GH) ds' T' n1 ->
      T' = open 0 (VarF (length GH)) T ->
      ds' = dms_open 0 (VarF (length GH)) ds ->
      closed (length GH) 1 T ->
      dms_closed (length GH) 1 ds ->
      TO = open 0 (VObj ds) T ->
      has_type GH (tvar (VObj ds)) TO (S n1)
  | T_VarF : forall GH x T n1,
      index x GH = Some T ->
      closed (S x) 0 T ->
      has_type GH (tvar (VarF x)) T (S n1)
  | T_VarPack : forall GH v T1 T1' n1,
      has_type GH (tvar v) T1' n1 ->
      T1' = (open 0 v T1) ->
      closed (length GH) 1 T1 ->
      has_type GH (tvar v) (TBind T1) (S n1)
  | T_VarUnpack : forall GH v T1 T1' n1,
      has_type GH (tvar v) (TBind T1) n1 ->
      T1' = (open 0 v T1) ->
      closed (length GH) 0 T1' ->
      has_type GH (tvar v) T1' (S n1)
  | T_App : forall l T1 T2 GH t1 t2 n1 n2,
      has_type GH t1 (TFun l T1 T2) n1 ->
      has_type GH t2 T1 n2 ->
      closed (length GH) 0 T2 ->
      has_type GH (tapp t1 l t2) T2 (S (n1+n2))
  | T_AppVar : forall l T1 T2 T2' GH t1 v2 n1 n2,
      has_type GH t1 (TFun l T1 T2) n1 ->
      has_type GH (tvar v2) T1 n2 ->
      vr_closed (length GH) 0 v2 ->
      T2' = (open 0 v2 T2) ->
      closed (length GH) 0 T2' ->
      has_type GH (tapp t1 l (tvar v2)) T2' (S (n1+n2))
  | T_Sub : forall GH t T1 T2 n1 n2,
      has_type GH t T1 n1 ->
      stp GH T1 T2 n2 ->
      has_type GH t T2 (S (n1 + n2))
with dm_has_type: tenv -> lb -> dm -> ty -> nat -> Prop :=
  | D_Mem : forall GH l T11 n1 g,
      closed (length GH) 0 T11 ->
      dm_has_type GH l (dty T11 g) (TMem l T11 T11) (S n1)
  | D_Fun : forall GH l T11 T12 T12' t12 t12' n1,
      has_type (T11::GH) t12' T12' n1 ->
      T12' = (open 0 (VarF (length GH)) T12) ->
      t12' = (tm_open 0 (VarF (length GH)) t12) ->
      closed (length GH) 0 T11 ->
      closed (length GH) 1 T12 ->
      tm_closed (length GH) 1 t12 ->
      dm_has_type GH l (dfun T11 T12 t12) (TFun l T11 T12) (S n1)
with dms_has_type: tenv -> dms -> ty -> nat -> Prop :=
  | D_Nil : forall GH n1,
      dms_has_type GH dnil TTop (S n1)
  | D_Cons : forall GH l d T ds TS n1 n2,
      l = length (dms_to_list ds) ->
      dm_has_type GH l d T n1 ->
      dms_has_type GH ds TS n2 ->
      dms_has_type GH (dcons d ds) (TAnd T TS) (S (n1+n2))

with stp: tenv -> ty -> ty -> nat -> Prop :=
| stp_bot: forall GH T n1,
    closed (length GH) 0  T ->
    stp GH TBot T (S n1)
| stp_top: forall GH T n1,
    closed (length GH) 0 T ->
    stp GH T  TTop (S n1)
| stp_fun: forall GH l T1 T2 T3 T4 T2' T4' n1 n2,
    T2' = (open 0 (VarF (length GH)) T2) ->
    T4' = (open 0 (VarF (length GH)) T4) ->
    closed (length GH) 1 T2 ->
    closed (length GH) 1 T4 ->
    stp GH T3 T1 n1 ->
    stp (T3::GH) T2' T4' n2 ->
    stp GH (TFun l T1 T2) (TFun l T3 T4) (S (n1+n2))
| stp_mem: forall GH l T1 T2 T3 T4 n1 n2,
    stp GH T3 T1 n2 ->
    stp GH T2 T4 n1 ->
    stp GH (TMem l T1 T2) (TMem l T3 T4) (S (n1+n2))

| stp_selx: forall GH l v1 n1,
    vr_closed (length GH) 0 v1 ->
    stp GH (TSel v1 l) (TSel v1 l) (S n1)

| stp_strong_sel1: forall GH l ds TX n1 g,
    index l (dms_to_list (subst_dms ds ds)) = Some (dty TX g) ->
    vr_closed (length GH) 0 (VObj ds) ->
    stp GH (TSel (VObj ds) l) TX (S n1)
| stp_strong_sel2: forall GH l ds TX n1 g,
    index l (dms_to_list (subst_dms ds ds)) = Some (dty TX g) ->
    vr_closed (length GH) 0 (VObj ds) ->
    stp GH TX (TSel (VObj ds) l) (S n1)

| stp_sel1: forall GH l T2 x n1,
    htp  GH x (TMem l TBot T2) n1 ->
    stp GH (TSel (VarF x) l) T2 (S n1)

| stp_sel2: forall GH l T1 x n1,
    htp  GH x (TMem l T1 TTop) n1 ->
    stp GH T1 (TSel (VarF x) l) (S n1)


| stp_bind1: forall GH T1 T1' T2 n1,
    htp (T1'::GH) (length GH) T2 n1 ->
    T1' = (open 0 (VarF (length GH)) T1) ->
    closed (length GH) 1 T1 ->
    closed (length GH) 0 T2 ->
    stp GH (TBind T1) T2 (S n1)

| stp_bindx: forall GH T1 T1' T2 T2' n1,
    htp (T1'::GH) (length GH) T2' n1 ->
    T1' = (open 0 (VarF (length GH)) T1) ->
    T2' = (open 0 (VarF (length GH)) T2) ->
    closed (length GH) 1 T1 ->
    closed (length GH) 1 T2 ->
    stp GH (TBind T1) (TBind T2) (S n1)

| stp_and11: forall GH T1 T2 T n1,
    stp GH T1 T n1 ->
    closed (length GH) 0 T2 ->
    stp GH (TAnd T1 T2) T (S n1)
| stp_and12: forall GH T1 T2 T n1,
    stp GH T2 T n1 ->
    closed (length GH) 0 T1 ->
    stp GH (TAnd T1 T2) T (S n1)
| stp_and2: forall GH T1 T2 T n1 n2,
    stp GH T T1 n1 ->
    stp GH T T2 n2 ->
    stp GH T (TAnd T1 T2) (S (n1+n2))

| stp_or21: forall GH T1 T2 T n1,
    stp GH T T1 n1 ->
    closed (length GH) 0 T2 ->
    stp GH T (TOr T1 T2) (S n1)
| stp_or22: forall GH T1 T2 T n1,
    stp GH T T2 n1 ->
    closed (length GH) 0 T1 ->
    stp GH T (TOr T1 T2) (S n1)
| stp_or1: forall GH T1 T2 T n1 n2,
    stp GH T1 T n1 ->
    stp GH T2 T n2 ->
    stp GH (TOr T1 T2) T (S (n1+n2))

| stp_trans: forall GH T1 T2 T3 n1 n2,
    stp GH T1 T2 n1 ->
    stp GH T2 T3 n2 ->
    stp GH T1 T3 (S (n1+n2))
| stp_later : forall GH T1 T2 n1,
    stp GH T1 T2 n1 ->
    stp GH (TLater T1) (TLater T2) (S n1)

with htp: tenv -> id -> ty -> nat -> Prop :=
| htp_var: forall GH x TX n1,
    index x GH = Some TX ->
    closed (S x) 0 TX ->
    htp GH x TX (S n1)
| htp_bind: forall GH x TX n1,
    htp GH x (TBind TX) n1 ->
    closed x 1 TX ->
    htp GH x (open 0 (VarF x) TX) (S n1)
| htp_sub: forall GH GU GL x T1 T2 n1 n2,
    (* use restricted GH. note: this is slightly different
    from the big-step version b/c here we do not distinguish
    if variables are bound in terms vs types. it would be easy
    to do exactly the same thing by adding this distinction. *)
    htp GH x T1 n1 ->
    stp GL T1 T2 n2 ->
    length GL = S x ->
    GH = GU ++ GL ->
    htp GH x T2 (S (n1+n2)).

Import ListNotations.

Inductive vtp(*possible types*) : nat(*pack count*) -> dms -> ty -> nat(*size*) -> Prop :=
| vtp_top: forall m ds n1,
    vr_closed 0 0 (VObj ds) ->
    vtp m ds TTop (S n1)
| vtp_mem: forall m l ds TX T1 T2 n1 n2 g,
    index l (dms_to_list (subst_dms ds ds)) = Some (dty TX g) ->
    stp [] T1 TX n1 ->
    stp [] TX T2 n2 ->
    vr_closed 0 0 (VObj ds) ->
    vtp m ds (TMem l T1 T2) (S (n1+n2))
| vtp_fun: forall m ds T l T3 T4 T1 T2 t T2' T4' ds' T' T1x T2x tx T2x' tx' n1 n2 n3 n4,
    index l (dms_to_list (subst_dms ds ds)) = Some (dfun T1 T2 t) ->
    dms_has_type [T'] ds' T' n4 ->
    T' = open 0 (VarF 0) T ->
    ds' = dms_open 0 (VarF 0) ds ->
    closed 0 1 T ->
    index l (dms_to_list ds') = Some (dfun T1x T2x tx) ->
    T2x' = (open 0 (VarF 1) T2x) ->
    tx' = (tm_open 0 (VarF 1) tx) ->
    has_type [T1x;T'] tx' T2x' n3 ->
    stp [] T3 T1 n1 ->
    T2' = (open 0 (VarF 0) T2) ->
    T4' = (open 0 (VarF 0) T4) ->
    closed 0 1 T2 ->
    closed 0 1 T4 ->
    tm_closed 1 1 tx ->
    stp [T3] T2' T4' n2 ->
    vr_closed 0 0 (VObj ds) ->
    vtp m ds (TFun l T3 T4) (S (n1+n2+n3+n4))
| vtp_bind: forall m ds T2 n1,
    vtp m ds (open 0 (VObj ds) T2) n1 ->
    closed 0 1 T2 ->
    vtp (S m) ds (TBind T2) (S (n1))
| vtp_sel: forall m ds dsy l TX n1 g,
    index l (dms_to_list (subst_dms dsy dsy)) = Some (dty TX g) ->
    vr_closed 0 0 (VObj dsy) ->
    vtp m ds TX n1 ->
    vtp m ds (TSel (VObj dsy) l) (S (n1))
| vtp_and: forall m m1 m2 ds T1 T2 n1 n2,
    vtp m1 ds T1 n1 ->
    vtp m2 ds T2 n2 ->
    m1 <= m -> m2 <= m ->
    vtp m ds (TAnd T1 T2) (S (n1+n2))
| vtp_or1: forall m m1 m2 ds T1 T2 n1,
    vtp m1 ds T1 n1 ->
    closed 0 0 T2 ->
    m1 <= m -> m2 <= m ->
    vtp m ds (TOr T1 T2) (S (n1))
| vtp_or2: forall m m1 m2 ds T1 T2 n1,
    vtp m1 ds T2 n1 ->
    closed 0 0 T1 ->
    m1 <= m -> m2 <= m ->
    vtp m ds (TOr T1 T2) (S (n1))
.

Definition has_typed GH x T1 := exists n, has_type GH x T1 n.

Definition stpd GH T1 T2 := exists n, stp GH T1 T2 n.

Definition htpd GH x T1 := exists n, htp GH x T1 n.

Definition vtpd m x T1 := exists n, vtp m x T1 n.

Definition vtpdd m x T1 := exists m1 n, vtp m1 x T1 n /\ m1 <= m.

Hint Constructors stp.
Hint Constructors vtp.

Ltac ep := match goal with
             | [ |- stp ?GH ?T1 ?T2 ?N ] => assert (exists (n:nat), stp GH T1 T2 n) as EEX
           end.

Ltac eu := match goal with
             | H: has_typed _ _ _ |- _ => destruct H as [? H]
             | H: stpd _ _ _ |- _ => destruct H as [? H]
             | H: htpd _ _ _ |- _ => destruct H as [? H]
             | H: vtpd _ _ _ |- _ => destruct H as [? H]
             | H: vtpdd _ _ _ |- _ => destruct H as [? [? [H ?]]]
           end.

Lemma stpd_bot: forall GH T,
    closed (length GH) 0 T ->
    stpd GH TBot T.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd_top: forall GH T,
    closed (length GH) 0 T ->
    stpd GH T TTop.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd_fun: forall GH l T1 T2 T3 T4 T2' T4',
    T2' = (open 0 (VarF (length GH)) T2) ->
    T4' = (open 0 (VarF (length GH)) T4) ->
    closed (length GH) 1 T2 ->
    closed (length GH) 1 T4 ->
    stpd GH T3 T1 ->
    stpd (T3::GH) T2' T4' ->
    stpd GH (TFun l T1 T2) (TFun l T3 T4).
Proof. intros. repeat eu. eexists. eapply stp_fun; eauto. Qed.
Lemma stpd_mem: forall GH l T1 T2 T3 T4,
    stpd GH T3 T1 ->
    stpd GH T2 T4 ->
    stpd GH (TMem l T1 T2) (TMem l T3 T4).
Proof. intros. repeat eu. eexists. eauto. Qed.



Lemma stpd_trans: forall GH T1 T2 T3,
    stpd GH T1 T2 ->
    stpd GH T2 T3 ->
    stpd GH T1 T3.
Proof. intros. repeat eu. eexists. eauto. Qed.




(* XXX *)
Hint Constructors stp.
Hint Constructors vtp.
Hint Constructors htp.
Hint Constructors has_type.

Hint Unfold has_typed.
Hint Unfold stpd.
Hint Unfold vtpd.
Hint Unfold vtpdd.




Lemma all_closed: forall ni,
  (forall GH T1 T2 n,
     stp GH T1 T2 n -> n < ni ->
     closed (length GH) 0 T1) /\
  (forall GH T1 T2 n,
     stp GH T1 T2 n -> n < ni ->
     closed (length GH) 0 T2) /\
  (forall m x T2 n,
     vtp m x T2 n -> n < ni ->
     closed 0 0 T2) /\
  (forall x GH T2 n,
     htp GH x T2 n -> n < ni ->
     x < length GH) /\
  (forall x GH T2 n,
     htp GH x T2 n -> n < ni ->
     closed (length GH) 0 T2) /\
  (forall GH t T n,
     has_type GH t T n -> n < ni ->
     closed (length GH) 0 T) /\
  (forall GH l d T n,
     dm_has_type GH l d T n -> n < ni ->
     closed (length GH) 0 T) /\
  (forall GH ds T n,
     dms_has_type GH ds T n -> n < ni ->
     closed (length GH) 0 T) /\
  (forall GH t T n,
     has_type GH t T n -> n < ni ->
     tm_closed (length GH) 0 t) /\
  (forall m x T2 n,
     vtp m x T2 n -> n < ni ->
     vr_closed 0 0 (VObj x)) /\
  (forall GH l d T n,
     dm_has_type GH l d T n -> n < ni ->
     dm_closed (length GH) 0 d) /\
  (forall GH ds T n,
     dms_has_type GH ds T n -> n < ni ->
     dms_closed (length GH) 0 ds).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H; destruct IHn as [IHS1 [IHS2 [IHV2 [IHH1 [IHH2 [IHT [IHD [IHD1 [IHT1 [IHV1 [IHD2 IHD3]]]]]]]]]]].
  (* stp left *)
  - econstructor.
  - eauto.
  - econstructor. eapply IHS2. eauto. omega. eauto.
  - econstructor. eapply IHS2. eauto. omega. eapply IHS1. eauto. omega.
  - subst. econstructor. eauto.
  - subst. econstructor. eauto.
  - subst.
    assert (dm_closed (length GH) 0 (dty T1 g)) as A. {
      eapply index_dm_closed. inversion H2; subst.
      eapply (proj2 (proj2 (proj2 (proj2 closed_open_rec)))).
      simpl. eassumption. eassumption.
      unfold subst_dms in *. eassumption.
    }
    inversion A; subst. eauto.
  - econstructor. econstructor. eapply IHH1. eauto. omega.
  - eapply closed_upgrade_gh. eapply IHH2 in H1. inversion H1. eauto. omega. simpl. omega.
  - econstructor. eauto.
  - econstructor. eauto.
  - econstructor. eapply IHS1. eauto. omega. eauto.
  - econstructor. eauto. eapply IHS1. eauto. omega.
  - eapply IHS1. eauto. omega.
  - eapply IHS1. eauto. omega.
  - eapply IHS1. eauto. omega.
  - econstructor. eapply IHS1. eauto. omega. eapply IHS1. eauto. omega.
  - eapply IHS1. eauto. omega.
  - Hint Constructors closed.
    constructor.
    eapply IHS1; eauto || omega.
  (* stp right *)
  - eauto.
  - econstructor.
  - econstructor. eapply IHS1. eauto. omega. eauto.
  - econstructor. eapply IHS1. eauto. omega. eapply IHS2. eauto. omega.
  - subst. econstructor. eauto.
  - subst.
    assert (dm_closed (length GH) 0 (dty T2 g)) as A. {
      eapply index_dm_closed. inversion H2; subst.
      eapply (proj2 (proj2 (proj2 (proj2 closed_open_rec)))).
      simpl. eassumption. eassumption.
      unfold subst_dms in *. eassumption.
    }
    inversion A; subst. eauto.
  - subst. econstructor. eauto.
  - eapply closed_upgrade_gh. eapply IHH2 in H1. inversion H1. eauto. omega. simpl. omega.
  - econstructor. econstructor. eapply IHH1. eauto. omega.
  - eauto.
  - econstructor. eauto.
  - eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  - econstructor. eapply IHS2. eauto. omega. eapply IHS2. eauto. omega.
  - econstructor. eapply IHS2. eauto. omega. eauto.
  - econstructor. eauto. eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  - constructor. subst. eapply IHS2; eauto || omega.
  (* vtp right *)
  - econstructor.
  - change 0 with (length ([]:tenv)) at 1. econstructor. eapply IHS1. eauto. omega. eapply IHS2. eauto. omega.
  - change 0 with (length ([]:tenv)) at 1. econstructor. eapply IHS1. eauto. omega. eauto.
  - econstructor. eauto.
  - subst. econstructor. eauto.
  - econstructor. eapply IHV2. eauto. omega. eapply IHV2. eauto. omega.
  - econstructor. eapply IHV2. eauto. omega. eauto.
  - econstructor. eauto. eapply IHV2. eauto. omega.
  (* htp left *)
  - eapply index_max. eauto.
  - eapply IHH1. eauto. omega.
  - eapply IHH1. eauto. omega.
  (* htp right *)
  - eapply closed_upgrade_gh. eauto. subst. eapply index_max in H1. omega.
  - eapply IHH1 in H1. eapply closed_open. simpl. eapply closed_upgrade_gh. eauto. omega. econstructor. eauto. omega.
  - eapply closed_upgrade_gh. eapply IHS2. eauto. omega. rewrite H4. rewrite app_length. omega.
  (* has_type *)
  - subst. eapply closed_open. simpl. eauto. econstructor. eauto.
  - subst. eapply closed_upgrade_gh. eauto. eapply index_max in H1. omega.
  - econstructor. eapply closed_upgrade_gh. eauto. omega.
  - eapply IHT in H1. inversion H1; subst. eauto. omega.
  - eapply IHT in H1. inversion H1. eauto. omega.
  - eapply IHT in H1. inversion H1. eauto. omega.
  - eapply IHS2. eauto. omega.
  (* dm_has_type *)
  - subst. econstructor. eauto. eauto.
  - subst. econstructor. eauto. eauto.
  (* dms_has_type *)
  - econstructor.
  - subst. econstructor. eapply IHD. eauto. omega. eapply IHD1. eauto. omega.
  (* has_type 1 *)
  - subst. econstructor. econstructor. eauto.
  - subst. econstructor. econstructor. eauto using index_max.
  - subst. eapply IHT1 in H1. eauto. omega.
  - subst. eapply IHT1 in H1. eauto. omega.
  - subst. eapply IHT1 in H1. eapply IHT1 in H2. econstructor. eauto. eauto. omega. omega.
  - subst. eapply IHT1 in H1. eapply IHT1 in H2. econstructor. eauto. eauto. omega. omega.
  - subst. eapply IHT1 in H1. eauto. omega.
  (* vtp 1 *)
  - subst. eauto.
  - subst. eauto.
  - subst. eauto.
  - subst. eapply IHV1 in H1. eauto. omega.
  - subst. eapply IHV1 in H3. eauto. omega.
  - subst. eapply IHV1 in H1. eauto. omega.
  - subst. eapply IHV1 in H1. eauto. omega.
  - subst. eapply IHV1 in H1. eauto. omega.
  (* dm_has_type 1 *)
  - subst. econstructor. eauto.
  - subst. econstructor. eauto. eauto. eauto.
  (* dms_has_type 1 *)
  - econstructor.
  - subst. econstructor. eapply IHD2. eauto. omega. eapply IHD3. eauto. omega.
Qed.

Lemma htp_closed: forall x GH T2 n,
  htp GH x T2 n ->
  closed (length GH) 0 T2.
Proof. intros. eapply all_closed with (x:=x). eauto. eauto. Qed.

Lemma vtp_closed: forall m x T2 n1,
  vtp m x T2 n1 ->
  closed 0 0 T2.
Proof. intros. eapply all_closed. eauto. eauto. Qed.

Lemma vtp_closed1: forall m x T2 n1,
  vtp m x T2 n1 ->
  vr_closed 0 0 (VObj x).
Proof. intros. eapply all_closed. eauto. eauto. Qed.

Lemma has_type_closed: forall GH t T n1,
  has_type GH t T n1 ->
  closed (length GH) 0 T.
Proof. intros. eapply all_closed with (t:=t). eauto. eauto. Qed.

Lemma has_type_closed1: forall GH t T n1,
  has_type GH t T n1 ->
  tm_closed (length GH) 0 t.
Proof. intros. eapply all_closed with (t:=t). eauto. eauto. Qed.

Lemma dms_has_type_closed: forall GH t T n1,
  dms_has_type GH t T n1 ->
  closed (length GH) 0 T.
Proof. intros. eapply all_closed with (ds:=t). eauto. eauto. Qed.

Lemma has_type_closed_z: forall GH z T n1,
  has_type GH (tvar (VarF z)) T n1 ->
  z < length GH.
Proof.
  intros. remember (tvar (VarF z)) as t. generalize dependent z.
  induction H; intros; inversion Heqt; subst; eauto using index_max.
Qed.

Lemma has_type_closed_b: forall v T n1,
  has_type [] (tvar v) T n1 ->
  exists ds, v = VObj ds.
 Proof.
 intros.
 remember [] as GH.
 remember (tvar v) as t.
 generalize HeqGH. clear HeqGH.
 induction H; intros; inversion Heqt; try subst; eauto using index_max.
 - simpl in H. inversion H.
Qed.

Lemma stp_closed1 : forall GH T1 T2 n1,
                      stp GH T1 T2 n1 ->
                      closed (length GH) 0 T1.
Proof. intros. edestruct all_closed. eapply H0. eauto. eauto. Qed.

Lemma stp_closed2 : forall GH T1 T2 n1,
                      stp GH T1 T2 n1 ->
                      closed (length GH) 0 T2.
Proof. intros. edestruct all_closed. destruct H1. eapply H1. eauto. eauto. Qed.

Lemma stpd_closed1 : forall GH T1 T2,
                      stpd GH T1 T2 ->
                      closed (length GH) 0 T1.
Proof. intros. eu. eapply stp_closed1. eauto. Qed.


Lemma stpd_closed2 : forall GH T1 T2,
                      stpd GH T1 T2 ->
                      closed (length GH) 0 T2.
Proof. intros. eu. eapply stp_closed2. eauto. Qed.



Lemma stpd_refl_aux: forall n GH T1,
  closed (length GH) 0 T1 ->
  tsize T1 < n ->
  stpd GH T1 T1.
Proof.
  intros n. induction n; intros; try omega.
  inversion H; subst; simpl in H0.
  - Case "bot". exists 1. eauto.
  - Case "top". exists 1. eauto.
  - Case "fun". eapply stpd_fun; eauto.
    eapply IHn; eauto; omega.
    eapply IHn; eauto.
    simpl. apply closed_open. simpl. eapply closed_upgrade_gh. eauto. omega.
    econstructor. omega.
    rewrite <- open_preserves_size. omega.
  - Case "mem". eapply stpd_mem; try eapply IHn; eauto; try omega.
  - Case "sel". exists 1. eapply stp_selx. eauto.
  - Case "bind".
    eexists. eapply stp_bindx. eapply htp_var. simpl. rewrite beq_nat_true_eq. eauto.
    instantiate (1:=open 0 (VarF (length GH)) T0).
    eapply closed_open. eapply closed_upgrade_gh. eauto. omega. econstructor. omega.
    eauto. eauto. eauto. eauto.
  - Case "and".
    destruct (IHn GH T0 H1). omega.
    destruct (IHn GH T2 H2). omega.
    eexists. eapply stp_and2. eapply stp_and11. eauto. eauto. eapply stp_and12. eauto. eauto.
  - Case "or".
    destruct (IHn GH T0 H1). omega.
    destruct (IHn GH T2 H2). omega.
    eexists. eapply stp_or1. eapply stp_or21. eauto. eauto. eapply stp_or22. eauto. eauto.
  - Case "TLater".
    destruct (IHn GH T0 H1); try omega.
    Hint Constructors stp.
    eexists; eauto 10.
Grab Existential Variables.
apply 0.
Qed.

Lemma stpd_refl: forall GH T1,
  closed (length GH) 0 T1 ->
  stpd GH T1 T1.
Proof.
  intros. apply stpd_refl_aux with (n:=S (tsize T1)); eauto.
Qed.

Lemma stpd_reg1 : forall GH T1 T2,
                      stpd GH T1 T2 ->
                      stpd GH T1 T1.
Proof. intros. eapply stpd_refl. eapply stpd_closed1. eauto. Qed.

Lemma stpd_reg2 : forall GH T1 T2,
                      stpd GH T1 T2 ->
                      stpd GH T2 T2.
Proof. intros. eapply stpd_refl. eapply stpd_closed2. eauto. Qed.



Lemma stp_splice_aux: forall ni, (forall G0 G1 T1 T2 v1 n,
   stp (G1++G0) T1 T2 n -> n < ni ->
   stp ((map (splice (length G0)) G1) ++ v1::G0)
   (splice (length G0) T1) (splice (length G0) T2) n) /\
  (forall G0 G1 x1 T1 v1 n,
   htp (G1++G0) x1 T1 n -> n < ni ->
   htp ((map (splice (length G0)) G1) ++ v1::G0)
   (splice_var (length G0) x1) (splice (length G0) T1) n).
Proof.
  intro ni. induction ni. split; intros; omega.
  destruct IHni as [IHstp IHhtp].
  split; intros; inversion H; subst.
  - Case "bot".
    eapply stp_bot.
    rewrite map_splice_length_inc.
    simpl. apply closed_splice.
    assumption.
  - Case "top".
    eapply stp_top.
    rewrite map_splice_length_inc.
    apply closed_splice.
    assumption.
  - Case "fun".
    eapply stp_fun.
    eauto. eauto.
    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.
    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.
    eapply IHstp. eauto. omega.
    specialize (IHstp G0 (T4::G1)).
    simpl in IHstp. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0).
    eapply IHstp. rewrite <- app_length. eauto. omega.
  - Case "mem".
    eapply stp_mem.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "selx". simpl. inversion H1; subst.
    + simpl. unfold splice_var.
      case_eq (le_lt_dec (length G0) x); intros E LE.
      * eapply stp_selx.
        rewrite map_splice_length_inc. econstructor. omega.
      * eapply stp_selx.
        rewrite map_splice_length_inc. econstructor. omega.
    + simpl. inversion H1; subst. omega.
    + simpl. eapply stp_selx.
      rewrite map_splice_length_inc. econstructor.
      eapply (proj2 (proj2 (proj2 (proj2 closed_splice_rec)))). eauto.
  - Case "ssel1". simpl.
    eapply stp_strong_sel1.
    eapply dm_splice_self_dty; eauto.
    rewrite map_splice_length_inc.
    assert (VObj (dms_splice (length G0) ds) = vr_splice (length G0) (VObj ds)) as A. {
      simpl. reflexivity.
    }
    rewrite A. eapply (proj1 closed_splice_rec). eauto.
  - Case "ssel2". simpl.
    eapply stp_strong_sel2.
    eapply dm_splice_self_dty; eauto.
    rewrite map_splice_length_inc.
    assert (VObj (dms_splice (length G0) ds) = vr_splice (length G0) (VObj ds)) as A. {
      simpl. reflexivity.
    }
    rewrite A. eapply (proj1 closed_splice_rec). eauto.
  - Case "sel1".
    eapply stp_sel1.
    specialize (IHhtp G0 G1 x (TMem l TBot T2)). simpl in IHhtp.
    eapply IHhtp. eauto. omega.
  - Case "sel2".
    eapply stp_sel2.
    specialize (IHhtp G0 G1 x (TMem l T1 TTop)). simpl in IHhtp.
    eapply IHhtp. eauto. omega.
  - Case "bind1".
    eapply stp_bind1.
    rewrite map_splice_length_inc.
    assert (splice_var (length G0) (length (G1 ++ G0)) = (S (length (G1 ++ G0)))) as A. {
      unfold splice_var.
      case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros E LE.
      omega. clear LE. rewrite app_length in E. omega.
    }
    rewrite <- A.
    specialize (IHhtp G0 (open 0 (VarF (length (G1 ++ G0))) T0 :: G1)).
    simpl in IHhtp. eapply IHhtp. eauto. omega.
    rewrite app_length. rewrite <- splice_open_permute.
    rewrite map_splice_length_inc. rewrite app_length.
    assert (length G1 + S (length G0)=(S (length G1 + length G0))) as B by omega.
    rewrite B. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "bindx".
    assert (length G1 + S (length G0)=(S (length G1 + length G0))) as B by omega.
    eapply stp_bindx.
    rewrite map_splice_length_inc.
    assert (splice_var (length G0) (length (G1 ++ G0)) = (S (length (G1 ++ G0)))) as A. {
      unfold splice_var.
      case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros E LE.
      omega. clear LE. rewrite app_length in E. omega.
    }
    rewrite <- A.
    specialize (IHhtp G0 (open 0 (VarF (length (G1 ++ G0))) T0 :: G1)).
    simpl in IHhtp. eapply IHhtp. eauto. omega.
    rewrite app_length. rewrite <- splice_open_permute.
    rewrite map_splice_length_inc. rewrite app_length.
    rewrite B. eauto.
    rewrite app_length. rewrite <- splice_open_permute.
    rewrite map_splice_length_inc. rewrite app_length.
    rewrite B. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "and11".
    simpl. eapply stp_and11.
    eapply IHstp. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "and12".
    simpl. eapply stp_and12.
    eapply IHstp. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "and2".
    simpl. eapply stp_and2.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "or21".
    simpl. eapply stp_or21.
    eapply IHstp. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "or22".
    simpl. eapply stp_or22.
    eapply IHstp. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "or1".
    simpl. eapply stp_or1.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "trans".
    eapply stp_trans.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "tlater".
    constructor.
    eapply IHstp; eauto || omega.
  - Case "htp_var".
    unfold splice_var.
    case_eq (le_lt_dec (length G0) x1); intros E LE.
    + eapply htp_var.
      apply index_splice_hi. eauto. eauto.
      eapply closed_splice.
      assert (S x1 = x1 + 1) as A by omega.
      rewrite <- A. eauto.
    + assert (splice (length G0) T1=T1) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      eapply htp_var.
      eapply index_splice_lo.
      rewrite A. eauto. omega.
      rewrite A. eauto.
  - Case "htp_bind".
    unfold splice_var.
    case_eq (le_lt_dec (length G0) x1); intros E LE.
    + remember (x1 - (length G0)) as n.
      assert (x1 = n + length G0) as A. {
        clear LE. apply le_plus_minus in E.
        rewrite E. unfold id in *. omega.
      }
      rewrite A at 2.
      rewrite <- splice_open_permute.
      assert (n + S (length G0)=x1+1) as B. {
        rewrite Heqn. omega.
      }
      rewrite B.
      eapply htp_bind.
      specialize (IHhtp G0 G1 x1 (TBind TX)).
      simpl in IHhtp. unfold splice_var in IHhtp. rewrite LE in IHhtp.
      eapply IHhtp. eauto. omega.
      assert (S x1 = x1 + 1) as C by omega. rewrite <- C.
      eapply closed_splice. eauto.
    + assert (splice (length G0) TX = TX) as A. {
        eapply closed_splice_idem. eauto. omega.
      }
      assert (splice (length G0) (open 0 (VarF x1) TX)=open 0 (VarF x1) TX) as B. {
        eapply closed_splice_idem.
        eapply closed_open. eapply closed_upgrade_gh. eauto.
        instantiate (1:=S x1). omega.
        econstructor. omega. omega.
      }
      rewrite B.
      eapply htp_bind.
      specialize (IHhtp G0 G1 x1 (TBind TX)).
      simpl in IHhtp. unfold splice_var in IHhtp. rewrite LE in IHhtp.
      rewrite <- A. eapply IHhtp. eauto. omega. eauto.
  - Case "htp_sub".
    unfold splice_var.
    case_eq (le_lt_dec (length G0) x1); intros E LE.
    + assert (S x1 = x1 + 1) as A by omega.
      assert (exists GH1L, G1 = GU ++ GH1L /\ GL = GH1L ++ G0) as EQGH. {
        eapply exists_GH1L. eauto. omega.
      }
      destruct EQGH as [GH1L [EQGH1 EQGL]].
      assert (splice_var (length G0) x1=x1+1) as B. {
        unfold splice_var. rewrite LE. reflexivity.
      }
      rewrite <- B.
      eapply htp_sub.
      eapply IHhtp. eauto. omega.
      eapply IHstp. subst. eauto. omega.
      rewrite app_length. rewrite map_length. simpl.
      unfold splice_var. rewrite LE. subst. rewrite app_length in *. omega.
      subst. rewrite map_app. simpl. rewrite app_assoc. reflexivity.
    + assert (splice (length G0) T1=T1) as A1. {
        eapply closed_splice_idem. eapply stp_closed2. eauto. omega.
      }
      assert (splice (length G0) T0=T0) as A0. {
        eapply closed_splice_idem. eapply stp_closed1. eauto. omega.
      }
      assert (exists GH0U, G0 = GH0U ++ GL) as EQGH. {
        eapply exists_GH0U. eauto. omega.
      }
      destruct EQGH as [GH0U EQGH].
      assert (splice_var (length G0) x1=x1) as C. {
        unfold splice_var. rewrite LE. reflexivity.
      }
      rewrite <- C.
      eapply htp_sub.
      eapply IHhtp. eauto. omega.
      rewrite A1. rewrite A0. eauto.
      rewrite C. eauto.
      instantiate (1:=(map (splice (length G0)) G1 ++ v1 :: GH0U)).
      rewrite <- app_assoc. simpl. rewrite EQGH. reflexivity.
Qed.

Lemma stp_splice: forall G0 G1 T1 T2 v1 n,
   stp (G1++G0) T1 T2 n ->
   stp ((map (splice (length G0)) G1) ++ v1::G0)
   (splice (length G0) T1) (splice (length G0) T2) n.
Proof. intros. eapply stp_splice_aux. eauto. eauto. Qed.

Lemma htp_splice: forall G0 G1 x1 T1 v1 n,
   htp (G1++G0) x1 T1 n ->
   htp ((map (splice (length G0)) G1) ++ v1::G0)
   (splice_var (length G0) x1) (splice (length G0) T1) n.
Proof. intros. eapply stp_splice_aux. eauto. eauto. Qed.

Lemma stp_upgrade_gh_aux: forall ni,
  (forall GH T T1 T2 n,
     stp GH T1 T2 n -> n < ni ->
     stp (T::GH) T1 T2 n) /\
  (forall T x GH T2 n,
     htp GH x T2 n -> n < ni ->
     htp (T::GH) x T2 n).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H.
  (* stp *)
  - econstructor. eapply closed_upgrade_gh. eauto. simpl. omega.
  - econstructor. eapply closed_upgrade_gh. eauto. simpl. omega.
  - econstructor. eauto. eauto.
    eapply closed_upgrade_gh. eauto. simpl. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
    eapply IHn. eauto. omega.
    subst.
    assert (splice (length GH) T0 = T0) as A. {
      eapply closed_splice_idem. eapply stp_closed2. eauto. omega.
    }
    assert (splice (length GH) T4 = T4) as B. {
      eapply closed_splice_idem. eapply stp_closed1. eauto. omega.
    }
    assert (splice (length GH) T3 = T3) as C. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (splice (length GH) T5 = T5) as D. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (map (splice (length GH)) [T4] ++ T::GH =
          (T4::T::GH)) as HGX. {
      simpl. rewrite B. eauto.
    }
    simpl. change (S (length GH)) with (0 + (S (length GH))).
    rewrite <- C. rewrite <- D.
    rewrite splice_open_permute. rewrite splice_open_permute.
    rewrite <- HGX.
    apply stp_splice. simpl. eauto.

  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - subst. econstructor. simpl. eapply (proj1 closed_upgrade_gh_rec). eauto. omega.
  - subst. econstructor. eauto. simpl. eapply (proj1 closed_upgrade_gh_rec). eauto. omega.
  - subst. econstructor. eauto. simpl. eapply (proj1 closed_upgrade_gh_rec). eauto. omega.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega.
  - subst.
    assert (splice (length GH) T0 = T0) as A. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (splice (length GH) T2 = T2) as B. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (length (T :: GH)=splice_var (length GH) (length GH)) as C. {
      unfold splice_var. simpl.
      case_eq (le_lt_dec (length GH) (length GH)); intros E LE; omega.
    }
    assert (map (splice (length GH)) [(open 0 (VarF (length GH)) T0)] ++ T::GH =
          (((open 0 (VarF (S (length GH))) (splice (length GH) T0)))::T::GH)) as HGX. {
      simpl. rewrite <- splice_open_permute0. reflexivity.
    }
    eapply stp_bind1.
    rewrite <- B.
    instantiate (1:=(open 0 (VarF (S (length GH))) (splice (length GH) T0))).
    rewrite <- HGX. rewrite C.
    apply htp_splice. simpl. eauto. simpl. rewrite A. reflexivity.
    eapply closed_upgrade_gh. eauto. simpl. omega.
    eapply closed_upgrade_gh. eauto. simpl. omega.

  - subst.
    assert (splice (length GH) T0 = T0) as A. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (splice (length GH) T3 = T3) as B. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (length (T :: GH)=splice_var (length GH) (length GH)) as C. {
      unfold splice_var. simpl.
      case_eq (le_lt_dec (length GH) (length GH)); intros E LE; omega.
    }
    assert (map (splice (length GH)) [(open 0 (VarF (length GH)) T0)] ++ T::GH =
          (((open 0 (VarF (S (length GH))) (splice (length GH) T0)))::T::GH)) as HGX. {
      simpl. rewrite <- splice_open_permute0. reflexivity.
    }
    eapply stp_bindx.
    instantiate (2:=(open 0 (VarF (S (length GH))) (splice (length GH) T0))).
    rewrite <- HGX. rewrite C.
    apply htp_splice. simpl. eauto. simpl. rewrite A. reflexivity.
    simpl. rewrite <- splice_open_permute0. rewrite B. reflexivity.
    eapply closed_upgrade_gh. eauto. simpl. omega.
    eapply closed_upgrade_gh. eauto. simpl. omega.

  - eapply stp_and11. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_and12. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_and2. eapply IHn. eauto. omega. eapply IHn. eauto. omega.

  - eapply stp_or21. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_or22. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_or1. eapply IHn. eauto. omega. eapply IHn. eauto. omega.

  - eapply stp_trans. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - constructor; eapply IHn; eauto || omega.
  (* htp *)
  - econstructor. eapply index_extend. eauto. eapply closed_upgrade_gh. eauto. omega.
  - eapply htp_bind. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. omega.
  - eapply htp_sub. eapply IHn. eauto. omega. eauto. eauto. subst GH.
    instantiate (1:=T::GU). eauto.
Qed.

Lemma stp_upgrade_gh : forall GH T T1 T2 n,
                      stp GH T1 T2 n ->
                      stp (T::GH) T1 T2 n.
Proof.
  intros. eapply stp_upgrade_gh_aux. eauto. eauto.
Qed.

Lemma stp_upgrade_gh_mult : forall GH GH' T1 T2 n,
                      stp GH T1 T2 n ->
                      stp (GH'++GH) T1 T2 n.
Proof. intros. induction GH'. simpl. eauto. simpl. eapply stp_upgrade_gh. eauto. Qed.

Lemma stp_upgrade_gh_mult0 : forall GH T1 T2 n,
                      stp [] T1 T2 n ->
                      stp GH T1 T2 n.
Proof. intros. rewrite <- (app_nil_r GH). eapply stp_upgrade_gh_mult. eauto. Qed.

Lemma hastp_splice_aux: forall ni, (forall G0 G1 t1 T2 v1 n,
   has_type (G1++G0) t1 T2 n -> n < ni ->
   has_type ((map (splice (length G0)) G1) ++ v1::G0)
   (tm_splice (length G0) t1) (splice (length G0) T2) n) /\
   (forall G0 G1 l d1 T2 v1 n,
   dm_has_type (G1++G0) l d1 T2 n -> n < ni ->
   dm_has_type ((map (splice (length G0)) G1) ++ v1::G0) l
   (dm_splice (length G0) d1) (splice (length G0) T2) n) /\
   (forall G0 G1 ds1 T2 v1 n,
   dms_has_type (G1++G0) ds1 T2 n -> n < ni ->
   dms_has_type ((map (splice (length G0)) G1) ++ v1::G0)
   (dms_splice (length G0) ds1) (splice (length G0) T2) n).
Proof.
  intro ni. induction ni. repeat split; intros; omega.
  destruct IHni as [IHT [IHD IHDS]].
  repeat split; intros; inversion H; subst.
  - assert ((length (G1 ++ G0) + 1) = S (length (G1 ++ G0))) as EqInc by omega.
    assert (dms_has_type (map (splice (length G0)) (open 0 (VarF (length (G1 ++ G0))) T :: G1) ++ v1::G0)
         (dms_splice (length G0) (dms_open 0 (VarF (length (G1 ++ G0))) ds))
         (splice (length G0) (open 0 (VarF (length (G1 ++ G0))) T)) n1) as IH. {
      eapply IHDS. simpl in *. eapply H1. omega.
    }
    simpl. eapply T_VObj.
    + eapply IH.
    + rewrite (proj1 (proj2 splice_open_distribute_rec)).
      simpl. unfold splice_var.
      case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros LE E.
      rewrite map_splice_length_inc. rewrite EqInc. reflexivity.
      clear E. rewrite app_length in LE. omega.
    + rewrite (proj2 (proj2 (proj2 (proj2 splice_open_distribute_rec)))).
      simpl. unfold splice_var.
      case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros LE E.
      rewrite map_splice_length_inc. rewrite EqInc. reflexivity.
      clear E. rewrite app_length in LE. omega.
    + rewrite map_splice_length_inc. eapply closed_splice. eauto.
    + rewrite map_splice_length_inc. eapply closed_splice_rec. eauto.
    + rewrite (proj1 (proj2 splice_open_distribute_rec)).
      simpl. reflexivity.
  - simpl. unfold splice_var.
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply T_VarF. apply index_splice_hi. eauto. omega.
      eapply closed_splice.
      assert (S x = x + 1) as A by omega.
      rewrite <- A. eauto.
    + assert (splice (length G0) T2=T2) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite A. eapply T_VarF. eapply index_splice_lo. eauto. omega. eauto.
  - simpl. eapply T_VarPack.
    assert (tvar (vr_splice (length G0) v) = tm_splice (length G0) (tvar v)) as A. {
      simpl. reflexivity.
    }
    rewrite A. eapply IHT. eauto. omega.
    rewrite (proj1 (proj2 splice_open_distribute_rec)). reflexivity.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - simpl. eapply T_VarUnpack.
    specialize (IHT G0 G1 (tvar v) (TBind T1) v1 n1). simpl in IHT.
    eapply IHT. eauto. omega.
    rewrite (proj1 (proj2 splice_open_distribute_rec)). reflexivity.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - simpl. eapply T_App.
    specialize (IHT G0 G1 t0 (TFun l T1 T2) v1 n1). simpl in IHT.
    eapply IHT. eauto. omega.
    eapply IHT. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - simpl. eapply T_AppVar.
    specialize (IHT G0 G1 t0 (TFun l T1 T0) v1 n1). simpl in IHT.
    eapply IHT. eauto. omega.
    specialize (IHT G0 G1 (tvar v2) T1 v1 n2). simpl in IHT.
    eapply IHT. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice_rec. eauto.
    rewrite (proj1 (proj2 splice_open_distribute_rec)). reflexivity.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - eapply T_Sub. eapply IHT. eauto. omega. eapply stp_splice. eauto.
  - simpl. eapply D_Mem.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - assert ((length (G1 ++ G0) + 1) = S (length (G1 ++ G0))) as EqInc by omega.
    simpl. eapply D_Fun.
    assert (splice (length G0) T11 :: map (splice (length G0)) G1 ++ v1 :: G0 =
            map (splice (length G0)) (T11::G1) ++ v1 :: G0) as A. {
      simpl. reflexivity.
    }
    rewrite A. eapply IHT. simpl. eauto. omega.
    rewrite (proj1 (proj2 splice_open_distribute_rec)).
    simpl. rewrite map_splice_length_inc. unfold splice_var.
    case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros LE E.
    rewrite EqInc. reflexivity.
    clear E. rewrite app_length in LE. omega.
    rewrite (proj1 (proj2 (proj2 splice_open_distribute_rec))).
    simpl. rewrite map_splice_length_inc. unfold splice_var.
    case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros LE E.
    rewrite EqInc. reflexivity.
    clear E. rewrite app_length in LE. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
    rewrite map_splice_length_inc. eapply closed_splice_rec. eauto.
  - eapply D_Nil.
  - eapply D_Cons.
    * fold dms_splice in *. reflexivity.
    * fold splice in *. fold dm_splice in *. eapply IHD.
      + rewrite <- length_dms_splice. eauto.
      + omega.
    * fold splice in *. fold dms_splice in *. eapply IHDS.
      + assumption.
      + omega.
Qed.



Lemma dms_hastp_splice: forall G0 G1 ds1 T2 v1 n,
   dms_has_type (G1++G0) ds1 T2 n ->
   dms_has_type ((map (splice (length G0)) G1) ++ v1::G0)
   (dms_splice (length G0) ds1) (splice (length G0) T2) n.
Proof. intros. eapply hastp_splice_aux. eauto. eauto. Qed.

Lemma hastp_upgrade_gh_aux: forall ni,
  (forall GH T t1 T2 n,
     has_type GH t1 T2 n -> n < ni ->
     has_type (T::GH) t1 T2 n).
Proof.
  intros n. induction n. repeat split; intros; omega.
  intros; inversion H; subst.
  - assert (dms_has_type (map (splice (length GH)) [(open 0 (VarF (length GH)) T0)] ++ (T::GH))
                         (dms_splice (length GH) (dms_open 0 (VarF (length GH)) ds))
                         (splice (length GH) (open 0 (VarF (length GH)) T0)) n1) as IH'. {
      eapply dms_hastp_splice. simpl. eauto.
    }
    assert ((length GH + 1) = (S (length GH))) as EqInc by omega.
    assert (splice (length GH) T0 = T0) as EqT0. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (dms_splice (length GH) ds = ds) as Eqds. {
      eapply closed_splice_idem_rec. eauto. omega.
    }
    assert (dms_has_type (open 0 (VarF (S (length GH))) T0 :: T :: GH) (dms_open 0 (VarF (S (length GH))) ds) (open 0 (VarF (S (length GH))) T0) n1) as IH. {
      simpl in IH'.
      rewrite (proj1 (proj2 splice_open_distribute_rec)) in IH'.
      rewrite (proj2 (proj2 (proj2 (proj2 splice_open_distribute_rec)))) in IH'.
      simpl in IH'. unfold splice_var in IH'. simpl in IH'.
      case_eq (le_lt_dec (length GH) (length GH)); intros LE E.
      rewrite E in IH'. rewrite EqInc in IH'. rewrite EqT0 in IH'. rewrite Eqds in IH'.
      eapply IH'.
      omega.
    }
    eapply T_VObj. eapply IH.
    simpl. reflexivity. simpl. reflexivity.
    simpl. eapply closed_upgrade_gh. eauto. omega.
    simpl. eapply (proj2 (proj2 (proj2 (proj2 closed_upgrade_gh_rec)))). eauto. omega.
    eauto.
  - eapply T_VarF. eapply index_extend. eauto.
    simpl. eapply closed_upgrade_gh. eauto. omega.
  - eapply T_VarPack. eapply IHn. eauto. omega. eauto.
    simpl. eapply closed_upgrade_gh. eauto. omega.
  - eapply T_VarUnpack. eapply IHn. eauto. omega. eauto.
    simpl. eapply closed_upgrade_gh. eauto. omega.
  - eapply T_App. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
    simpl. eapply closed_upgrade_gh. eauto. omega.
  - eapply T_AppVar. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
    simpl. eapply (proj1 closed_upgrade_gh_rec). eauto. omega.
    eauto.
    simpl. eapply closed_upgrade_gh. eauto. omega.
  - eapply T_Sub. eapply IHn. eauto. omega. eapply stp_upgrade_gh. eauto.
Qed.

Lemma hastp_upgrade_gh : forall GH T t1 T2 n,
                      has_type GH t1 T2 n ->
                      has_type (T::GH) t1 T2 n.
Proof.
  intros. eapply hastp_upgrade_gh_aux. eauto. eauto.
Qed.

Lemma hastp_upgrade_gh_mult : forall GH GH' t1 T2 n,
                      has_type GH t1 T2 n ->
                      has_type (GH'++GH) t1 T2 n.
Proof. intros. induction GH'. simpl. eauto. simpl. eapply hastp_upgrade_gh. eauto. Qed.

Lemma hastp_upgrade_gh_mult0 : forall GH t1 T2 n,
                      has_type [] t1 T2 n ->
                      has_type GH t1 T2 n.
Proof. intros. rewrite <- (app_nil_r GH). eapply hastp_upgrade_gh_mult. eauto. Qed.

Lemma hastp_upgrade_gh_var: forall GH x T n1,
  has_type [] (tvar (VObj x)) T n1 ->
  has_type GH (tvar (VObj x)) T n1.
Proof.
  intros. eapply hastp_upgrade_gh_mult0. eauto.
Qed.

Lemma hastp_upgrade_gh_var_ex: forall GH x T n1,
  has_type [] (tvar (VObj x)) T n1 ->
  exists n, has_type GH (tvar (VObj x)) T n.
Proof.
  intros. exists n1.
  induction GH. simpl. eauto. simpl. eapply hastp_upgrade_gh_var. eauto.
Qed.

(* upgrade_gh interlude ends *)

Lemma stp_subst_narrow0: forall x, vr_closed 0 0 (VObj x) ->
   forall n, forall GH T1 T2 TX n2,
   stp (GH++[TX]) T1 T2 n2 -> n2 < n ->
   (forall GH (T3 : ty) (n1 : nat),
      htp (GH++[TX]) 0 T3 n1 -> n1 < n ->
      exists m2, vtpd m2 x (substt x T3)) ->
   stpd (map (substt x) GH) (substt x T1) (substt x T2).
Proof.
  intros x Hx.
  intros n. induction n. intros. omega.
  intros ? ? ? ? ? ? ? narrowX.

  (* helper lemma for htp *)
  assert (forall ni n2, forall GH T2 xi,
    htp (GH ++ [TX]) xi T2 n2 -> xi <> 0 -> n2 < ni -> ni < S n ->
    htpd (map (substt x) GH) (xi-1) (substt x T2)) as htp_subst_narrow02. {
      induction ni. intros. omega.
      intros. inversion H1.
      + (* var *) subst.
        repeat eexists. eapply htp_var. eapply index_subst1. eauto. eauto.
        eapply closed_subst0.
        eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
        eapply closed_upgrade_gh. eauto. omega.
      + (* bind *) subst.
        assert (htpd (map (substt x) (GH0)) (xi-1) (substt x (TBind TX0))) as BB.
        eapply IHni. eapply H5. eauto. omega. omega.
        erewrite subst_open5.
        eu. repeat eexists. eapply htp_bind. eauto. eapply closed_subst1. eauto. eauto.
        eapply (proj1 closed_upgrade_gh_rec); eauto. omega. eauto.
        eauto. eauto.
      + (* sub *) subst.
        assert (exists GL0, GL = GL0 ++ [TX] /\ GH0 = GU ++ GL0) as A. eapply gh_match1. eauto. omega.
        destruct A as [GL0 [? ?]]. subst GL.
        assert (htpd (map (substt x) GH0) (xi-1) (substt x T3)) as AA.
        eapply IHni. eauto. eauto. omega. omega.
        assert (stpd (map (substt x) GL0) (substt x T3) (substt x T0)) as BB.
        eapply IHn. eauto. eauto. omega. { intros. eapply narrowX. eauto. eauto. }
        eu. eu. repeat eexists. eapply htp_sub. eauto. eauto.
        (* - *)
        rewrite map_length. rewrite app_length in H7. simpl in H7. unfold id in *. omega.
        subst GH0. rewrite map_app. eauto.
  }
  (* special case *)
  assert (forall ni n2, forall T0 T2,
    htp (T0 :: GH ++ [TX]) (length (GH ++ [TX])) T2 n2 -> n2 < ni -> ni < S n ->
    htpd (map (substt x) (T0::GH)) (length GH) (substt x T2)) as htp_subst_narrow0. {
      intros.
      rewrite app_comm_cons in H1.
      remember (T0::GH) as GH1. remember (length (GH ++ [TX])) as xi.
      rewrite app_length in Heqxi. simpl in Heqxi.
      assert (length GH = xi-1) as R. omega.
      rewrite R. eapply htp_subst_narrow02. eauto. omega. eauto. eauto.
  }


  (* main logic *)
  inversion H.
  - Case "bot". subst.
    eapply stpd_bot; eauto. rewrite map_length. simpl.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H1. simpl in H1. eapply H1.
  - Case "top". subst.
    eapply stpd_top; eauto. rewrite map_length. simpl.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H1. simpl in H1. eapply H1.
  - Case "fun". subst.
    eapply stpd_fun. eauto. eauto.
    rewrite map_length.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in *. simpl in *. eauto.
    rewrite map_length.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in *. simpl in *. eauto.
    eapply IHn; eauto. omega.
    erewrite <- subst_open_commute_z. erewrite <- subst_open_commute_z.
    specialize (IHn (T4::GH)). simpl in IHn.
    unfold substt in IHn at 2.  unfold substt in IHn at 3. unfold substt in IHn at 3.
    simpl in IHn. eapply IHn.
    rewrite map_length. rewrite app_length in *. eassumption.
    omega. eauto. eauto. eauto.
  - Case "mem". subst.
    eapply stpd_mem. eapply IHn; eauto. omega. eapply IHn; eauto. omega.


  - Case "selx". subst.
    eexists. eapply stp_selx.
    eapply (proj1 closed_subst_rec).
    rewrite map_length. rewrite app_length in H1. simpl in H1. eapply H1.
    eapply (proj1 closed_upgrade_gh_rec); eauto. omega.

  - Case "ssel1". subst.
    unfold substt at 2. unfold substt at 2. simpl.
    eexists. eapply stp_strong_sel1.
    eapply dm_subst_self in H1; eauto.
    rewrite app_length in H2. simpl in H2. inversion H2; subst.
    rewrite map_length. econstructor.
    eapply (proj2 (proj2 (proj2 (proj2 closed_subst_rec)))). eauto.
    eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
  - Case "ssel2". subst.
    unfold substt at 2. unfold substt at 2. simpl.
    eexists. eapply stp_strong_sel2.
    eapply dm_subst_self in H1; eauto.
    rewrite app_length in H2. simpl in H2. inversion H2; subst.
    rewrite map_length. econstructor.
    eapply (proj2 (proj2 (proj2 (proj2 closed_subst_rec)))). eauto.
    eapply (proj1 closed_upgrade_gh_rec); eauto. omega.

  - Case "sel1". subst. (* invert htp to vtp and create strong_sel node *)
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff. eauto. subst x0.
      assert (exists m0, vtpd m0 x (substt x (TMem l TBot T2))) as A. eapply narrowX. eauto. omega.
      destruct A as [? A]. eu. inversion A. subst.
      repeat eexists. eapply stp_trans. eapply stp_strong_sel1. eauto.
      eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
      eapply stp_upgrade_gh_mult0; eauto.
    + assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      eapply htp_subst_narrow02 in H1.
      eu. repeat eexists. unfold substt. simpl. rewrite E. eapply stp_sel1. eapply H1. eauto. eauto. eauto.

  - Case "sel2". subst. (* invert htp to vtp and create strong_sel node *)
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff. eauto. subst x0.
      assert (exists m0, vtpd m0 x (substt x (TMem l T1 TTop))) as A. eapply narrowX. eauto. omega.
      destruct A as [? A]. eu. inversion A. subst.
      repeat eexists. eapply stp_trans.
      eapply stp_upgrade_gh_mult0; eauto.
      eapply stp_strong_sel2. eauto.
      eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    + assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      eapply htp_subst_narrow02 in H1.
      eu. repeat eexists. unfold substt. simpl. rewrite E. eapply stp_sel2. eapply H1. eauto. eauto. eauto.

  - Case "bind1".
    assert (htpd (map (substt x) (T1'::GH)) (length GH) (substt x T2)).
    eapply htp_subst_narrow0. eauto. eauto. omega.
    eu. repeat eexists. eapply stp_bind1. rewrite map_length. eapply H9.
    simpl. subst T1'. fold subst. eapply subst_open4. eauto.
    fold subst.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H3. simpl in H3. rewrite map_length. eauto. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite map_length. rewrite app_length in H4. simpl in H4. eauto.

  - Case "bindx".
    assert (htpd (map (substt x) (T1'::GH)) (length GH) (substt x T2')).
    eapply htp_subst_narrow0. eauto. eauto. omega.
    eu. repeat eexists. eapply stp_bindx. rewrite map_length. eapply H10.
    subst T1'. fold subst. eapply subst_open4. eauto.
    subst T2'. fold subst. eapply subst_open4. eauto.
    rewrite app_length in H4. simpl in H4. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite map_length. eauto.
    rewrite app_length in H5. simpl in H5. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite map_length. eauto.

  - Case "and11".
    assert (stpd (map (substt x) GH) (substt x T0) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_and11. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H2. rewrite map_length. eauto.
  - Case "and12".
    assert (stpd (map (substt x) GH) (substt x T3) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_and12. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H2. rewrite map_length. eauto.
  - Case "and2".
    assert (stpd (map (substt x) GH) (substt x T1) (substt x T0)). eapply IHn. eauto. eauto. omega. eauto.
    assert (stpd (map (substt x) GH) (substt x T1) (substt x T3)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eu. eexists. eapply stp_and2. eauto. eauto.

  - Case "or21".
    assert (stpd (map (substt x) GH) (substt x T1) (substt x T0)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_or21. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H2. rewrite map_length. eauto.
  - Case "or22".
    assert (stpd (map (substt x) GH) (substt x T1) (substt x T3)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_or22. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H2. rewrite map_length. eauto.
  - Case "or1".
    assert (stpd (map (substt x) GH) (substt x T0) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    assert (stpd (map (substt x) GH) (substt x T3) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eu. eexists. eapply stp_or1. eauto. eauto.

  - Case "trans".
    assert (stpd (map (substt x) GH) (substt x T1) (substt x T3)).
    eapply IHn; eauto. omega.
    assert (stpd (map (substt x) GH) (substt x T3) (substt x T2)).
    eapply IHn; eauto. omega.
    eu. eu. repeat eexists. eapply stp_trans. eauto. eauto.
  - Case "later".
    assert (stpd (map (substt x) GH) (substt x T0) (substt x T3)). {
      eapply IHn. eauto.  omega.
      intros; eauto.
    }
    eu. repeat eexists. constructor; eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.


Lemma stp_subst_narrowX: forall x, vr_closed 0 0 (VObj x) ->
   forall ml, forall nl, forall m GH T2 TX n1 n2,
   vtp m x (substt x TX) n1 ->
   htp (GH++[TX]) 0 T2 n2 -> m < ml -> n2 < nl ->
   (forall (m0 : nat) x (T2 T3 : ty) (n1 n2 : nat),
        vtp m0 x T2 n1 ->
        stp [] T2 T3 n2 -> m0 <= m ->
        vtpdd m0 x T3) ->
   vtpdd m x (substt x T2). (* decrease b/c transitivity *)
Proof.
  intros x Hx.
  intros ml. (* induction ml. intros. omega. *)
  intros nl. induction nl. intros. omega.
  intros.
  inversion H0.
  - Case "var". subst.
    assert (T2 = TX). eapply index_hit0. eauto.
    subst T2.
    repeat eexists. eauto. eauto.
  - Case "bind". subst.
    assert (vtpdd m x (substt x (TBind TX0))) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    destruct A as [? [? [A ?]]]. inversion A. subst.
    repeat eexists. unfold substt. erewrite subst_open_commute0.
    assert (closed 0 0 (TBind (substt x TX0))). eapply vtp_closed. unfold substt in A. simpl in A. eapply A.
    assert ((substt x (TX0)) = TX0) as R. eapply subst_closed_id. eauto.
    unfold substt in R. rewrite R in H8. eapply H8. simpl. eauto. omega.
  - Case "sub". subst.
    destruct GL.

    assert (vtpdd m x (substt x T1)) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    eu.
    assert (stpd [] (substt x T1) (substt x T2)) as B.
    erewrite subst_closed_id. erewrite subst_closed_id. eexists. eassumption.
    eapply stp_closed2 in H5. simpl in H5. eapply H5.
    eapply stp_closed1 in H5. simpl in H5. eapply H5.
    simpl in B. eu.
    assert (vtpdd x0 x (substt x T2)).
    eapply H3. eauto. eauto. eauto.
    eu. repeat eexists. eauto. omega.

    assert (length GL = 0) as LenGL. simpl in *. omega.
    assert (GL = []). destruct GL. reflexivity. simpl in LenGL. inversion LenGL.
    subst GL.
    assert (TX = t). eapply proj2. apply app_inj_tail. eassumption.
    subst t.
    assert (vtpdd m x (substt x T1)) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    eu.
    assert (stpd (map (substt x) []) (substt x T1) (substt x T2)) as B.
    eapply stp_subst_narrow0. eauto. eauto. eauto. {
      intros. eapply IHnl in H. eu. repeat eexists. eauto. eauto. eauto. eauto. omega. eauto.
    }
    simpl in B. eu.
    assert (vtpdd x0 x (substt x T2)).
    eapply H3. eauto. eauto. eauto.
    eu. repeat eexists. eauto. omega.
Qed.

Lemma stp_narrow_aux: forall n,
  (forall GH x T n0,
  htp GH x T n0 -> n0 <= n ->
  forall GH1 GH0 GH' TX1 TX2,
    GH=GH1++[TX2]++GH0 ->
    GH'=GH1++[TX1]++GH0 ->
    stpd GH0 TX1 TX2 ->
    htpd GH' x T) /\
  (forall GH T1 T2 n0,
  stp GH T1 T2 n0 -> n0 <= n ->
  forall GH1 GH0 GH' TX1 TX2,
    GH=GH1++[TX2]++GH0 ->
    GH'=GH1++[TX1]++GH0 ->
    stpd GH0 TX1 TX2 ->
    stpd GH' T1 T2).
Proof.
  intros n.
  induction n.
  - Case "z". split; intros; inversion H0; subst; inversion H; eauto.
  - Case "s n". destruct IHn as [IHn_htp IHn_stp].
    split.
    {
    intros GH x T n0 H NE. inversion H; subst;
    intros GH1 GH0 GH' TX1 TX2 EGH EGH' HX.
    + SCase "var".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (index x ([TX2]++GH0) = Some TX2) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (index x GH = Some TX2) as A2'. {
          rewrite EGH. eapply index_extend_mult. apply A2.
        }
        rewrite A2' in H0. inversion H0. subst.
        destruct HX as [nx HX].
        eexists. eapply htp_sub. eapply htp_var. eapply index_extend_mult.
        simpl. rewrite E. reflexivity.
        eapply stp_closed1 in HX. eapply closed_upgrade_gh.
        eapply HX. apply beq_nat_true in E. subst. omega.
        eapply stp_upgrade_gh. eauto. simpl.
        f_equal. apply beq_nat_true in E. subst. reflexivity.
        simpl. reflexivity.
      * assert (index x GH' = Some T) as A. {
          subst.
          eapply index_same. apply E. eassumption.
        }
        eexists. eapply htp_var. eapply A.
        subst. eauto.
    + SCase "bind".
      edestruct IHn_htp with (GH:=GH) (GH':=GH').
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      eexists. eapply htp_bind; eauto.
    + SCase "sub".
      edestruct IHn_htp as [? Htp].
      eapply H0. omega. eapply EGH. eapply EGH'. assumption.
      case_eq (le_lt_dec (S (length GH0)) (length GL)); intros E' LE'.
      assert (exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ (TX2) :: GH0) as EQGH. {
        eapply exists_GH1L. eassumption. simpl. eassumption.
      }
      destruct EQGH as [GH1L [EQGH1 EQGL]].
      edestruct IHn_stp as [? Hsub].
      eapply H1. omega. simpl. eapply EQGL. simpl. reflexivity. eapply HX.

      eexists. eapply htp_sub. eapply Htp. eapply Hsub.
      subst. rewrite app_length in *. simpl in *. eauto.
      rewrite EGH'. simpl. rewrite EQGH1. rewrite <- app_assoc. reflexivity.
      assert (exists GH0U, TX2::GH0 = GH0U ++ GL) as EQGH. {
        eapply exists_GH0U. eassumption. simpl. omega.
      }
      destruct EQGH as [GH0U EQGH].
      destruct GH0U. simpl in EQGH.
      assert (length (TX2::GH0)=length GL) as Contra. {
        rewrite EQGH. reflexivity.
      }
      simpl in Contra. rewrite <- Contra in H2. subst. omega.
      simpl in EQGH. inversion EQGH.
      eexists. eapply htp_sub. eapply Htp. eassumption. eauto.
      instantiate (1:=GH1 ++ [TX1] ++ GH0U). subst.
      rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
    }

    intros GH T1 T2 n0 H NE. inversion H; subst;
    intros GH1 GH0 GH' TX1 TX2 EGH EGH' HX;
    assert (length GH' = length GH) as EGHLEN by solve [
      subst; repeat rewrite app_length; simpl; reflexivity
    ].
    + SCase "bot". eapply stpd_bot. rewrite EGHLEN; assumption.
    + SCase "top". eapply stpd_top. rewrite EGHLEN; assumption.
    + SCase "fun". eapply stpd_fun.
      reflexivity. reflexivity.
      rewrite EGHLEN; assumption. rewrite EGHLEN; assumption.
      eapply IHn_stp; try eassumption. omega.
      eapply IHn_stp with (GH1:=(T4::GH1)); try eassumption.
      rewrite EGHLEN. eauto. omega.
      subst. simpl. reflexivity. subst. simpl. reflexivity.
    + SCase "mem". eapply stpd_mem.
      eapply IHn_stp; try eassumption. omega.
      eapply IHn_stp; try eassumption. omega.
    + SCase "selx". eexists. eapply stp_selx.
      rewrite EGHLEN; assumption.
    + SCase "ssel1". eexists. eapply stp_strong_sel1; try eassumption.
      rewrite EGHLEN; assumption.
    + SCase "ssel2". eexists. eapply stp_strong_sel2; try eassumption.
      rewrite EGHLEN; assumption.
    + SCase "sel1".
      edestruct IHn_htp as [? Htp]; eauto. omega.
    + SCase "sel2".
      edestruct IHn_htp as [? Htp]; eauto. omega.
    + SCase "bind1".
      edestruct IHn_htp with (GH1:=(open 0 (VarF (length GH)) T0 :: GH1)) as [? Htp].
      eapply H0. omega. rewrite EGH. reflexivity. reflexivity. eapply HX.
      eexists. eapply stp_bind1.
      rewrite EGHLEN. subst. simpl. simpl in Htp. eapply Htp.
      rewrite EGHLEN. subst. simpl. reflexivity.
      rewrite EGHLEN. assumption. rewrite EGHLEN. assumption.
    + SCase "bindx".
      edestruct IHn_htp with (GH1:=(open 0 (VarF (length GH)) T0 :: GH1)) as [? Htp].
      eapply H0. omega. rewrite EGH. reflexivity. reflexivity. eapply HX.
      eexists. eapply stp_bindx.
      rewrite EGHLEN. subst. simpl. simpl in Htp. eapply Htp.
      rewrite EGHLEN. subst. simpl. reflexivity.
      rewrite EGHLEN. subst. simpl. reflexivity.
      rewrite EGHLEN. assumption. rewrite EGHLEN. assumption.
    + SCase "and11".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_and11. eapply IH. rewrite EGHLEN. assumption.
    + SCase "and12".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_and12. eapply IH. rewrite EGHLEN. assumption.
    + SCase "and2".
      edestruct IHn_stp as [? IH1].
      eapply H0. omega. eauto. eauto. eauto.
      edestruct IHn_stp as [? IH2].
      eapply H1. omega. eauto. eauto. eauto.
      eexists. eapply stp_and2. eapply IH1. eapply IH2.
    + SCase "or21".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_or21. eapply IH. rewrite EGHLEN. assumption.
    + SCase "or22".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_or22. eapply IH. rewrite EGHLEN. assumption.
    + SCase "or1".
      edestruct IHn_stp as [? IH1].
      eapply H0. omega. eauto. eauto. eauto.
      edestruct IHn_stp as [? IH2].
      eapply H1. omega. eauto. eauto. eauto.
      eexists. eapply stp_or1. eapply IH1. eapply IH2.
    + SCase "trans".
      edestruct IHn_stp as [? IH1].
      eapply H0. omega. eauto. eauto. eauto.
      edestruct IHn_stp as [? IH2].
      eapply H1. omega. eauto. eauto. eauto.
      eexists. eapply stp_trans. eapply IH1. eapply IH2.
    + SCase "later".
      edestruct IHn_stp as [? IH1]; eauto || omega.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.

Lemma stp_narrow: forall TX1 TX2 GH0 T1 T2 n nx,
  stp ([TX2]++GH0) T1 T2 n ->
  stp GH0 TX1 TX2 nx ->
  stpd ([TX1]++GH0) T1 T2.
Proof.
  intros. eapply stp_narrow_aux. eapply H. reflexivity.
  instantiate(3:=nil). simpl. reflexivity. simpl. reflexivity.
  eauto.
Qed.


(* possible types closure *)
Lemma vtp_widen: forall l, forall n, forall k, forall m1 x T2 T3 n1 n2,
  vtp m1 x T2 n1 ->
  stp [] T2 T3 n2 ->
  m1 < l -> n2 < n -> n1 < k ->
  vtpdd m1 x T3.
Proof.
  intros l. induction l. intros. solve by inversion.
  intros n. induction n. intros. solve by inversion.
  intros k. induction k; intros. solve by inversion.
  inversion H.
  - Case "top". inversion H0; subst; invty.
    + SCase "top". repeat eexists; eauto.
    + SCase "ssel2".
      repeat eexists. eapply vtp_sel. eauto. simpl in *. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H8. omega.
    + SCase "and".
      assert (vtpdd m1 x T1). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T0). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T1). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T0). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T0) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
    + SCase "later".
      solve by inversion.

  - Case "mem". inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eauto. eauto.
    + SCase "mem". invty. subst.
      repeat eexists. eapply vtp_mem. eauto.
      eapply stp_trans. eauto. eauto.
      eapply stp_trans. eauto. eauto.
      eauto. eauto.
    + SCase "ssel2".
      repeat eexists. eapply vtp_sel. eauto. simpl in *. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H11. omega.
    + SCase "and".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T5). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T5). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T5) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
    + SCase "later".
      solve by inversion.
  - Case "fun". inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eauto. eauto.
    + SCase "fun". invty. subst.
      assert (stpd [T8] (open 0 (VarF 0) T5) (open 0 (VarF 0) T4)) as A. {
        eapply stp_narrow. simpl. eassumption. simpl. eassumption.
      }
      eu.
      repeat eexists. eapply vtp_fun. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      eauto. eauto.
      eapply stp_trans. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    + SCase "ssel2".
      repeat eexists. eapply vtp_sel. eauto. simpl in *. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. subst. inversion H11. omega.
    + SCase "and".
      assert (vtpdd m1 x T6). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T7). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T6). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T7). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T7) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
    + SCase "later".
      solve by inversion.

  - Case "bind".
    inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top.
      eapply vtp_closed1. eauto. eauto.
    + SCase "sel2".
      repeat eexists. eapply vtp_sel. eauto. simpl in *. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H9. omega.
    + SCase "bind1".
      invty. subst.
      remember (VarF (length [])) as VZ.
      remember (VObj x) as VX.

      (* left *)
      assert (vtpd m x (open 0 VX T0)) as LHS. eexists. eassumption.
      eu.
      (* right *)
      assert (substt x (open 0 VZ T0) = (open 0 VX T0)) as R. unfold substt. subst. eapply subst_open_commute0. eauto.
      assert (substt x T3 = T3) as R1. eapply subst_closed_id. eauto.

      assert (vtpdd m x (substt x T3)) as BB. {
        eapply stp_subst_narrowX.
        eapply vtp_closed1. eauto.
        rewrite <-R in LHS.
        eauto.
        instantiate (2:=nil). simpl. eapply H10. eauto. eauto.
        { intros. eapply IHl. eauto. eauto. omega. eauto. eauto. }
      }
      rewrite R1 in BB.
      eu. repeat eexists. eauto. omega.
    + SCase "bindx".
      invty. subst.
      remember (VarF (length [])) as VZ.
      remember (VObj x) as VX.

      (* left *)
      assert (vtpd m x (open 0 VX T0)) as LHS. eexists. eassumption.
      eu.
      (* right *)
      assert (substt x (open 0 VZ T0) = (open 0 VX T0)) as R. unfold substt. subst. eapply subst_open_commute0. eauto.

      assert (vtpdd m x (substt x (open 0 VZ T4))) as BB. {
        eapply stp_subst_narrowX.
        eapply vtp_closed1. eauto.
        rewrite <-R in LHS. eapply LHS.
        instantiate (2:=nil). simpl. eapply H10. eauto. eauto.
        { intros. eapply IHl. eauto. eauto. omega. eauto. eauto. }
      }
      unfold substt in BB. subst. erewrite subst_open_commute0 in BB.
      clear R.
      eu. repeat eexists. eapply vtp_bind. eauto. eauto. omega. eauto. (* enough slack to add bind back *)
    + SCase "and".
      assert (vtpdd (S m) x T1). eapply IHn; eauto. omega. eu.
      assert (vtpdd (S m) x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd (S m) x T1). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd (S m) x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd (S m) x T4) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
    + SCase "later".
      solve by inversion.
  - Case "ssel2". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top.
      eapply vtp_closed1. eauto. eauto.
    + SCase "ssel1".
      repeat eexists. eauto. omega.
    + SCase "ssel2".
      rewrite H4 in H10. inversion H10; subst.
      repeat eexists. eauto. omega.
    + SCase "sel1".
      repeat eexists. eapply vtp_sel. eassumption.
      eapply stp_closed2 in H0. simpl in H0. inversion H0; subst. assumption.
      eauto. omega.
    + SCase "selx".
      eapply stp_closed2 in H0. simpl in H0. inversion H0; subst. inversion H11; subst.
      omega.
    + SCase "and".
      assert (vtpdd m1 x T1). eapply IHn with (n1 := S n0); eauto. omega. eu.
      assert (vtpdd m1 x T2). eapply IHn with (n1 := S n0); eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T1). eapply IHn with (n1 := S n0); eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T2). eapply IHn with (n1 := S n0); eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T2) as LHS. eapply IHn with (n1 := S n0); eauto. omega. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "and". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top.
      eapply vtp_closed1. eauto. eauto.
    + SCase "ssel2".
      repeat eexists. eapply vtp_sel. eauto. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H12. omega.
    + SCase "and11". eapply IHn in H4. eu. repeat eexists. eauto. omega. eauto. omega. omega. eauto.
    + SCase "and12". eapply IHn in H5. eu. repeat eexists. eauto. omega. eauto. omega. omega. eauto.
    + SCase "and".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T4) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.

  - Case "or1". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top.
      eapply vtp_closed1. eauto. eauto.
    + SCase "ssel2".
      repeat eexists. eapply vtp_sel. eauto. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H12. omega.
    + SCase "and".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "or...".
      eapply IHn in H4. eu.
      repeat eexists. eapply H4. omega. eauto. omega. omega. eauto.
    + SCase "or...".
      assert (vtpdd m1 x T4) as A. eapply IHn. eapply H. eauto. omega. omega. eauto. eu.
      eapply IHn in A. eu.
      repeat eexists. eauto. omega. eauto. omega. omega. eauto.

  - Case "or2". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top.
      eapply vtp_closed1. eauto. eauto.
    + SCase "ssel2".
      repeat eexists. eapply vtp_sel. eauto. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H12. omega.
    + SCase "and".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "or...".
      eapply IHn in H4. eu.
      repeat eexists. eapply H4. omega. eauto. omega. omega. eauto.
    + SCase "or...".
      assert (vtpdd m1 x T4) as A. eapply IHn. eapply H. eauto. omega. omega. eauto. eu.
      eapply IHn in A. eu.
      repeat eexists. eauto. omega. eauto. omega. omega. eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.



Lemma stp_subst_narrow_z: forall GH0 TX T1 T2 x m n1 n2,
  stp (GH0 ++ [TX]) T1 T2 n2 ->
  vtp m x (substt x TX) n1 ->
  stpd (map (substt x) GH0) (substt x T1) (substt x T2).
Proof.
  intros.
  edestruct stp_subst_narrow0.
  eapply vtp_closed1. eauto.
  eauto. eauto.
  { intros. edestruct stp_subst_narrowX.
    eapply vtp_closed1. eauto.
    eauto. eauto. eauto. eauto.
    { intros. eapply vtp_widen; eauto. }
    ev. repeat eexists. eauto.
  }
  eexists. eassumption.
Qed.



Lemma dms_hastp_inv_aux_rec: forall T0 T00 ds0 ds0' n0',
  closed 0 0 (substt ds0 T0) ->
  dms_closed 0 1 ds0 ->
  ds0' = dms_open 0 (VarF 0) ds0 ->
  T0 = open 0 (VarF 0) T00 ->
  closed 0 1 T00 ->
  dms_has_type [T0] ds0' T0 n0' -> forall n0, forall n1 T' ds ds',
  dms_has_type [T0] ds' T' n1 -> n1 <= n0 ->
  closed 0 0 (substt ds0 T') ->
  dms_closed 0 1 ds ->
  ds' = dms_open 0 (VarF 0) ds -> forall dsa dsa',
  dms_to_list ds0 = dsa ++ dms_to_list ds ->
  dms_to_list ds0' = dsa' ++ dms_to_list ds' ->
  exists m n, vtp m ds0 (substt ds0 T') n.
Proof.
  intros T0 T00 ds0 ds0' n0' HC0 Hds0 Eq0' Eq00 HC00 HD0 n0.
  induction n0. intros. inversion H; subst; omega.
  intros n1 T' ds ds' HD LE.
  intros HC Hds Eq'.
  intros dsa dsa' Eqa Eqa'.
  inversion HD; subst.
  - repeat eexists. eapply vtp_top.
    econstructor. eauto.

  - inversion H0; subst.

  { unfold substt in *.
    destruct ds; simpl in H3; try solve [inversion H3].
    inversion H3; subst.
    destruct d; simpl in H4; try solve [inversion H4].
    inversion H4; subst.
    unfold substt in *. simpl in HC. inversion HC; subst. inversion Hds; subst.
    edestruct IHn0 as [? [? IH]]. eapply H1. omega. eauto. eassumption. reflexivity.
    instantiate (1:=dsa ++ [(dty t g0)]). rewrite <- app_assoc. eauto.
    instantiate (1:=dsa' ++ [(dm_open 0 (VarF 0) (dty t g0))]). rewrite <- app_assoc. eauto.
    simpl.

    assert (closed 0 1 t) as A1. {
      simpl. inversion H10; subst. eassumption.
    }
    assert ((subst (VObj ds0) (open 0 (VarF 0) t))=(open 0 (VObj ds0) t)) as B1. {
      rewrite subst_open_commute0. reflexivity. simpl. eauto.
    }
    assert (stpd [] (open 0 (VObj ds0) t) (open 0 (VObj ds0) t)) as C1. {
      eapply stpd_refl.
      simpl. eapply closed_open. simpl. eauto. econstructor. eauto.
    }
    eu.

    exists x. eexists. eapply vtp_and.
    eapply vtp_mem. rewrite <- length_dms_open.
    instantiate (2:=(subst_ty ds0 t)).
    assert (dty (subst_ty ds0 t) g0 = subst_dm ds0 (dty t g0)) as R1. {
      unfold subst_ty. unfold subst_dm. simpl. reflexivity.
    }
    rewrite R1. eapply index_subst_dms. instantiate (1:=dsa). simpl. eauto.
    unfold subst_ty. rewrite B1. eauto. unfold subst_ty. rewrite B1. eauto.
    econstructor. eauto.
    eapply IH. eauto. omega.
  }

  { unfold substt in *.
    destruct ds; simpl in H3; try solve [inversion H3].
    inversion H3.
    destruct d; simpl in H4; try solve [inversion H4].
    inversion H4; subst.
    unfold substt in *. simpl in HC. inversion HC; subst. inversion Hds; subst.
    edestruct IHn0 as [? [? IH]]. eapply H1. omega. eauto. eassumption. reflexivity.
    instantiate (1:=dsa ++ [(dfun t t0 t1)]). rewrite <- app_assoc. eauto.
    instantiate (1:=dsa' ++ [(dm_open 0 (VarF 0) (dfun t t0 t1))]). rewrite <- app_assoc. eauto.
    simpl.

    assert (closed 0 1 t) as A1. {
      simpl. inversion H13; subst. eassumption.
    }
    assert ((subst (VObj ds0) (open 0 (VarF 0) t))=(open 0 (VObj ds0) t)) as B1. {
      rewrite subst_open_commute0. reflexivity. simpl. eauto.
    }
    assert (stpd [] (open 0 (VObj ds0) t) (open 0 (VObj ds0) t)) as C1. {
      eapply stpd_refl.
      simpl. eapply closed_open. simpl. eauto. econstructor. eauto.
    }
    eu.

    assert (closed 0 2 t0) as A2. {
      simpl. inversion H13; subst. eassumption.
    }
    assert (subst (VObj ds0) (open 1 (VarF 0) t0)=(open 1 (VObj ds0) t0)) as B2. {
      rewrite subst_open_commute0. reflexivity. simpl. eauto.
    }
    assert (stpd [subst (VObj ds0) (open 0 (VarF 0) t)]
                (open 0 (VarF 0) (open 1 (VObj ds0) t0))
                (open 0 (VarF 0) (open 1 (VObj ds0) t0))) as C2. {
      eapply stpd_refl.
      simpl. eapply closed_open. simpl. eapply closed_open. simpl.
      eapply closed_upgrade_gh. eauto. omega.
      econstructor.
      eapply (proj2 (proj2 (proj2 closed_upgrade_rec))).
      eapply (proj2 (proj2 (proj2 closed_upgrade_gh_rec))).
      eauto. omega. omega.
      econstructor. omega.
    }
    eu.

    exists x. eexists. eapply vtp_and.
    eapply vtp_fun. rewrite <- length_dms_open.
    instantiate (1:=(tm_open 1 (VObj ds0) t1)).
    instantiate (1:=(open 1 (VObj ds0) t0)).
    instantiate (1:=(subst_ty ds0 t)).
    assert (dfun (subst_ty ds0 t) (open 1 (VObj ds0) t0) (tm_open 1 (VObj ds0) t1) =
            subst_dm ds0 (dfun t t0 t1)) as R1. {
      unfold subst_dm. simpl. reflexivity.
    }
    rewrite R1. eapply index_subst_dms. instantiate (1:=dsa). simpl. eauto.
    eapply HD0.
    eauto. eauto. eauto.
    rewrite <- length_dms_open.
    instantiate (1:=(tm_open 1 (VarF 0) t1)).
    instantiate (1:=(open 1 (VarF 0) t0)).
    instantiate (1:=(open 0 (VarF 0) t)).
    assert (dfun (open 0 (VarF 0) t) (open 1 (VarF 0) t0) (tm_open 1 (VarF 0) t1) =
            dm_open 0 (VarF 0) (dfun t t0 t1)) as R1'. {
      simpl. reflexivity.
    }
    rewrite R1'. eapply index_dms_open. instantiate (1:=dsa). simpl. eauto.
    eauto. eauto. eauto.
    unfold subst_ty. rewrite B1. eauto.
    eauto. eauto. simpl in *.
    inversion H11; subst. eapply closed_open. simpl. eauto.
    econstructor.
    eapply (proj2 (proj2 (proj2 (proj2 closed_upgrade_rec)))). eauto. omega.
    eapply closed_subst. simpl. eauto. econstructor. eauto.
    inversion H13; subst.
    eapply (proj1 (proj2 (proj2 closed_open_rec))). simpl.
    eapply (proj1 (proj2 (proj2 closed_upgrade_gh_rec))). eauto. omega.
    econstructor. omega.
    rewrite B2. eapply C2.
    econstructor. eauto.
    eapply IH. eauto. omega.
  }
Grab Existential Variables.
apply 0. apply 0.
Qed.

Lemma dms_hastp_inv: forall ds T n1,
  dms_has_type [open 0 (VarF 0) T] (dms_open 0 (VarF 0) ds) (open 0 (VarF 0) T) n1 ->
  closed 0 1 T ->
  dms_closed 0 1 ds ->
  exists m n, vtp m ds (open 0 (VObj ds) T) n.
Proof.
  intros ds T n H HCT HCds.
  assert (open 0 (VObj ds) T=substt ds (open 0 (VarF 0) T)) as A. {
    unfold substt. rewrite subst_open_commute0. reflexivity.
    simpl. eauto.
  }
  rewrite A. eapply dms_hastp_inv_aux_rec; eauto.
  rewrite <- A.
  eapply closed_open; eauto. econstructor. eauto.
  rewrite <- A.
  eapply closed_open; eauto. econstructor. eauto.
  instantiate (1:=[]). rewrite app_nil_l. reflexivity.
  instantiate (1:=[]). rewrite app_nil_l. reflexivity.
Qed.

Lemma hastp_inv: forall x T n1,
  has_type [] (tvar (VObj x)) T n1 ->
  exists m n1, vtp m x T n1.
Proof.
  intros. remember [] as GH. remember (tvar (VObj x)) as t.
  induction H; subst; try inversion Heqt.
  - Case "var". subst. simpl in *. eapply dms_hastp_inv; eauto.
  - Case "pack". subst.
    destruct IHhas_type. eauto. eauto. ev.
    repeat eexists. eapply vtp_bind. eauto. eauto.
  - Case "unpack". subst.
    destruct IHhas_type. eauto. eauto. ev. inversion H0.
    repeat eexists. eauto.
  - Case "sub".
    destruct IHhas_type. eauto. eauto. ev.
    assert (exists m0, vtpdd m0 x T2). eexists. eapply vtp_widen; eauto.
    ev. eu. repeat eexists. eauto.
Qed.

Lemma hastp_subst_aux_z: forall ni, (forall GH TX T x t n1 n2,
  has_type (GH++[TX]) t T n2 -> n2 < ni ->
  has_type [] (tvar (VObj x)) (substt x TX) n1 ->
  exists n3, has_type (map (substt x) GH) (tm_subst (VObj x) t) (substt x T) n3) /\
  (forall GH TX T x l d n1 n2,
  dm_has_type (GH++[TX]) l d T n2 -> n2 < ni ->
  has_type [] (tvar (VObj x)) (substt x TX) n1 ->
  exists n3, dm_has_type (map (substt x) GH) l (dm_subst (VObj x) d) (substt x T) n3) /\
  (forall GH TX T x ds n1 n2,
  dms_has_type (GH++[TX]) ds T n2 -> n2 < ni ->
  has_type [] (tvar (VObj x)) (substt x TX) n1 ->
  exists n3, dms_has_type (map (substt x) GH) (dms_subst (VObj x) ds) (substt x T) n3).
Proof.
  intro ni. induction ni. repeat split; intros; omega. destruct IHni as [IHniT [IHniD IHniDs]].
  repeat split;
  intros; remember (GH++[TX]) as GH0; revert GH HeqGH0; inversion H; intros.
  - Case "vobj".
    assert (vr_closed 0 0 (VObj x)) as HCx. {
      eapply has_type_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
    }
    edestruct IHniDs with (GH:=T'::GH1) as [? IH]. subst. eauto. omega. subst. eauto.
    subst. simpl.
    eexists. eapply T_VObj. eapply IH.
    rewrite app_length. simpl. rewrite map_length. unfold substt.
    assert (substt x (open 0 (VarF (length GH1 + 1)) T0) = open 0 (VarF (length GH1)) (substt x T0)) as A. {
      erewrite subst_open. reflexivity. eauto.
    }
    unfold substt in A. rewrite A. reflexivity.
    rewrite app_length. simpl. rewrite map_length. unfold subst_dms.
    rewrite (proj2 (proj2 (proj2 (proj2 (subst_open_rec 0 x HCx))))).
    reflexivity.
    eapply closed_subst.
    rewrite app_length in *. simpl in *. rewrite map_length. eauto.
    eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    eapply (proj2 (proj2 (proj2 (proj2 closed_subst_rec)))).
    rewrite app_length in *. simpl in *. rewrite map_length. eauto.
    eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    unfold substt.
    assert (subst (VObj x) (open 0 (VObj ds) T0) = open 0 (vr_subst (VObj x) (VObj ds)) (subst (VObj x) T0)) as B. {
      eapply (proj2 (subst_open_distribute 0 0 (VObj x) (VObj ds) HCx)).
      omega.
    }
    rewrite B. simpl. reflexivity.

  - Case "varz". subst. simpl.
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff; eauto. subst x0.
      eapply index_hit0 in H2. subst.
      eapply hastp_upgrade_gh_var_ex. eauto.
    + assert (x0 <> 0). eapply beq_nat_false_iff; eauto.
      eexists. eapply T_VarF.
      eapply index_subst1. eauto. eauto.
      eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec).
      eapply has_type_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
      omega.
      assert (S (x0 - 1) + 1 = S x0) as Eq. {
        unfold id in *. omega.
      }
      rewrite Eq. eauto.

  - Case "pack". subst. simpl.
    assert (vr_closed 0 0 (VObj x)) as HCx. {
      eapply has_type_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
    }
    edestruct IHniT as [? IH]. eauto. omega. eauto.
    assert (substt x (TBind T1) = (TBind (substt x T1))) as A. {
      eauto.
    }
    rewrite A.
    destruct v.
    + case_eq (beq_nat i 0); intros E.
      * assert (i = 0). eapply beq_nat_true_iff; eauto. subst.
        simpl in IH.
        eexists. eapply T_VarPack. eapply IH.
        erewrite subst_open_commute0b. eauto. eapply HCx.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4. simpl in H4.
        eapply H4.
        eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
      * assert (i <> 0). eapply beq_nat_false_iff; eauto.
        simpl in IH. rewrite E in IH.
        eexists. eapply T_VarPack.
        simpl. rewrite E. eapply IH.
        remember (i - 1) as z.
        assert (i = z + 1) as B. {
          unfold id in *. omega.
        }
        rewrite B. unfold substt.
        erewrite subst_open_commute_z. simpl. rewrite <- B. rewrite E.
        rewrite Heqz. reflexivity. eapply HCx.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4.
        simpl in H4. eapply H4.
        eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    + eapply has_type_closed1 in H. inversion H; subst. inversion H7; subst.
      omega.
    + eexists. eapply T_VarPack. eapply IH.
      unfold substt.
      eapply (proj2 (subst_open_distribute 0 0 (VObj x) (VObj d) HCx)).
      omega.
      rewrite map_length. eapply closed_subst0.
      eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
      rewrite app_length in H4. simpl in H4.
      apply H4.

  - Case "unpack". subst. simpl.
    assert (vr_closed 0 0 (VObj x)) as HCx. {
      eapply has_type_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
    }
    edestruct IHniT as [? IH]. eapply H2. omega. eauto.
    assert (substt x (TBind T1) = (TBind (substt x T1))) as A. {
      eauto.
    }
    rewrite A in IH.
    destruct v.
    + case_eq (beq_nat i 0); intros E.
      * assert (i = 0). eapply beq_nat_true_iff; eauto. subst.
        simpl in IH.
        eexists. eapply T_VarUnpack. eapply IH.
        erewrite subst_open_commute0b. simpl. reflexivity. eapply HCx.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4. simpl in H4.
        eapply H4.
        eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
      * assert (i <> 0). eapply beq_nat_false_iff; eauto.
        simpl in IH. rewrite E in IH.
        eexists. eapply T_VarUnpack.
        simpl. rewrite E. eapply IH.
        remember (i - 1) as z.
        assert (i = z + 1) as B. {
          unfold id in *. omega.
        }
        rewrite B. unfold substt.
        erewrite subst_open_commute_z. simpl. rewrite <- B. rewrite E.
        rewrite Heqz. reflexivity. eapply HCx.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4.
        simpl in H4. eapply H4.
        eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    + eapply has_type_closed1 in H. inversion H; subst. inversion H7; subst.
      omega.
    + eexists. eapply T_VarUnpack. eapply IH.
      unfold substt.
      eapply (proj2 (subst_open_distribute 0 0 (VObj x) (VObj d) HCx)).
      omega.
      rewrite map_length. eapply closed_subst0.
      eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
      rewrite app_length in H4. simpl in H4.
      apply H4.

  - Case "app". subst. simpl.
    edestruct IHniT as [? IH1]. eapply H2. omega. eauto.
    edestruct IHniT as [? IH2]. eapply H3. omega. eauto.
    eexists. eapply T_App. eauto. eauto. eapply closed_subst.
    subst. rewrite map_length. rewrite app_length in *. simpl in *. eauto.
    subst. rewrite map_length.
    eapply (proj1 closed_upgrade_gh_rec).
    eapply has_type_closed1 in H1. inversion H1; subst. simpl in *. eauto. omega.
  - Case "appvar". subst. simpl.
    assert (vr_closed 0 0 (VObj x)) as HCx. {
      eapply has_type_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
    }

    edestruct IHniT as [? IH1]. eapply H2. omega. eauto.
    edestruct IHniT as [? IH2]. eapply H3. omega. eauto.
    destruct v2.

    case_eq (beq_nat i 0); intros E.

    eapply beq_nat_true in E. subst.
    erewrite subst_open_commute0b.
    eexists. eapply T_AppVar. eauto. eauto.
    simpl. eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega.
    eauto.
    rewrite map_length. erewrite <- subst_open_commute0b.
    eapply closed_subst. eapply closed_upgrade_gh. eassumption.
    rewrite app_length. simpl. omega.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega. eauto. eauto.

    erewrite subst_open5.
    simpl in *. rewrite E in *.
    eexists. eapply T_AppVar. eauto. eauto.
    eapply has_type_closed1 in IH2. inversion IH2; subst. eassumption.
    eauto.
    erewrite <- subst_open5. eapply closed_subst.
    subst. rewrite map_length. rewrite app_length in *. simpl in *. eassumption.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega. eauto.
    apply []. apply beq_nat_false. apply E.
    eauto.
    apply []. apply beq_nat_false. apply E.

    eapply has_type_closed1 in IH2. inversion IH2; subst. inversion H9; subst. omega.

    eexists. eapply T_AppVar. eauto. eauto.
    eapply has_type_closed1 in IH2. inversion IH2; subst. eassumption.
    unfold substt.
    eapply (proj2 (subst_open_distribute 0 0 (VObj x) (VObj d) HCx)). omega.
    eapply closed_subst. subst. rewrite map_length. rewrite app_length in *. simpl in *.
    eapply closed_upgrade_gh. eassumption. omega.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega.

  - Case "sub". subst.
    edestruct hastp_inv as [? [? HV]]; eauto.
    edestruct stp_subst_narrow_z. eapply H3. eapply HV.
    edestruct IHniT as [? IH]. eapply H2. omega. eauto.
    eexists. eapply T_Sub. eauto. eauto.
  - Case "mem". subst. simpl.
    assert (vr_closed 0 0 (VObj x)) as HCx. {
      eapply has_type_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
    }
    eexists. eapply D_Mem. eauto. eapply closed_subst0. rewrite app_length in H2. rewrite map_length. eauto.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega.
    rewrite app_length in *. simpl in *. rewrite map_length. eassumption.
  - Case "fun". subst. simpl.
    assert (vr_closed 0 0 (VObj x)) as HCx. {
      eapply has_type_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
    }
    edestruct IHniT with (GH:=T11::GH1) as [? HI] . eauto. omega. eauto.
    simpl in HI.
    eexists. eapply D_Fun. eapply HI.
    rewrite map_length. rewrite app_length. simpl.
    erewrite subst_open. unfold substt. reflexivity. eapply HCx.
    rewrite map_length. rewrite app_length. simpl.
    erewrite (proj1 (proj2 (proj2 (subst_open_rec 0 x HCx)))). reflexivity.
    rewrite map_length in *. rewrite app_length in *. simpl in *.
    eapply closed_subst0.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega. eauto.
    rewrite map_length in *. rewrite app_length in *. simpl in *.
    eapply closed_subst0.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega. eauto.
    rewrite map_length in *. rewrite app_length in *. simpl in *.
    eapply (proj1 (proj2 (proj2 closed_subst_rec))). eauto.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega.

  - Case "dnil". subst. simpl.
    eexists. eapply D_Nil.

  - Case "dcons". subst. simpl.
    edestruct IHniDs as [? IHDs]. eapply H4. omega. eauto.
    edestruct IHniD as [? IHD]. eapply H3. omega. eauto.
    eexists. eapply D_Cons.
    + reflexivity.
    + fold subst. rewrite <- length_dms_subst. eapply IHD.
    + fold subst. eapply IHDs.
Grab Existential Variables.
apply 0. apply 0. apply 0.
Qed.

Lemma hastp_subst_z: forall GH TX T x t n1 n2,
  has_type (GH++[TX]) t T n2 ->
  has_type [] (tvar (VObj x)) (substt x TX) n1 ->
  exists n3, has_type (map (substt x) GH) (tm_subst (VObj x) t) (substt x T) n3.
Proof.
  intros. eapply hastp_subst_aux_z with (t:=t). eauto. eauto. eauto.
Qed.

Lemma hastp_subst: forall GH TX T x t n1 n2,
  has_type (GH++[TX]) t T n2 ->
  has_type [] (tvar (VObj x)) TX n1 ->
  exists n3, has_type (map (substt x) GH) (tm_subst (VObj x) t) (substt x T) n3.
Proof.
  intros. eapply hastp_subst_z with (t:=t). eauto.
  erewrite subst_closed_id. eauto. eapply has_type_closed in H0. eauto.
Qed.

Lemma stp_subst_narrow: forall GH0 TX T1 T2 x m n1 n2,
  stp (GH0 ++ [TX]) T1 T2 n2 ->
  vtp m x TX n1 ->
  stpd (map (substt x) GH0) (substt x T1) (substt x T2).
Proof.
  intros. eapply stp_subst_narrow_z. eauto.
  erewrite subst_closed_id. eauto. eapply vtp_closed in H0. eauto.
Qed.

Theorem type_safety : forall t T n1,
  has_type [] t T n1 ->
  (exists x, t = tvar (VObj x)) \/
  (exists t' n2, step t t' /\ has_type [] t' T n2).
Proof.
  intros.
  assert (closed (length ([]:tenv)) 0 T) as CL. eapply has_type_closed. eauto.
  remember [] as GH. remember t as tt. remember T as TT.
  revert T t HeqTT HeqGH Heqtt CL.
  induction H; intros.
  - Case "vobj". eauto.
  - Case "varz". subst GH. inversion H.
  - Case "pack". subst GH.
    eapply has_type_closed_b in H. destruct H. subst.
    left. eexists. reflexivity.
  - Case "unpack". subst GH.
    eapply has_type_closed_b in H. destruct H. subst.
    left. eexists. reflexivity.
  - Case "app". subst.
    assert (closed (length ([]:tenv)) 0 (TFun l T1 T)) as TF. eapply has_type_closed. eauto.
    assert ((exists x, t2 = tvar (VObj x)) \/
                (exists (t' : tm) n2,
                   step t2 t' /\ has_type [] t' T1 n2)) as HX.
    eapply IHhas_type2. eauto. eauto. eauto. inversion TF. eauto.
    assert ((exists x, t1 = tvar (VObj x)) \/
                (exists (t' : tm) n2,
                   step t1 t' /\ has_type [] t' (TFun l T1 T) n2)) as HF.
    eapply IHhas_type1. eauto. eauto. eauto. eauto.
    destruct HF.
    + SCase "fun-val".
      destruct HX.
      * SSCase "arg-val".
        ev. ev. subst.
        assert (exists m n1, vtp m x (TFun l T1 T) n1). { eapply hastp_inv. eauto. }
        assert (exists m n1, vtp m x0 T1 n1). { eapply hastp_inv. eauto. }
        ev. inversion H2. subst.
        assert (vtpdd x1 x0 T2). { eapply vtp_widen. eauto. eauto. eauto. eauto. eauto. }
        eu.
        assert (exists n1, has_type [] (tvar (VObj x)) (open 0 (VObj x) T0) n1) as A. {
          eexists. eapply T_VObj. eauto. simpl. reflexivity. simpl. reflexivity.
          simpl. eauto. simpl. inversion H26; subst. eauto. eauto.
        }
        destruct A as [? A].
        assert (substt x (open 0 (VarF 0) T0) = open 0 (VObj x) T0) as EqTx. {
          unfold substt. rewrite subst_open_commute0. reflexivity.
          simpl. assumption.
        }
        assert (has_typed (map (substt x) [T1x]) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx)) (substt x (open 0 (VarF 1) T2x))) as HIx. {
          eapply hastp_subst_z. eapply H15. rewrite EqTx. eapply A.
        }
        eu. simpl in HIx.
        assert (dm_subst (VObj x) (dfun T1x T2x tx) = dfun T2 T5 t) as EqD. {
          erewrite index_dms_open_eq; eauto.
        }
        simpl in EqD. inversion EqD.
        assert (has_typed (map (substt x0) []) (tm_subst (VObj x0) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx))) (substt x0 (substt x (open 0 (VarF 1) T2x)))) as HIx0. {
          eapply hastp_subst. rewrite app_nil_l. eapply HIx. unfold substt. rewrite H9. eauto.
        }
        eu. simpl in HIx0.
        assert ((substt x (open 0 (VarF 1) T2x))=(open 0 (VarF 0) (substt x T2x))) as EqT2x. {
          change 1 with (0+1). erewrite subst_open. reflexivity. eauto.
        }
        assert (vr_closed 0 0 (VObj x0)) as HC0. {
          eapply vtp_closed1; eauto.
        }
        assert (vr_closed 0 0 (VObj x)) as HC. {
          eapply vtp_closed1; eauto.
        }
        assert ((tm_subst (VObj x0) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx))) =
                (subst_tm x0 t)) as Eqtx0. {
          subst. unfold subst_tm.
          change 1 with (0+1).
          rewrite (proj1 (proj2 (proj2 (subst_open_rec 0 x HC)))).
          rewrite (proj1 (proj2 (proj2 subst_open_commute0_rec))).
          reflexivity.
          simpl.
          eapply (proj1 (proj2 (proj2 closed_subst_rec))).
          simpl. eauto.
          eauto.
        }
        assert (has_typed [] (subst_tm x0 t) (substt x0 (open 0 (VarF 0) T5))) as HI. {
          subst. rewrite <- Eqtx0. unfold substt in EqT2x. rewrite <- EqT2x. eauto.
        }
        eu. simpl in HI.
        edestruct stp_subst_narrow as [? HI2]. rewrite app_nil_l. eapply H25. eauto.
        simpl in HI2.
        assert (substt x0 (open 0 (VarF 0) T) = T) as EqT. {
          erewrite <- closed_no_open. erewrite subst_closed_id. reflexivity.
          eassumption. eassumption.
        }
        rewrite EqT in HI2.
        right. repeat eexists. eapply ST_AppAbs. eauto. eauto.
      * SSCase "arg_step".
        ev. subst.
        right. repeat eexists. eapply ST_App2. eauto. eapply T_App.
        eauto. eauto.
        simpl in *. eassumption.
    + SCase "fun_step".
      ev. subst. right. repeat eexists. eapply ST_App1. eauto. eapply T_App.
      eauto. eauto.
      simpl in *. eassumption.

  - Case "appvar". subst.
    assert (closed (length ([]:tenv)) 0 (TFun l T1 T2)) as TF. eapply has_type_closed. eauto.
    assert ((exists x, tvar v2 = tvar (VObj x)) \/
                (exists (t' : tm) n2,
                   step (tvar v2) t' /\ has_type [] t' T1 n2)) as HX.
    eapply IHhas_type2. eauto. eauto. eauto. inversion TF. eauto.
    assert (exists x2, v2 = (VObj x2)) as HXeq. {
      destruct HX as [[? HX] | Contra]. inversion HX. eexists. reflexivity.
      destruct Contra as [t' [n' [Hstep Htyp]]].
      inversion Hstep.
    }
    clear HX. destruct HXeq as [x2 HXeq]. subst v2.
    assert ((exists x, t1 = tvar (VObj x)) \/
                (exists (t' : tm) n2,
                   step t1 t' /\ has_type [] t' (TFun l T1 T2) n2)) as HF.
    eapply IHhas_type1. eauto. eauto. eauto. eauto.
    destruct HF.
    + SCase "fun-val".
      ev. ev. subst.
      assert (exists m n1, vtp m x (TFun l T1 T2) n1). eapply hastp_inv. eauto.
      assert (exists m n1, vtp m x2 T1 n1). eapply hastp_inv. eauto.
      ev. inversion H2. subst.
      assert (vtpdd x0 x2 T0). { eapply vtp_widen. eauto. eauto. eauto. eauto. eauto. }
      eu.
      assert (exists n1, has_type [] (tvar (VObj x)) (open 0 (VObj x) T) n1) as A. {
        eexists. eapply T_VObj. eauto. simpl. reflexivity. simpl. reflexivity.
        simpl. eauto. simpl. inversion H27; subst. eauto. eauto.
      }
      destruct A as [? A].
      assert (substt x (open 0 (VarF 0) T) = open 0 (VObj x) T) as EqTx. {
        unfold substt. rewrite subst_open_commute0. reflexivity.
        simpl. assumption.
      }
      assert (has_typed (map (substt x) [T1x]) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx)) (substt x (open 0 (VarF 1) T2x))) as HIx. {
        eapply hastp_subst_z. eapply H16. rewrite EqTx. eapply A.
      }
      eu. simpl in HIx.
      assert (dm_subst (VObj x) (dfun T1x T2x tx) = dfun T0 T5 t) as EqD. {
        erewrite index_dms_open_eq; eauto.
      }
      simpl in EqD. inversion EqD.
      assert (has_typed (map (substt x2) []) (tm_subst (VObj x2) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx))) (substt x2 (substt x (open 0 (VarF 1) T2x)))) as HIx0. {
        eapply hastp_subst. rewrite app_nil_l. eapply HIx. unfold substt. rewrite H10. eauto.
      }
      eu. simpl in HIx0.
      assert ((substt x (open 0 (VarF 1) T2x))=(open 0 (VarF 0) (substt x T2x))) as EqT2x. {
        change 1 with (0+1). erewrite subst_open. reflexivity. eauto.
      }
      assert (vr_closed 0 0 (VObj x2)) as HC0. {
        eapply vtp_closed1; eauto.
      }
      assert (vr_closed 0 0 (VObj x)) as HC. {
        eapply vtp_closed1; eauto.
      }
      assert ((tm_subst (VObj x2) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx))) =
              (subst_tm x2 t)) as Eqtx0. {
        subst. unfold subst_tm.
        change 1 with (0+1).
        rewrite (proj1 (proj2 (proj2 (subst_open_rec 0 x HC)))).
        rewrite (proj1 (proj2 (proj2 subst_open_commute0_rec))).
        reflexivity.
        simpl.
        eapply (proj1 (proj2 (proj2 closed_subst_rec))).
        simpl. eauto.
        eauto.
      }
      assert (has_typed [] (subst_tm x2 t) (substt x2 (open 0 (VarF 0) T5))) as HI. {
        subst. rewrite <- Eqtx0. unfold substt in EqT2x. rewrite <- EqT2x. eauto.
      }
      eu. simpl in HI.
      edestruct stp_subst_narrow as [? HI2]. rewrite app_nil_l. eapply H26. eauto.
      simpl in HI2.
      assert (substt x2 (open 0 (VarF 0) T2) = (open 0 (VObj x2) T2)) as EqT. {
        erewrite subst_open_commute0b. erewrite subst_closed_id. reflexivity.
        eassumption. eauto.
      }
      rewrite EqT in HI2.
      right. repeat eexists. eapply ST_AppAbs. eauto. eauto.

    + SCase "fun_step".
      ev. subst. right. repeat eexists. eapply ST_App1. eauto. eapply T_AppVar.
      eauto. eauto. eauto. eauto.
      simpl in *. eassumption.

  - Case "sub". subst.
    assert ((exists x, t0 = tvar (VObj x)) \/
               (exists (t' : tm) n2,
                  step t0 t' /\ has_type [] t' T1 n2)) as HH.
    eapply IHhas_type; eauto. change 0 with (length ([]:tenv)) at 1. eapply stpd_closed1; eauto.
    destruct HH.
    + SCase "val".
      ev. subst. left. eexists. eauto.
    + SCase "step".
      ev. subst.
      right. repeat eexists. eauto. eapply T_Sub. eauto. eauto.
Qed.
