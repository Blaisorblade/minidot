Require Import dsubsup_total_rec_monotone.

Require Import Omega.
Require Import FunctionalExtensionality.

Lemma vtp_unfold':
  vtp = val_type.
Proof.
  repeat (apply functional_extensionality; intro).
  apply vtp_unfold.
Qed.

Ltac inverse H := (inversion H; subst).
Ltac match_case_analysis :=
  repeat
    match goal with
    | H : context f [match ?x with _ => _ end] |- _ =>
      destruct x; try solve [inverse H]
    end.

Ltac match_case_analysis_eauto :=
  repeat
    match goal with
    | H : context f [match ?x with _ => _ end] |- _ =>
      destruct x; try solve [inverse H; eauto]
    end.

Lemma val_type_unfold : forall n env GH T v, vtp env GH T n v =
  match v,T with
    | vabs env1 T0 y, TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall vx j (Hj : j < n),
        vtp env GH T1 j vx ->
        exists v, tevaln (vx::env1) y v /\ vtp env (v::GH) (open (varH (length GH)) T2) j v

    | vty env1 TX, TMem T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2 /\
      forall j (Hj : j < n),
        forall vy,
          (vtp env GH T1 j vy -> vtp env1 GH TX j vy) /\
          (vtp env1 GH TX j vy -> vtp env GH T2 j vy)
    | _, TSel (varF x) =>
      match indexr x env with
        | Some (vty env1 TX) => forall j (Hk : j < n), vtp env1 GH TX j v
        | _ => False
      end
    | _, TSel (varH x) =>
      match indexr x GH with
        | Some (vty env1 TX) => forall j (Hk : j < n), vtp env1 GH TX j v
        | _ => False
      end

    | _, TAnd T1 T2 =>
      vtp env GH T1 n v /\ vtp env GH T2 n v

    | _, TBind T1 =>
      closed 1 (length GH) (length env) T1 /\
      vtp env (v::GH) (open (varH (length GH)) T1) n v

    | _, TTop =>
      True
    | _,_ =>
      False
  end.
Proof.
  intros;
    rewrite vtp_unfold';
    rewrite val_type_unfold';
    reflexivity.
Qed.

(* some quick examples *)

Example ex0 : forall n v, vtp [] [] (TTop) n v.
Proof.
  intros. rewrite val_type_unfold. destruct v; auto.
Qed.

Example ex1: forall G1 GH T n, exists (dd:vset), forall v, val_type G1 GH T n v <-> dd  v.
Proof.
  intros. remember (vtp G1 GH T n) as V.

  simpl.
  exists (fun v => val_type G1 GH T n v). intros.
  split; intros; assumption.
Qed.

Example ex3: forall H T n, vtp [] [] (TMem TBot TTop) n (vty H T).
Proof.
  intros. rewrite val_type_unfold.
  split. constructor.
  split. constructor.
  induction n.
  - intros j Hj. inversion Hj.
  -
    intros. split. intros. rewrite val_type_unfold in H0. destruct vy; inversion H0.
    intros. rewrite val_type_unfold. destruct vy; trivial.
Qed.


(* Safer version of split; for use in automation. *)
Ltac split_conj :=
  repeat match goal with
  | |- _ /\ _ => split
  end.

Lemma val_type_mon: forall G H T n v, vtp G H T n v -> forall m, m < n -> vtp G H T m v.
Proof.
  (* The proof is by induction on type T, because monotonicity on intersection types follows by induction. *)
  (* We proceed by case analysis on values. *)
  induction T; intros;
    rewrite val_type_unfold in *;
      destruct v; ev; repeat split_conj; match_case_analysis.
  (* We could finish the proof by *)
  (* all: intros; try assert (Hjn: j < n) by omega; eauto 2. *)
  (* But let's look how our cases (24 right now!) are solved. *)
  (* Most cases (12) follow trivially, or by using the induction hypothesis. *)
  all: trivial.
  (* A couple (4) follow just by using induction. *)
  all: eauto 2.
  (* The other cases (8) have hypothesis for all j < n and have a conclusion for
     all j < m (with m < n). So we assert that j < n, and then Coq can finish
     the proof automatically. *)
  all: intros; assert (Hjn: j < n) by omega; eauto 2.
Qed.

(* (* This lemma  establishes that val_type indeed defines a value set (vseta). *)
(*    We need this result in the t_typ/TMem case in the main proof, *)
(*    to establish a vseta equivalent to [[ T1 ]] that can be passed *)
(*    to [[ TMem T1 T1 ]]. *)
(*   *) *)
(* Example valtp_to_vseta: forall G1 GH T, exists (dd:vseta),  *)
(*     forall n d v, val_type G1 GH T n d v <-> dd (S n) d v. *)
(* Proof. *)
(*   intros. remember (vtp G1 GH T) as V. *)

(*   simpl. *)
(*   exists (fun n => match n return vset n with *)
(*                      | 0 => fun v => True *)
(*                      | S n0 => (fun d v => val_type G1 GH T n0 d v) *)
(*                    end). *)
(*   intros. *)
(*   split; intros; assumption. *)
(* Qed. *)





(* (* consistent environment *) *)
Definition R_env k venv tenv :=
  length venv = length tenv /\
  forall x TX, indexr x tenv = Some TX ->
    (exists vx,
       indexr x venv = Some vx /\ vtp venv [] TX k vx).


(* automation *)
Hint Unfold venv.
Hint Unfold tenv.

Hint Unfold open.
Hint Unfold indexr.
Hint Unfold length.

(* Hint Unfold R. *)
Hint Unfold R_env.

Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.

Hint Constructors closed.
Hint Constructors has_type.
Hint Constructors stp.

Hint Constructors option.
Hint Constructors list.

Hint Resolve ex_intro.

(* ############################################################ *)
(* Examples *)
(* ############################################################ *)


Ltac crush :=
  try solve [eapply stp_selx; compute; eauto; crush];
  try solve [eapply stp_selax; compute; eauto; crush];
  try solve [econstructor; compute; eauto; crush];
  try solve [eapply t_sub; crush].

(* define polymorphic identity function *)

Definition polyId := TAll (TMem TBot TTop) (TAll (TSel (varB 0)) (TSel (varB 1))).

Example ex10: has_type [] (tabs (TMem TBot TTop) (tabs (TSel (varF 0)) (tvar 1))) polyId.
Proof.
  crush.
Qed.


(* instantiate it to TTop *)
(* Example ex20: has_type [polyId] (tapp (tvar 0) (ttyp TTop)) (TAll TTop TTop). *)
(* Proof. *)
(*   crush. *)
(* Qed. *)


(* ############################################################ *)
(* Proofs *)
(* ############################################################ *)



(* ## Extension, Regularity ## *)

Lemma wf_length : forall k vs ts,
                    R_env k vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
Qed.

(* Lemma wf_length2 : forall vs ts, *)
(*                     R_env vs ts -> *)
(*                     (length gs = length ts). *)
(* Proof. *)
(*   intros. destruct H. destruct H0. auto. *)
(* Qed. *)


Hint Immediate wf_length.

Lemma indexr_max : forall X vs n (T: X),
                       indexr n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs.
  - Case "nil". intros. inversion H.
  - Case "cons".
    intros. inversion H.
    case_eq (beq_nat n (length vs)); intros E2.
    + SSCase "hit".
      eapply beq_nat_true in E2. subst n. compute. eauto.
    + SSCase "miss".
      rewrite E2 in H1.
      assert (n < length vs). eapply IHvs. apply H1.
      compute. eauto.
Qed.

Lemma le_xx : forall a b,
                       a <= b ->
                       exists E, le_lt_dec a b = left E.
Proof. intros.
  case_eq (le_lt_dec a b). intros. eauto.
  intros. omega.
Qed.
Lemma le_yy : forall a b,
                       a > b ->
                       exists E, le_lt_dec a b = right E.
Proof. intros.
  case_eq (le_lt_dec a b). intros. omega.
  intros. eauto.
Qed.

Lemma indexr_extend : forall X vs n x (T: X),
                       indexr n vs = Some T ->
                       indexr n (x::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply indexr_max. eauto.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff. omega.
  unfold indexr. unfold indexr in H. rewrite H. rewrite E. reflexivity.
Qed.

(* splicing -- for stp_extend. *)

Fixpoint splice n (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TAll T1 T2   => TAll (splice n T1) (splice n T2)
    | TSel (varF i) => TSel (varF i)
    | TSel (varB i) => TSel (varB i)
    | TSel (varH i) => if le_lt_dec n i then TSel (varH (i+1)) else TSel (varH i)
    | TMem T1 T2   => TMem (splice n T1) (splice n T2)
    | TBind T      => TBind (splice n T)
    | TAnd T1 T2   => TAnd (splice n T1) (splice n T2)
  end.

Definition spliceat n (V: (venv*ty)) :=
  match V with
    | (G,T) => (G,splice n T)
  end.

Lemma splice_open_permute: forall {X} (G0:list X) T2 n j,
(open_rec j (varH (n + S (length G0))) (splice (length G0) T2)) =
(splice (length G0) (open_rec j (varH (n + length G0)) T2)).
Proof.
  intros X G T. induction T; intros; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2; try rewrite IHT; eauto;
  destruct v; eauto.

  case_eq (le_lt_dec (length G) i); intros E LE; simpl; eauto.
  rewrite LE. eauto.
  rewrite LE. eauto.
  case_eq (beq_nat j i); intros E; simpl; eauto.
  case_eq (le_lt_dec (length G) (n + length G)); intros EL LE.
  rewrite E.
  assert (n + S (length G) = n + length G + 1). omega.
  rewrite H. eauto.
  omega.
  rewrite E. eauto.
Qed.

Lemma indexr_splice_hi: forall G0 G2 x0 v1 T,
    indexr x0 (G2 ++ G0) = Some T ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (splice (length G0)) G2 ++ v1 :: G0) = Some (splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply indexr_max in H. simpl in H. omega.
  - simpl in H.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). {
        eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.
      }
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply indexr_extend. eapply H. eauto.
Qed.

Lemma indexr_spliceat_hi: forall G0 G2 x0 v1 G T,
    indexr x0 (G2 ++ G0) = Some (G, T) ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (spliceat (length G0)) G2 ++ v1 :: G0) =
    Some (G, splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply indexr_max in H. simpl in H. omega.
  - simpl in H. destruct a.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). {
        eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.
      }
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply indexr_extend. eapply H. eauto.
Qed.

Lemma plus_lt_contra: forall a b,
  a + b < b -> False.
Proof.
  intros a b H. induction a.
  - simpl in H. apply lt_irrefl in H. assumption.
  - simpl in H. apply IHa. omega.
Qed.

Lemma indexr_splice_lo0: forall {X} G0 G2 x0 (T:X),
    indexr x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    indexr x0 G0 = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl in H. apply H.
  - simpl in H.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E. subst.
      rewrite app_length in H0. apply plus_lt_contra in H0. inversion H0.
    + rewrite E in H. apply IHG2. apply H. apply H0.
Qed.

Lemma indexr_extend_mult: forall {X} G0 G2 x0 (T:X),
    indexr x0 G0 = Some T ->
    indexr x0 (G2++G0) = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl. assumption.
  - simpl.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E.
      apply indexr_max in H. subst.
      rewrite app_length in H. apply plus_lt_contra in H. inversion H.
    + apply IHG2. assumption.
Qed.

Lemma indexr_splice_lo: forall G0 G2 x0 v1 T f,
    indexr x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    indexr x0 (map (splice f) G2 ++ v1 :: G0) = Some T.
Proof.
  intros.
  assert (indexr x0 G0 = Some T). eapply indexr_splice_lo0; eauto.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.

Lemma indexr_spliceat_lo: forall G0 G2 x0 v1 G T f,
    indexr x0 (G2 ++ G0) = Some (G, T) ->
    x0 < length G0 ->
    indexr x0 (map (spliceat f) G2 ++ v1 :: G0) = Some (G, T).
Proof.
  intros.
  assert (indexr x0 G0 = Some (G, T)). eapply indexr_splice_lo0; eauto.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.

Lemma closed_splice: forall i j k T n,
  closed i j k T ->
  closed i (S j) k (splice n T).
Proof.
  intros. induction H; simpl; eauto.
  case_eq (le_lt_dec n x); intros E LE.
  apply cl_selh. omega.
  apply cl_selh. omega.
Qed.

Lemma map_splice_length_inc: forall G0 G2 v1,
   (length (map (splice (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma map_spliceat_length_inc: forall G0 G2 v1,
   (length (map (spliceat (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma closed_inc_mult: forall i j k T,
  closed i j k T ->
  forall i' j' k',
  i' >= i -> j' >= j -> k' >= k ->
  closed i' j' k' T.
Proof.
  intros i j k T H. induction H; intros; eauto; try solve [constructor; omega].
  - apply cl_all. apply IHclosed1; omega. apply IHclosed2; omega.
  - constructor. apply IHclosed; omega.
Qed.

Lemma closed_inc: forall i j k T,
  closed i j k T ->
  closed i (S j) k T.
Proof.
  intros. apply (closed_inc_mult i j k T H i (S j) k); omega.
Qed.

Lemma closed_splice_idem: forall i j k T n,
                            closed i j k T ->
                            n >= j ->
                            splice n T = T.
Proof.
  intros. induction H; eauto.
  - (* TAll *) simpl.
    rewrite IHclosed1. rewrite IHclosed2.
    reflexivity.
    assumption. assumption.
  - (* TVarH *) simpl.
    case_eq (le_lt_dec n x); intros E LE. omega. reflexivity.
  - (* TMem *) simpl.
    rewrite IHclosed1. rewrite IHclosed2.
    reflexivity.
    assumption. assumption.
  - simpl. rewrite IHclosed. reflexivity. assumption.
  - simpl. rewrite IHclosed1. rewrite IHclosed2. reflexivity. assumption. assumption.
Qed.

Lemma stp_closed : forall G GH T1 T2,
                     stp G GH T1 T2 ->
                     closed 0 (length GH) (length G) T1 /\ closed 0 (length GH) (length G) T2.
Proof.
  intros. induction H;
    try solve [repeat ev; split; try inv_mem; eauto using indexr_max].
Qed.

Lemma stp_closed2 : forall G1 GH T1 T2,
                       stp G1 GH T1 T2 ->
                       closed 0 (length GH) (length G1) T2.
Proof.
  intros. apply (proj2 (stp_closed G1 GH T1 T2 H)).
Qed.

Lemma stp_closed1 : forall G1 GH T1 T2,
                       stp G1 GH T1 T2 ->
                       closed 0 (length GH) (length G1) T1.
Proof.
  intros. apply (proj1 (stp_closed G1 GH T1 T2 H)).
Qed.


Lemma closed_upgrade: forall i j k i' T,
 closed i j k T ->
 i' >= i ->
 closed i' j k T.
Proof.
 intros. apply (closed_inc_mult i j k T H i' j k); omega.
Qed.

Lemma closed_upgrade_free: forall i j k j' T,
 closed i j k T ->
 j' >= j ->
 closed i j' k T.
Proof.
 intros. apply (closed_inc_mult i j k T H i j' k); omega.
Qed.

Lemma closed_upgrade_freef: forall i j k k' T,
 closed i j k T ->
 k' >= k ->
 closed i j k' T.
Proof.
 intros. apply (closed_inc_mult i j k T H i j k'); omega.
Qed.

Lemma closed_open: forall i j k V T, closed (i+1) j k T -> closed i j k (TSel V) ->
  closed i j k (open_rec i V T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.
  eapply closed_upgrade. eauto. eauto.
  - Case "TVarB". simpl.
    case_eq (beq_nat i x); intros E. eauto.
    econstructor. eapply beq_nat_false_iff in E. omega.
  - eapply closed_upgrade. eassumption. omega.
Qed.

Lemma indexr_has: forall X (G: list X) x,
  length G > x ->
  exists v, indexr x G = Some v.
Proof.
  intros. remember (length G) as n.
  generalize dependent x.
  generalize dependent G.
  induction n; intros; try omega.
  destruct G; simpl.
  - simpl in Heqn. inversion Heqn.
  - simpl in Heqn. inversion Heqn. subst.
    case_eq (beq_nat x (length G)); intros E.
    + eexists. reflexivity.
    + apply beq_nat_false in E. apply IHn; eauto.
      omega.
Qed.

Lemma stp_refl_aux: forall n T G GH,
  closed 0 (length GH) (length G) T ->
  tsize_flat T < n ->
  stp G GH T T.
Proof.
  intros n. induction n; intros; try omega.
  inversion H; subst; eauto;
  try solve [omega];
  try solve [simpl in H0; constructor; apply IHn; eauto; try omega];
  try solve [apply indexr_has in H1; destruct H1; eauto].
  - simpl in H0.
    eapply stp_all.
    eapply IHn; eauto; try omega.
    reflexivity.
    assumption.
    assumption.
    apply IHn; eauto.
    simpl. apply closed_open; auto using closed_inc.
    unfold open. rewrite <- open_preserves_size. omega.
  - remember (open (varH (length GH)) T0) as TT.
    assert (stp G (TT :: GH) TT TT). eapply IHn. subst.
    eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
    constructor. simpl. omega. subst. unfold open. erewrite <- open_preserves_size. simpl in H0. omega.
    eapply stp_bindx; try eassumption.
  - simpl in *. assert (stp G GH T1 T1). eapply IHn; try eassumption; try omega.
    assert (stp G GH T2 T2). eapply IHn; try eassumption; try omega.
    eapply stp_and2; try eassumption. econstructor; try eassumption. eapply stp_and12; try eassumption.
Qed.

Lemma stp_refl: forall T G GH,
  closed 0 (length GH) (length G) T ->
  stp G GH T T.
Proof.
  intros. apply stp_refl_aux with (n:=S (tsize_flat T)); eauto.
Qed.


Lemma concat_same_length: forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GU = length GH1 ->
  GU=GH1 /\ GL=GH0.
Proof.
  intros. generalize dependent GH1. induction GU; intros.
  - simpl in H0. induction GH1. rewrite app_nil_l in H. rewrite app_nil_l in H.
    split. reflexivity. apply H.
    simpl in H0. omega.
  - simpl in H0. induction GH1. simpl in H0. omega.
    simpl in H0. inversion H0. simpl in H. inversion H. specialize (IHGU GH1 H4 H2).
    destruct IHGU. subst. split; reflexivity.
Qed.

Lemma concat_same_length': forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GL = length GH0 ->
  GU=GH1 /\ GL=GH0.
Proof.
  intros.
  assert (length (GU ++ GL) = length (GH1 ++ GH0)) as A. {
    rewrite H. reflexivity.
  }
  rewrite app_length in A. rewrite app_length in A.
  rewrite H0 in A. apply Nat.add_cancel_r in A.
  apply concat_same_length; assumption.
Qed.


Lemma indexr_at_index: forall {A} x0 GH0 GH1 (v:A),
  beq_nat x0 (length GH1) = true ->
  indexr x0 (GH0 ++ v :: GH1) = Some v.
Proof.
  intros. apply beq_nat_true in H. subst.
  induction GH0.
  - simpl. rewrite <- beq_nat_refl. reflexivity.
  - simpl.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. rewrite <- plus_Sn_m.
    rewrite false_beq_nat. assumption. omega.
Qed.

Lemma indexr_same: forall {A} x0 (v0:A) GH0 GH1 (v:A) (v':A),
  beq_nat x0 (length GH1) = false ->
  indexr x0 (GH0 ++ v :: GH1) = Some v0 ->
  indexr x0 (GH0 ++ v' :: GH1) = Some v0.
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

Inductive venv_ext : venv -> venv -> Prop :=
| venv_ext_refl : forall G, venv_ext G G
| venv_ext_cons : forall T G1 G2, venv_ext G1 G2 -> venv_ext (T::G1) G2.

Lemma venv_ext__ge_length:
  forall G G',
    venv_ext G' G ->
    length G' >= length G.
Proof.
  intros. induction H; simpl; omega.
Qed.


Lemma indexr_safe_ex: forall n GH G1 TF i,
             R_env n GH G1 ->
             indexr i G1 = Some TF ->
             exists v, indexr i GH = Some v /\ vtp GH [] TF n v.
Proof.
  intros. destruct H. destruct (H1 i TF H0) as [v [E G]].
  exists v. split; eauto.
Qed.


(* ### Substitution for relating static and dynamic semantics ### *)
Lemma indexr_hit2 {X}: forall x (B:X) A G,
  length G = x ->
  B = A ->
  indexr x (B::G) = Some A.
Proof.
  intros.
  unfold indexr.
  assert (beq_nat x (length G) = true). eapply beq_nat_true_iff. eauto.
  rewrite H1. subst. reflexivity.
Qed.

Lemma indexr_miss {X}: forall x (B:X) A G,
  indexr x (B::G) = A ->
  x <> (length G)  ->
  indexr x G = A.
Proof.
  intros.
  unfold indexr in H.
  assert (beq_nat x (length G) = false). eapply beq_nat_false_iff. eauto.
  rewrite H1 in H. eauto.
Qed.

Lemma indexr_hit {X}: forall x (B:X) A G,
  indexr x (B::G) = Some A ->
  x = length G ->
  B = A.
Proof.
  intros.
  unfold indexr in H.
  assert (beq_nat x (length G) = true). eapply beq_nat_true_iff. eauto.
  rewrite H1 in H. inversion H. eauto.
Qed.

Lemma indexr_hit0: forall GH (GX0:venv) (TX0:ty),
      indexr 0 (GH ++ [(GX0, TX0)]) =
      Some (GX0, TX0).
Proof.
  intros GH. induction GH.
  - intros. simpl. eauto.
  - intros. simpl. destruct a. simpl. rewrite app_length. simpl.
    assert (length GH + 1 = S (length GH)). omega. rewrite H.
    eauto.
Qed.

Hint Resolve beq_nat_true_iff.
Hint Resolve beq_nat_false_iff.

Lemma closed_no_open: forall T x i j k,
  closed i j k T ->
  T = open_rec i x T.
Proof.
  intros. induction H; intros; eauto;
  try solve [compute; compute in IHclosed; rewrite <-IHclosed; auto];
  try solve [compute; compute in IHclosed1; compute in IHclosed2;
             rewrite <-IHclosed1; rewrite <-IHclosed2; auto].

  Case "TVarB".
    unfold open_rec. assert (i <> x0). omega.
    apply beq_nat_false_iff in H0.
    rewrite H0. auto.
Qed.

Lemma open_subst_commute: forall T2 V j k x i,
closed i j k (TSel V) ->
(open_rec i (varH x) (subst V T2)) =
(subst V (open_rec i (varH (x+1)) T2)).
Proof.
  intros T2 TX j k. induction T2; intros; eauto; try destruct v; eauto.
  - simpl. rewrite IHT2_1; eauto. rewrite IHT2_2; eauto.
    eapply closed_upgrade. eauto. eauto.
  - simpl.
    case_eq (beq_nat i 0); intros E.
    apply beq_nat_true in E. subst.
    case_eq (beq_nat i0 0); intros E0.
    apply beq_nat_true in E0. subst.
    destruct TX; eauto.
    simpl. destruct i; eauto.
    inversion H; subst. omega.
    simpl. reflexivity.
    case_eq (beq_nat i0 0); intros E0.
    apply beq_nat_true in E0. subst.
    simpl. destruct TX; eauto.
    case_eq (beq_nat i i0); intros E1.
    apply beq_nat_true in E1. subst.
    inversion H; subst. omega.
    reflexivity.
    simpl. reflexivity.
  - simpl.
    case_eq (beq_nat i i0); intros E.
    apply beq_nat_true in E; subst.
    simpl.
    assert (x+1 <> 0) as A by omega.
    eapply beq_nat_false_iff in A.
    rewrite A.
    assert (x = x + 1 - 1) as B. unfold id. omega.
    rewrite <- B. reflexivity.
    simpl. reflexivity.
  - simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eauto. eauto.
  - simpl. rewrite IHT2. reflexivity. eapply closed_upgrade. eassumption. omega.
  - simpl. rewrite IHT2_1. rewrite IHT2_2. reflexivity. assumption. assumption.
Qed.

Lemma closed_no_subst: forall T i k TX,
   closed i 0 k T ->
   subst TX T = T.
Proof.
  intros T. induction T; intros; inversion H; simpl; eauto;
  try solve [rewrite (IHT i k TX); eauto; try omega];
  try solve [rewrite (IHT1 i k TX); eauto; rewrite (IHT2 (S i) k TX); eauto; try omega];
  try solve [rewrite (IHT1 i k TX); eauto; rewrite (IHT2 i k TX); eauto; try omega];
  try omega.
  erewrite IHT. reflexivity. eassumption.
Qed.

Lemma closed_subst: forall i j k V T, closed i (j+1) k T -> closed 0 j k (TSel V) -> closed i j k (subst V T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.

  - Case "TVarH". simpl.
    case_eq (beq_nat x 0); intros E.
    eapply closed_upgrade. eapply closed_upgrade_free.
    eauto. omega. eauto. omega.
    econstructor. assert (x > 0). eapply beq_nat_false_iff in E. omega. omega.
Qed.

Lemma closed_nosubst: forall i j k V T, closed i (j+1) k T -> nosubst T -> closed i j k (subst V T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto; subst;
  try inversion H0; eauto.

  - Case "TVarH". simpl. simpl in H0. unfold id in H0.
    assert (beq_nat x 0 = false) as E. apply beq_nat_false_iff. assumption.
    rewrite E.
    eapply cl_selh. omega.
Qed.

Lemma subst_open_commute_m: forall i j k k' j' V T2, closed (i+1) (j+1) k T2 -> closed 0 j' k' (TSel V) ->
    subst V (open_rec i (varH (j+1)) T2) = open_rec i (varH j) (subst V T2).
Proof.
  intros.
  generalize dependent i. generalize dependent j.
  induction T2; intros; inversion H; simpl; eauto; subst;
  try rewrite IHT2_1;
  try rewrite IHT2_2;
  try rewrite IHT2; eauto.
  - Case "TVarH". simpl. case_eq (beq_nat x 0); intros E.
    eapply closed_no_open. eapply closed_upgrade. eauto. omega.
    eauto.
  - Case "TVarB". simpl. case_eq (beq_nat i x); intros E.
    simpl. case_eq (beq_nat (j+1) 0); intros E2.
    eapply beq_nat_true_iff in E2. omega.
    subst. assert (j+1-1 = j) as A. omega. rewrite A. eauto.
    eauto.
Qed.

Lemma subst_open_commute: forall i j k k' V T2, closed (i+1) (j+1) k T2 -> closed 0 0 k' (TSel V) ->
    subst V (open_rec i (varH (j+1)) T2) = open_rec i (varH j) (subst V T2).
Proof.
  intros. eapply subst_open_commute_m; eauto.
Qed.

Lemma subst_open_zero: forall i i' k TX T2, closed i' 0 k T2 ->
    subst TX (open_rec i (varH 0) T2) = open_rec i TX T2.
Proof.
  intros. generalize dependent i'. generalize dependent i.
  induction T2; intros; inversion H; simpl; eauto;
  try solve [rewrite (IHT2_1 _ i'); eauto;
             rewrite (IHT2_2 _ (S i')); eauto;
             rewrite (IHT2_2 _ (S i')); eauto];
  try solve [rewrite (IHT2_1 _ i'); eauto;
             rewrite (IHT2_2 _ i'); eauto].
  subst.
  case_eq (beq_nat x 0); intros E. omega. omega.
  case_eq (beq_nat i x); intros E. eauto. eauto.
  erewrite IHT2. reflexivity. eassumption.
Qed.

Lemma Forall2_length: forall A B f (G1:list A) (G2:list B),
                        Forall2 f G1 G2 -> length G1 = length G2.
Proof.
  intros. induction H.
  eauto.
  simpl. eauto.
Qed.

Lemma nosubst_intro: forall i k T, closed i 0 k T -> nosubst T.
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H; simpl; eauto.
  omega.
Qed.

Lemma nosubst_open: forall i V T2, nosubst (TSel V) -> nosubst T2 -> nosubst (open_rec i V T2).
Proof.
  intros. generalize dependent i. induction T2; intros;
  try inversion H0; simpl; eauto; destruct v; eauto.
  case_eq (beq_nat i i0); intros E. eauto. eauto.
Qed.






(* ### Value Typing / Logical Relation for Values ### *)

(* NOTE: we need more generic internal lemmas, due to contravariance *)

(* used in valtp_widen *)
Lemma valtp_closed: forall T1 vf GH H1 n,
  vtp H1 GH T1 n  vf ->
  closed 0 (length GH) (length H1) T1.
Proof.
  induction T1; intros; destruct vf;
  rewrite val_type_unfold in H; try eauto; try contradiction.
  - (* fun *) ev; econstructor; assumption.
  - (* sel *) destruct v.
              remember (indexr i H1) as L; try destruct L as [?|]; try contradiction.
              constructor. eapply indexr_max. eauto.
              remember (indexr i GH) as L; try destruct L as [?|]; try contradiction.
              constructor. eapply indexr_max. eauto.
              inversion H.
  - (* sel *) destruct v.
              remember (indexr i H1) as L; try destruct L as [?|]; try contradiction.
              constructor. eapply indexr_max. eauto.
              remember (indexr i GH) as L; try destruct L as [?|]; try contradiction.
              constructor. eapply indexr_max. eauto.
              inversion H.
  - ev. constructor; assumption.
  - ev. constructor; assumption.
  - ev. constructor; assumption.
  - ev. constructor. eapply IHT1_1. eassumption. eapply IHT1_2. eassumption.
  - ev. constructor. eapply IHT1_1. eassumption. eapply IHT1_2. eassumption.
Qed.

 
Lemma valtp_extend_aux: forall n T1 vx vf k H1 G1,
  tsize_flat T1 < n ->
  closed 0 (length G1) (length H1) T1 ->
  (vtp H1 G1 T1 k vf <-> vtp (vx :: H1) G1 T1 k vf).
Proof.
  induction n; intros ? ? ? ? ? ? S C. inversion S.
  destruct T1; split; intros V; rewrite val_type_unfold in V.
  - rewrite val_type_unfold. assumption.
  - rewrite val_type_unfold. assumption.
  - rewrite val_type_unfold. assumption.
  - rewrite val_type_unfold. assumption.
  - destruct vf; try solve [inversion V]. ev.
    rewrite val_type_unfold.
    split. simpl. eapply closed_upgrade_freef. apply H. omega.
    split. simpl. eapply closed_upgrade_freef. apply H0. omega.
    intros.
    assert (vtp (H1) G1 T1_1 j vx0).
    intros. simpl in S. assert (tsize_flat T1_1 < n) by omega.
    eapply IHn with (H1 := H1); simpl; try apply vv; try eassumption; auto.
    apply unvv.
    apply H3.
    (* assert (forall jx: nat, jx < k -> val_type (H1) G1 T1_1 jx vx0). *)
    (* intros. simpl in S. assert (tsize_flat T1_1 < n) by omega. *)
    (* apply unvv. eapply IHn with (H1 := H1); simpl; try apply vv; try eassumption; auto. *)
    (* apply unvv. *)
    (* apply H3. *)
    specialize (H2 _ j Hj H4).
    ev. exists x. split. assumption.
    eapply IHn with (H1 := H1). unfold open. rewrite <-open_preserves_size.
    simpl in S. omega.
    eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
    constructor. simpl. omega.
    assumption.
  - destruct vf; try solve by inversion. ev.
    rewrite val_type_unfold. inversion C. subst.
    split. assumption. split. assumption. intros.
    assert (vtp (vx :: H1) G1 T1_1 j vx0).
    intros. eapply IHn with (H1 := H1). simpl in S. omega. assumption.
    assumption.
    specialize (H2 _ j Hj H4).
    ev. exists x. split. assumption. eapply IHn with (H1 := H1).
    unfold open. rewrite <- open_preserves_size. simpl in S. omega.
    eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
    constructor. simpl. omega.
    eapply H5.

  - rewrite val_type_unfold. destruct vf.
    + destruct v.
    destruct (indexr i H1) eqn : A.
    assert (indexr i (vx :: H1) = Some v). apply indexr_extend. assumption. rewrite H. assumption.
    inversion V. assumption. inversion V.
    + destruct v.
    destruct (indexr i H1) eqn : A.
    assert (indexr i (vx :: H1) = Some v). apply indexr_extend. assumption. rewrite H. assumption.
    inversion V. assumption. inversion V.

  - rewrite val_type_unfold. destruct vf.
    + destruct v. inversion C. subst.
    eapply indexr_has in H4. ev. assert (indexr i (vx:: H1) = Some x). apply indexr_extend.
    assumption. rewrite H0 in V. rewrite H. assumption. assumption. inversion V.
    + destruct v. inversion C. subst.
    eapply indexr_has in H4. ev. assert (indexr i (vx:: H1) = Some x). apply indexr_extend.
    assumption. rewrite H0 in V. rewrite H. assumption. assumption. inversion V.

  - inversion C. subst. rewrite val_type_unfold. destruct vf; try solve by inversion.
    ev.
    repeat split_conj.

    + simpl. eapply closed_upgrade_freef. eassumption. omega.
    + simpl. eapply closed_upgrade_freef. eassumption. omega.
    + intros.
      simpl in S.
      assert (tsize_flat T1_1 + tsize_flat T1_2 < n) by omega.
      specialize (H2 j Hj vy). ev.
      split; intros.
      * apply H2.
        eapply IHn with (H1 := H1); omega || eauto.
      * eapply IHn with (H1 := H1); omega || eauto.

        (* destruct k. auto. intros. specialize (H2 vy). ev. split. *)
        (* intros. apply H2. eapply IHn. simpl in S. omega. assumption. eassumption. *)
        (* intros. specialize (H3 H4). eapply IHn with (H1 := H1). simpl in S. omega. *)
        (* assumption.  assumption. *)

  - inversion C. subst. rewrite val_type_unfold. destruct vf; try solve by inversion.
    ev.
    simpl in S.
    assert (tsize_flat T1_1 + tsize_flat T1_2 < n) by omega.
    repeat split_conj; try assumption; intros.
    
    (* destruct k. repeat split; try assumption. *)
    (* split. assumption. split. assumption. *)
    specialize (H2 j Hj vy). ev.
    split; intros.
    + apply H2.
      eapply IHn with (H1:= H1); omega || assumption.
    +
      eapply IHn with (H1:= H1); omega || auto.

  - inversion C. subst.
    simpl in *.
    assert (tsize_flat T1 < n) by omega.
    rewrite val_type_unfold.
    match_case_analysis; ev; repeat split_conj; simpl.
    + eapply closed_upgrade_freef; eassumption || omega.
    + intros.
      eapply IHn with (H1 := H1); try eassumption || omega.
      * unfold open. rewrite <- open_preserves_size. omega.
      * eapply closed_open. simpl. eapply closed_upgrade_free.
        eassumption.
        all: omega || constructor; simpl; omega.
      * eapply H2; assumption.
    + eapply closed_upgrade_freef. eassumption. omega.

    + intros.
      (* eapply IHn with (H1 := H1). *)
      (* * unfold open. rewrite <- open_preserves_size. omega. *)
      (* * eapply closed_open. simpl. *)
      eapply IHn with (H1 := H1); try eassumption || omega.
      * unfold open. rewrite <- open_preserves_size. omega.
      * eapply closed_open. simpl. eapply closed_upgrade_free.
        eassumption.
        all: omega || constructor; simpl; omega.
      * eapply H2; assumption.
  - inversion C. subst.
    simpl in *.
    assert (tsize_flat T1 < n) by omega.
    rewrite val_type_unfold.
    match_case_analysis; ev; repeat split_conj; simpl.
    + eapply closed_upgrade_freef; eassumption || omega.
    + intros.
      eapply IHn with (H1 := H1); try eassumption || omega.
      * unfold open. rewrite <- open_preserves_size. omega.
      * eapply closed_open. simpl. eapply closed_upgrade_free.
        eassumption.
        all: omega || constructor; simpl; omega.
      * eapply H2; assumption.
    + eapply closed_upgrade_freef. eassumption. omega.

    + intros.
      (* eapply IHn with (H1 := H1). *)
      (* * unfold open. rewrite <- open_preserves_size. omega. *)
      (* * eapply closed_open. simpl. *)
      eapply IHn with (H1 := H1); try eassumption || omega.
      * unfold open. rewrite <- open_preserves_size. omega.
      * eapply closed_open. simpl. eapply closed_upgrade_free.
        eassumption.
        all: omega || constructor; simpl; omega.
      * eapply H2; assumption.
    (* assert (closed 1 (length G1) (length H1) T1 /\ *)
    (*     (exists jj : forall x : nat, vset x, *)
    (*        jj k = df k /\ *)
    (*        (forall n0 : nat, *)
    (*         val_type H1 (jj :: G1) (open (varH (length G1)) T1) n0 (jj n0) vf))). destruct vf; assumption. clear V. ev. *)
    (* assert (closed 1 (length G1) (length (vx :: H1)) T1 /\ *)
    (* (exists jj : forall x0 : nat, vset x0, *)
    (*    jj k = df k /\ *)
    (*    (forall n0 : nat, *)
    (*     val_type (vx :: H1) (jj :: G1) (open (varH (length G1)) T1) n0 *)
    (*       (jj n0) vf))) as Goal. *)
    (* split. simpl. eapply closed_upgrade_freef. eassumption. omega. *)
    (* exists x. split. assumption. intros. specialize (H2 n0). eapply IHn with (H1 := H1). *)
    (* unfold open. rewrite <- open_preserves_size. omega. *)
    (* eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega. *)
    (* constructor. simpl. omega. *)
    (* assumption. *)
    (* destruct vf; apply Goal. *)

  (* - inversion C. subst. rewrite val_type_unfold. *)
  (*   assert (closed 1 (length G1) (length (vx :: H1)) T1 /\ *)
  (*       (exists jj : forall x : nat, vset x, *)
  (*          jj k = df k /\ *)
  (*          (forall n0 : nat, *)
  (*           val_type (vx :: H1) (jj :: G1) (open (varH (length G1)) T1) n0 *)
  (*             (jj n0) vf))). destruct vf; assumption. clear V. ev. *)
  (*   assert (closed 1 (length G1) (length H1) T1 /\ *)
  (*   (exists jj : forall x0 : nat, vset x0, *)
  (*      jj k = df k /\ *)
  (*      (forall n0 : nat, *)
  (*       val_type H1 (jj :: G1) (open (varH (length G1)) T1) n0 (jj n0) vf))) as Goal. *)
  (*   split. assumption. exists x. split. assumption. intros. specialize (H2 n0). *)
  (*   apply unvv. eapply IHn with (H1 := H1). unfold open. rewrite <- open_preserves_size. *)
  (*   simpl in S. omega. eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega. *)
  (*   constructor. simpl. omega. apply vv. eassumption. *)
  (*   destruct vf; apply Goal. *)

  - inversion C. subst. simpl in *. rewrite val_type_unfold.
    destruct vf. ev.
    split. eapply IHn with (H1 := H1); try eassumption; try omega.
    eapply IHn with (H1 := H1); try eassumption; try omega.
    ev.
    split. eapply IHn with (H1 := H1); try eassumption; try omega.
    eapply IHn with (H1 := H1); try eassumption; try omega.
  - inversion C. subst. simpl in *. rewrite val_type_unfold.
    destruct vf. ev.
    split. eapply IHn with (H1 := H1); try eassumption; try omega.
    eapply IHn with (H1 := H1); try eassumption; try omega.
    ev.
    split. eapply IHn with (H1 := H1); try eassumption; try omega.
    eapply IHn with (H1 := H1); try eassumption; try omega.
Qed.
 

(* (* used in wf_env_extend and in main theorem *) *)
Lemma valtp_extend: forall vx vf k G1 H1 T1,
  vtp H1 G1 T1 k  vf ->
  vtp (vx::H1) G1 T1 k vf.
Proof.
  intros. eapply valtp_extend_aux with (H1 := H1) (n := tsize_flat T1 + 1).
  - omega.
  - apply valtp_closed in H. assumption.
  - assumption.
Qed.

(* used in wf_env_extend *)
Lemma valtp_shrink: forall vx vf k G1 H1 T1,
  vtp (vx::H1) G1 T1 k vf ->
  closed 0 (length G1) (length H1) T1 ->
  vtp H1 G1 T1 k vf.
Proof.
  intros. eapply valtp_extend_aux. eauto. simpl. assumption.
  eassumption.
Qed.

Lemma valtp_shrinkM: forall vx vf k H1 GH T1,
  vtp (vx::H1) GH T1 k  vf ->
  closed 0 (length GH) (length H1) T1 ->
  vtp H1 GH T1 k vf.
Proof.
  intros. eapply valtp_extend_aux. eauto. simpl. assumption.
  eassumption.
Qed.

Lemma indexr_hit_high: forall (X:Type) x (jj : X) l1 l2 vf,
  indexr x (l1 ++ l2) = Some vf -> (length l2) <= x ->
  indexr (x + 1) (l1 ++ jj :: l2) = Some vf.
Proof. intros. induction l1. simpl in *. apply indexr_max in H. omega.
  simpl in *. destruct (beq_nat x (length (l1 ++ l2))) eqn : A.
  rewrite beq_nat_true_iff in A. assert (x + 1 = length (l1 ++ l2) + 1).
  omega. rewrite app_length in *. assert(x + 1 = length (l1) + S (length l2)).
  omega. simpl in *. rewrite <- beq_nat_true_iff in H2. rewrite H2. assumption.
  rewrite beq_nat_false_iff in A. assert (x + 1 <> length (l1 ++ l2) + 1).
  omega. rewrite app_length in *. assert(x + 1 <> length (l1) + S (length l2)). omega.
  rewrite <- beq_nat_false_iff in H2. simpl. rewrite H2. apply IHl1. assumption.
Qed.

Lemma indexr_hit_low: forall (X:Type) x (jj : X) l1 l2 vf,
  indexr x (l1 ++ l2) = Some vf -> x < (length l2) ->
  indexr (x) (l1 ++ jj :: l2) = Some vf.
Proof. intros. apply indexr_has in H0. ev. assert (indexr x (l1 ++ l2) = Some x0).
  apply indexr_extend_mult. assumption. rewrite H1 in H. inversion H. subst.
  assert (indexr x (jj :: l2) = Some vf). apply indexr_extend. assumption.
  apply indexr_extend_mult. eassumption.
Qed.

Lemma splice_preserves_size: forall T j,
  tsize_flat T = tsize_flat (splice j T).
Proof.
  intros. induction T; simpl; try rewrite IHT1; try rewrite IHT2; try reflexivity.
  destruct v; simpl; try reflexivity. destruct (le_lt_dec j i); simpl; try reflexivity.
  rewrite IHT. reflexivity.
Qed.

Lemma open_permute : forall T V0 V1 i j a b c d,
  closed 0 a b (TSel V0) -> closed 0 c d (TSel V1) -> i <> j ->
  open_rec i V0 (open_rec j V1 T) = open_rec j V1 (open_rec i V0 T).
Proof. intros. generalize dependent i. generalize dependent j.
  induction T; intros.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. specialize (IHT1 _ _ H1). rewrite IHT1. assert ((S i) <> (S j)) by omega.
  specialize (IHT2 _ _ H2). rewrite IHT2. reflexivity.
  destruct v. simpl. reflexivity. simpl. reflexivity.
  (* varB *)
  destruct (beq_nat i i0) eqn : A. rewrite beq_nat_true_iff in A. subst.
  assert ((open_rec j V1 (TSel (varB i0)) = (TSel (varB i0)))). simpl.
  assert (beq_nat j i0 = false). rewrite beq_nat_false_iff. omega. rewrite H2. reflexivity.
  rewrite H2. simpl. assert (beq_nat i0 i0 = true). erewrite beq_nat_refl. eauto. rewrite H3.
  eapply closed_no_open. eapply closed_upgrade. eauto. omega.
  destruct (beq_nat j i0) eqn : B. rewrite beq_nat_true_iff in B. subst.
  simpl. assert (beq_nat i0 i0 = true). erewrite beq_nat_refl. eauto. rewrite H2.
  assert (beq_nat i i0 = false). rewrite beq_nat_false_iff. omega. rewrite H3.
  assert (TSel (V1) = open_rec i V0 (TSel V1)). eapply closed_no_open. eapply closed_upgrade.
  eapply H0. omega. rewrite <- H4. simpl. rewrite H2. reflexivity.
  assert ((open_rec j V1 (TSel (varB i0))) = TSel (varB i0)). simpl. rewrite B. reflexivity.
  rewrite H2. assert (open_rec i V0 (TSel (varB i0)) = (TSel (varB i0))). simpl.
  rewrite A. reflexivity. rewrite H3. simpl. rewrite B. reflexivity.

  simpl. specialize (IHT1 _ _ H1). rewrite IHT1.
  specialize (IHT2 _ _ H1). rewrite IHT2. reflexivity.
  simpl. rewrite IHT. reflexivity. omega.
  simpl. rewrite IHT1. rewrite IHT2. reflexivity. omega. omega.
Qed.

Lemma closed_open2: forall i j k V T i1, closed i j k T -> closed i j k (TSel V) ->
  closed i j k (open_rec i1 V T).
Proof.
  intros. generalize dependent i. revert i1.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.
  eapply closed_upgrade. eauto. eauto.
  - Case "TVarB". simpl.
    case_eq (beq_nat i1 x); intros E. eauto.
    econstructor. eapply beq_nat_false_iff in E. omega.
  - eapply closed_upgrade. eassumption. omega.
Qed.


Lemma splice_retreat4: forall T i j k m V' V ,
  closed i (j + 1) k (open_rec m V' (splice 0 T)) ->
  (closed i j k (TSel V) -> closed i (j) k (open_rec m V T)).
Proof. induction T; intros; try destruct v; simpl in *.
  constructor.
  constructor.
  inversion H; subst.
  specialize (IHT1 _ _ _ _ _ _ H6 H0). assert (closed (S i) (j) k (TSel V)).
  eapply closed_upgrade. eapply H0. omega.
  specialize (IHT2 _ _ _ _ _ _ H7 H1). constructor. assumption. assumption.
  inversion H. subst. constructor. omega.
  inversion H. subst. constructor. omega.
  destruct (beq_nat m i0) eqn : A. assumption.
    inversion H. subst. constructor. omega.
  inversion H. subst. constructor. eapply IHT1. eassumption. assumption.
  eapply IHT2. eassumption. assumption.
  constructor. inversion H. subst.  eapply IHT; try eassumption. eapply closed_upgrade. eassumption. omega.
  inversion H. subst. constructor.  eapply IHT1; try eassumption.
  eapply IHT2; try eassumption.
Qed.

Lemma splice_retreat5: forall T i j k m V' V ,
  closed i (j + 1) k (TSel V') -> closed i (j) k (open_rec m V T) ->
  closed i (j + 1) k (open_rec m V' (splice 0 T)).
Proof. induction T; intros; try destruct v; simpl in *.
  constructor.
  constructor.
  inversion H0; subst.
  specialize (IHT1 _ _ _ _ _ _ H H6). assert (closed (S i) (j + 1) k (TSel V')).
  eapply closed_upgrade. eapply H. omega.
  specialize (IHT2 _ _ _ _ _ _ H1 H7). constructor. assumption. assumption.
  inversion H0. subst. constructor. omega.
  inversion H0. subst. constructor. omega.
  destruct (beq_nat m i0) eqn : A. assumption.
    inversion H0. subst. constructor. omega.
  inversion H0. subst. constructor. eapply IHT1. eassumption. eassumption.
  eapply IHT2. eassumption. eassumption.
  inversion H0. subst. constructor. eapply IHT; try eassumption. eapply closed_upgrade. eassumption. omega.
  inversion H0. subst. constructor. eapply IHT1; try eassumption. eapply IHT2; try eassumption.

Qed.



Lemma splice_open_permute0: forall x0 T2 n j,
(open_rec j (varH (n + x0 + 1 )) (splice (x0) T2)) =
(splice (x0) (open_rec j (varH (n + x0)) T2)).
Proof.
  intros x0 T. induction T; intros; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2; try rewrite IHT; eauto;
  destruct v; eauto.

  case_eq (le_lt_dec (x0) i); intros E LE; simpl; eauto.
  rewrite LE. eauto.
  rewrite LE. eauto.
  case_eq (beq_nat j i); intros E; simpl; eauto.
  case_eq (le_lt_dec (x0) (n + x0)); intros EL LE.
  rewrite E. eauto. omega.
  rewrite E. eauto.
Qed.

Lemma indexr_extend_end: forall {X : Type} (jj : X) l x,
  indexr (x + 1) (l ++ [jj]) = indexr x l.
Proof. intros. induction l. simpl. assert (beq_nat (x + 1) 0 = false).
  rewrite beq_nat_false_iff. omega. rewrite H. reflexivity.
  simpl. destruct (beq_nat (x) (length (l))) eqn : A.
  rewrite beq_nat_true_iff in A. assert (x + 1 = length (l ++ [jj])). rewrite app_length. simpl. omega.
  rewrite <- beq_nat_true_iff in H. rewrite H. reflexivity.
  rewrite beq_nat_false_iff in A. assert (x +1 <> length (l ++ [jj])). rewrite app_length. simpl. omega.
  rewrite <- beq_nat_false_iff in H. rewrite H. assumption.
Qed.

Lemma indexr_hit01: forall {X : Type} GH (jj : X),
      indexr 0 (GH ++ [jj]) = Some (jj).
Proof.
  intros X GH. induction GH.
  - intros. simpl. eauto.
  - intros. simpl. destruct (length (GH ++ [jj])) eqn : A.
    rewrite app_length in *. simpl in *. omega.
    apply IHGH.
Qed.
  


Lemma valtp_splice_aux: forall n T vf H GH1 GH0 vl k,
tsize_flat T < n -> closed 0 (length (GH1 ++ GH0)) (length H) T ->
(
  vtp H (GH1 ++ GH0) T k vf <->
  vtp H (GH1 ++ vl :: GH0) (splice (length GH0) T) k vf
).
Proof.
  induction n; intros * Sz C. inversion Sz.
  destruct T; split; intros V; simpl in *; rewrite val_type_unfold in V;
    assert (length GH1 + S (length GH0) = S (length (GH1 ++ GH0))) as E;
    try rewrite app_length; try omega.
  - rewrite val_type_unfold. destruct vf; apply V.
  - rewrite val_type_unfold. destruct vf; apply V.
  - rewrite val_type_unfold. destruct vf; apply V.
  - rewrite val_type_unfold. destruct vf; apply V.
  - destruct vf; try solve by inversion.
    ev. simpl. rewrite val_type_unfold.
    repeat split_conj.
    + rewrite app_length. simpl. rewrite E. apply closed_splice. apply H0.
    + rewrite app_length. simpl. rewrite E. apply closed_splice. apply H1.
    + intros.
      assert (tsize_flat T1 + tsize_flat T2 < n) by omega.
      assert (vtp H (GH1 ++ GH0) T1 j vx).
      * intros. eapply IHn; (omega || eassumption).
      * specialize (H2 _ _ Hj H5).
        ev. exists x. split. assumption.
        rewrite app_comm_cons.
        (* rewrite app_comm_cons in H5. *)
        unfold open. rewrite app_length.
        replace (length (vl::GH0)) with (length GH0 + 1) by (simpl; omega).
        rewrite plus_assoc.
        rewrite splice_open_permute0.
        eapply IHn with (GH0 := GH0).
        -- rewrite <- open_preserves_size. omega.
        -- eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
           constructor. simpl. rewrite app_length. omega.
        -- unfold open in *. rewrite app_length in *. assumption.
    
  - destruct vf; try solve by inversion. simpl in V.
    ev. rewrite val_type_unfold. inversion C. subst.
    split. assumption. split. assumption. intros.
    assert (tsize_flat T1 + tsize_flat T2 < n) by omega.
    assert (vtp H (GH1 ++ vl :: GH0) (splice (length GH0) T1) j vx) by
        (eapply IHn with (GH0 := GH0); try (omega || eassumption)).
   specialize (H2 _ _ Hj H5). ev. exists x.
    split_conj; try assumption.
    intros. rewrite app_comm_cons.
    eapply IHn with (GH0 := GH0).
    + unfold open. rewrite <- open_preserves_size. omega.
    + apply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.
    +
      rewrite app_length in H6. simpl in H6.
      replace (S (length GH0)) with (length GH0 + 1) in H6 by (simpl; omega).
      rewrite plus_assoc in H6. unfold open in H6. rewrite splice_open_permute0 in H6.
      rewrite app_length. unfold open. eassumption.
    
  - rewrite val_type_unfold.
    (* simpl in *. match_case_analysis. *)
    destruct vf. simpl in *. destruct v.
    (* + assumption. *)
    + destruct (indexr i H) eqn : B; try solve by inversion.
      match_case_analysis.
      intros.
      Admitted.

(*     + destruct (indexr i (GH1 ++ GH0)) eqn : B; try solve by inversion. *)
(*     destruct (le_lt_dec (length GH0) i) eqn : A. *)
(*     assert (indexr (i + 1) (GH1 ++ vl :: GH0) = Some v). apply indexr_hit_high. assumption. omega. *)
(*     rewrite H0. apply V. assert (indexr (i) (GH1 ++ vl :: GH0) = Some v). apply indexr_hit_low. assumption. omega. *)
(*     rewrite H0. apply V. *)
(*     + inversion V. *)
(*     + simpl in *. destruct v; simpl; try apply V. *)
(*     destruct (indexr i (GH1 ++ GH0)) eqn : B; try solve by inversion. *)
(*     destruct (le_lt_dec (length GH0) i) eqn : A. *)
(*     assert (indexr (i + 1) (GH1 ++ vl :: GH0) = Some v). apply indexr_hit_high. assumption. omega. *)
(*     rewrite H0. apply V. assert (indexr (i) (GH1 ++ vl :: GH0) = Some v). apply indexr_hit_low. assumption. omega. *)
(*     rewrite H0. apply V. *)

(*   - apply vv. rewrite val_type_unfold. destruct vf; simpl in *. destruct v. *)
(*     + assumption. *)
(*     + destruct (le_lt_dec (length GH0) i) eqn : A. inversion C. subst. *)
(*     eapply indexr_has in H4. ev. assert (indexr (i + 1)(GH1 ++ vl:: GH0) = Some x). apply indexr_hit_high; assumption. *)
(*     rewrite H0. rewrite H1 in V. assumption. *)
(*     assert (i < length GH0) as H4 by omega. eapply indexr_has in H4. ev. assert (indexr (i)(GH1 ++ GH0) = Some x). *)
(*     apply indexr_extend_mult. assumption. assert (indexr i (GH1 ++ vl :: GH0) = Some x). apply indexr_hit_low; assumption. *)
(*     rewrite H1. rewrite H2 in V. assumption. *)
(*     + inversion V. *)
(*     + destruct v; try solve by inversion; try assumption. *)
(*     destruct (le_lt_dec (length GH0) i) eqn : A. inversion C. subst. *)
(*     eapply indexr_has in H4. ev. assert (indexr (i + 1)(GH1 ++ vl:: GH0) = Some x). apply indexr_hit_high; assumption. *)
(*     rewrite H0. rewrite H1 in V. assumption. *)
(*     assert (i < length GH0) as H4 by omega. eapply indexr_has in H4. ev. assert (indexr (i)(GH1 ++ GH0) = Some x). *)
(*     apply indexr_extend_mult. assumption. assert (indexr i (GH1 ++ vl :: GH0) = Some x). apply indexr_hit_low; assumption. *)
(*     rewrite H1. rewrite H2 in V. assumption. *)

(*   - inversion C. subst. apply vv. rewrite val_type_unfold. destruct vf; try solve by inversion. *)
(*     simpl in *. ev. *)
(*     split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption. *)
(*     split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption. *)
(*     destruct k. auto. intros. specialize (H2 dy vy). ev. split. intros. apply H2. *)
(*     apply unvv. eapply IHn. simpl in Sz. omega. assumption. apply vv. eassumption. *)
(*     intros. specialize (H3 H4). apply unvv. eapply IHn with (GH0 := GH0). simpl in Sz. omega. *)
(*     assumption. apply vv. assumption. *)

(*   - inversion C. subst. apply vv. rewrite val_type_unfold. destruct vf; try solve by inversion. *)
(*     simpl in *. ev. split. assumption. split. assumption. destruct k. auto. *)
(*     intros. specialize (H2 dy vy). ev. split. intros. *)
(*     apply H2. apply unvv. eapply IHn with (GH0 := GH0). simpl in Sz. omega. *)
(*     assumption. apply vv. assumption. *)
(*     intros. specialize (H3 H4). apply unvv. eapply IHn. simpl in Sz. omega. *)
(*     assumption. apply vv. eassumption. *)

(*   - inversion C. subst. simpl in *. apply vv. rewrite val_type_unfold. *)
(*     assert (closed 1 (length (GH1 ++ GH0)) (length H) T /\ *)
(*         (exists vl0 : forall x : nat, vset x, *)
(*            vl0 k = df k /\ *)
(*            (forall n0 : nat, *)
(*             val_type H (vl0 :: GH1 ++ GH0) *)
(*               (open (varH (length (GH1 ++ GH0))) T) n0 (vl0 n0) vf))). *)
(*               destruct vf; assumption. clear V. ev. *)
(*     assert (closed 1 (length (GH1 ++ vl :: GH0)) (length H) (splice (length GH0) T) /\ *)
(*     (exists vl0 : forall x : nat, vset x, *)
(*        vl0 k = df k /\ *)
(*        (forall n0 : nat, *)
(*         val_type H (vl0 :: GH1 ++ vl :: GH0) *)
(*           (open (varH (length (GH1 ++ vl :: GH0))) (splice (length GH0) T)) *)
(*           n0 (vl0 n0) vf))) as Goal. *)
(*     split. rewrite app_length. simpl. rewrite <- plus_n_Sm. eapply closed_splice. *)
(*     rewrite <- app_length. assumption. *)
(*     exists x. split. assumption. *)
(*     intros. specialize (H2 n0). apply unvv. rewrite app_length. replace (length (vl::GH0)) with (length GH0 + 1). *)
(*     rewrite plus_assoc. unfold open. rewrite splice_open_permute0. rewrite app_comm_cons. eapply IHn with (GH0 := GH0). *)
(*     rewrite <- open_preserves_size. simpl in Sz. omega. *)
(*     eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega. *)
(*     constructor. simpl. rewrite app_length. omega. *)
(*     apply vv. unfold open in *. rewrite app_length in *. assumption. *)
(*     simpl. omega. *)
(*     destruct vf; apply Goal. *)

(*   - inversion C. subst. simpl in *. apply vv. rewrite val_type_unfold. *)
(*     assert (closed 1 (length (GH1 ++ vl :: GH0)) (length H) *)
(*           (splice (length GH0) T) /\ *)
(*         (exists vl0 : forall x : nat, vset x, *)
(*            vl0 k = df k /\ *)
(*            (forall n0 : nat, *)
(*             val_type H (vl0 :: GH1 ++ vl :: GH0) *)
(*               (open (varH (length (GH1 ++ vl :: GH0))) *)
(*                  (splice (length GH0) T)) n0 (vl0 n0) vf))). destruct vf; assumption. clear V. ev. *)
(*     assert (closed 1 (length (GH1 ++ GH0)) (length H) T /\ *)
(*     (exists vl0 : forall x0 : nat, vset x0, *)
(*        vl0 k = df k /\ *)
(*        (forall n0 : nat, *)
(*         val_type H (vl0 :: GH1 ++ GH0) (open (varH (length (GH1 ++ GH0))) T) *)
(*           n0 (vl0 n0) vf))) as Goal. *)
(*     split. assumption. exists x. split. assumption. *)
(*     intros. specialize (H2 n0). apply unvv. rewrite app_comm_cons. eapply IHn with (GH0 := GH0). *)
(*     unfold open. rewrite <- open_preserves_size. simpl in Sz. omega. *)
(*     apply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega. *)
(*     constructor. simpl. omega. *)
(*     rewrite app_length in H2. replace (length (vl :: GH0)) with (length GH0 + 1) in H2. *)
(*     unfold open in H2. rewrite plus_assoc in H2. rewrite splice_open_permute0 in H2. *)
(*     rewrite app_length. unfold open. apply vv. eassumption. *)
(*     simpl. omega. *)
(*     destruct vf; apply Goal. *)

(*   - inversion C. subst. simpl in *. apply vv. rewrite val_type_unfold. destruct vf; ev. *)
(*     split. apply unvv. apply vv in H0. eapply IHn with (GH0 := GH0); try eassumption; try omega. *)
(*     apply unvv. apply vv in H1. eapply IHn with (GH0 := GH0); try eassumption; try omega. *)
(*     split. apply unvv. apply vv in H0. eapply IHn with (GH0 := GH0); try eassumption; try omega. *)
(*     apply unvv. apply vv in H1. eapply IHn with (GH0 := GH0); try eassumption; try omega. *)
(*   - inversion C. subst. simpl in *. apply vv. rewrite val_type_unfold. destruct vf; ev. *)
(*     split. apply unvv. apply vv in H0. eapply IHn with (GH0 := GH0); try eassumption; try omega. *)
(*     apply unvv. apply vv in H1. eapply IHn with (GH0 := GH0); try eassumption; try omega. *)
(*     split. apply unvv. apply vv in H0. eapply IHn with (GH0 := GH0); try eassumption; try omega. *)
(*     apply unvv. apply vv in H1. eapply IHn with (GH0 := GH0); try eassumption; try omega. *)

(* Qed. *)


(* used in valtp_widen *)
Lemma valtp_extendH: forall vf k H1 GH T1 vl,
  vtp H1 GH T1 k vf ->
  vtp H1 (vl::GH) T1 k vf.
Proof.
  intros. assert (vl::GH = ([] ++ vl :: GH)) by reflexivity. rewrite H0.
  assert (splice (length GH) T1 = T1). apply valtp_closed in H. eapply closed_splice_idem. eassumption. omega.
  rewrite <- H2.
  eapply valtp_splice_aux with (GH0 := GH). eauto. simpl. apply valtp_closed in H. eapply closed_upgrade_free. eassumption. omega.
  simpl. assumption.
Qed.

Lemma valtp_shrinkH: forall vf k H1 GH T1 jj,
  vtp H1 (jj::GH) T1 k vf ->
  closed 0 (length GH) (length H1) T1 ->
  vtp H1 GH T1 k vf.
Proof.
  intros.
  assert (vtp H1 ([] ++ GH) T1 k vf <->
  vtp H1 ([] ++ jj :: GH) (splice (length GH) T1) k vf).
  eapply valtp_splice_aux. eauto. simpl. assumption.
  apply H2. simpl. assert (splice (length GH) T1 = T1).
  eapply closed_splice_idem. eassumption. omega.
  rewrite H3. assumption.
Qed.




(* used in invert_abs *)
Lemma vtp_subst1: forall venv jj v k T2,
  vtp venv [jj] (open (varH 0) T2) k v ->
  closed 0 0 (length venv) T2 ->
  vtp venv [] T2 k v.
Proof.
  intros. assert (open (varH 0) T2 = T2). symmetry. unfold open.
  eapply closed_no_open. eapply H0. rewrite H1 in H.
 eapply valtp_shrinkH. simpl. eassumption. assumption.
Qed.

Lemma vtp_subst2_aux: forall n T venv jj v x m GH j k,
  tsize_flat T < n ->
  closed j (length GH) (length venv) T -> k < j ->
  indexr x venv = Some jj ->
  (vtp venv (GH ++ [jj]) (open_rec k (varH 0) (splice 0 T)) m v <->
   vtp venv GH (open_rec k (varF x) T) m v).
Admitted.
(* Proof. *)
(*   induction n; intros ? ? ? ? ? ? ? ? ? ? Sz Cz Bd Id. inversion Sz. *)
(*   destruct T; split; intros V; apply unvv in V; rewrite val_type_unfold in V. *)
(*   - unfold open. simpl in *. apply vv. rewrite val_type_unfold. destruct v; apply V. *)
(*   - unfold open. simpl in *. apply vv. rewrite val_type_unfold. destruct v; apply V. *)
(*   - unfold open. simpl in *. apply vv. rewrite val_type_unfold. destruct v; apply V. *)
(*   - unfold open. simpl in *. apply vv. rewrite val_type_unfold. destruct v; apply V. *)
(*   - inversion Cz. subst.   *)
(*     unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. destruct v; try solve by inversion. *)
(*     ev.  *)
(*     split. {rewrite app_length in *.  simpl in *. eapply splice_retreat4.  *)
(*     eassumption. constructor. eapply indexr_max. eassumption. } *)
(*     split. { rewrite app_length in *. simpl in *. eapply splice_retreat4. *)
(*     eassumption. constructor. eapply indexr_max. eassumption. } *)
    
(*     intros. assert (forall kx : nat, val_type venv0 (GH ++ [jj])  *)
(*       (open_rec k (varH 0) (splice 0 T1)) kx (jj0 kx) vx). *)
(*     intros. specialize (H2 kx). apply unvv. apply vv in H2. eapply IHn; try omega; eassumption. *)
(*     specialize (H1 _ _ H3). *)
(*     ev. exists x0. exists x1. split. assumption. *)
(*     intros. specialize (H6 k0). apply unvv. apply vv in H6. unfold open. erewrite open_permute.  *)
(*     eapply IHn; try rewrite <- open_preserves_size; try omega; try eassumption. *)
(*     eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. *)
(*     constructor. simpl. omega. omega. *)
(*     simpl. erewrite open_permute in H6. rewrite app_length in H6. replace (length[jj]) with (0+1) in H6. *)
(*     rewrite plus_assoc in H6. rewrite splice_open_permute0 in H6. rewrite plus_0_r in H6. assumption. *)
(*     simpl. omega. constructor. eauto. constructor. eauto. omega. constructor. eauto. constructor. eauto. omega. *)
  
(*   - inversion Cz. subst.  *)
(*     unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. destruct v; try solve by inversion. ev. *)
(*     split. { rewrite app_length. simpl. eapply splice_retreat5. constructor. omega. eassumption. } *)
(*     split. { rewrite app_length. simpl. eapply splice_retreat5. constructor. omega. eassumption. } *)
(*     intros. assert (forall kx : nat, val_type venv0 GH (open_rec k (varF x) T1) kx (jj0 kx) vx). *)
(*     intros. specialize (H2 kx). apply unvv. apply vv in H2. eapply IHn; try omega; eassumption. *)
(*     specialize (H1 _ _ H3). *)
(*     ev. exists x0. exists x1. split. assumption. *)
(*     intros. apply unvv. specialize (H6 k0). apply vv in H6. rewrite app_comm_cons. *)
(*     unfold open. erewrite open_permute. rewrite app_length. replace (length [jj]) with (0+1). *)
(*     rewrite plus_assoc. rewrite splice_open_permute0. eapply IHn; try omega; try eassumption. *)
(*     rewrite <- open_preserves_size. omega.  *)
(*     eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. *)
(*     constructor. simpl. omega. omega.  *)
(*     erewrite open_permute. rewrite plus_0_r. assumption. *)
(*     constructor. auto. constructor. auto. omega. simpl. omega. constructor. auto. constructor. auto. omega. *)
    
(*   - unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *.  *)
(*     destruct v; destruct v0; simpl in *; try apply V. *)
(*     + assert (indexr (i + 1) (GH ++ [jj]) = indexr i GH). { *)
(*     apply indexr_extend_end. }    *)
(*     rewrite H in V. apply V. *)
(*     + destruct (beq_nat k i) eqn : A.  *)
(*     simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj).  *)
(*     apply indexr_hit01. *)
(*     rewrite H in V. rewrite Id. apply V. inversion V. *)
(*     + assert (indexr (i + 1) (GH ++ [jj]) = indexr i GH). apply indexr_extend_end. *)
(*     rewrite H in V. apply V. *)
(*     + destruct (beq_nat k i) eqn : A.  *)
(*     simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). apply indexr_hit01. *)
(*     rewrite H in V. rewrite Id. apply V. inversion V. *)

(*   - unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *.  *)
(*     destruct v; destruct v0; simpl in *; try apply V. *)
(*     assert (indexr (i + 1) (GH ++ [jj]) = indexr i GH). apply indexr_extend_end. *)
(*     rewrite H. apply V. *)
(*     destruct (beq_nat k i) eqn : A.  *)
(*     simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). apply indexr_hit01. *)
(*     rewrite H. rewrite Id in V. apply V. inversion V. *)
(*     assert (indexr (i + 1) (GH ++ [jj]) = indexr i GH). apply indexr_extend_end. *)
(*     rewrite H. apply V. *)
(*     destruct (beq_nat k i) eqn : A.  *)
(*     simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). apply indexr_hit01. *)
(*     rewrite H. rewrite Id in V. apply V. inversion V. *)

(*   - inversion Cz. subst.  *)
(*     unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. destruct v; try solve by inversion.     *)
(*     ev. rewrite app_length in *. *)
(*     split. { eapply splice_retreat4. simpl in *. eassumption. constructor. apply indexr_max in Id. omega. }  *)
(*     split. { eapply splice_retreat4. simpl in *. eassumption. constructor. apply indexr_max in Id. omega. }  *)
(*     destruct m. auto. *)
(*     intros. specialize (H1 dy vy). ev. *)
(*     split. intros. apply H1. apply unvv. apply vv in H3. eapply IHn; try omega; eassumption. *)
(*     intros. specialize (H2 H3). apply unvv. apply vv in H2. eapply IHn; try omega; eassumption. *)

(*   - inversion Cz. subst.  *)
(*     unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. *)
(*     destruct v; try solve by inversion. ev. rewrite app_length in *.  *)
(*     split. { eapply splice_retreat5. constructor. omega. eassumption. } *)
(*     split. { eapply splice_retreat5. constructor. omega. eassumption. } *)
(*     destruct m. auto. *)
(*     intros. specialize (H1 dy vy). ev. split.  *)
(*     intros. apply H1. apply unvv. apply vv in H3. eapply IHn; try omega; eassumption. *)
(*     intros. specialize (H2 H3). apply unvv. apply vv in H2. eapply IHn; try omega; eassumption. *)

(*   - inversion Cz. subst. simpl in *. rewrite app_length in *. apply vv. rewrite val_type_unfold. *)
(*     assert (closed 1 (length GH + length [jj]) (length venv0) *)
(*           (open_rec (S k) (varH 0) (splice 0 T)) /\ *)
(*         (exists jj0 : forall x0 : nat, vset x0, *)
(*            jj0 m = d m /\ *)
(*            (forall n0 : nat, *)
(*             val_type venv0 (jj0 :: GH ++ [jj]) *)
(*               (open (varH (length GH + length [jj])) *)
(*                  (open_rec (S k) (varH 0) (splice 0 T))) n0 (jj0 n0) v))). *)
(*                  destruct v; assumption. clear V. ev. *)
(*     assert (closed 1 (length GH) (length venv0) (open_rec (S k) (varF x) T) /\ *)
(*     (exists jj0 : forall x1 : nat, vset x1, *)
(*        jj0 m = d m /\ *)
(*        (forall n0 : nat, *)
(*         val_type venv0 (jj0 :: GH) *)
(*           (open (varH (length GH)) (open_rec (S k) (varF x) T)) n0 (jj0 n0) v))) as Goal. *)
(*     split. eapply splice_retreat4. simpl in H. eassumption.  *)
(*     constructor. eapply indexr_max. eassumption.  *)
(*     exists x0. split. assumption. intros. specialize (H1 n0). *)
(*     apply unvv. apply vv in H1. unfold open. erewrite open_permute.  eapply IHn. *)
(*     rewrite <- open_preserves_size. omega. *)
(*     eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. *)
(*     constructor. simpl. omega. omega. eassumption. *)
(*     unfold open in *. erewrite open_permute in H1. replace (length [jj]) with (0 + 1) in H1. rewrite plus_assoc in H1. *)
(*     rewrite splice_open_permute0 in H1. rewrite plus_0_r in H1. assumption. *)
(*     simpl. omega. constructor. auto. constructor. auto. omega. constructor. auto. constructor. auto. omega. *)
(*     destruct v; apply Goal. *)

(*   - inversion Cz. subst. simpl in *. apply vv. rewrite val_type_unfold. *)
(*     assert (closed 1 (length GH) (length venv0) (open_rec (S k) (varF x) T) /\ *)
(*         (exists jj0 : forall x0 : nat, vset x0, *)
(*            jj0 m = d m /\ *)
(*            (forall n0 : nat, *)
(*             val_type venv0 (jj0 :: GH) *)
(*               (open (varH (length GH)) (open_rec (S k) (varF x) T)) n0 *)
(*               (jj0 n0) v))). destruct v; assumption. clear V. ev. *)
(*     assert (closed 1 (length (GH ++ [jj])) (length venv0) *)
(*       (open_rec (S k) (varH 0) (splice 0 T)) /\ *)
(*     (exists jj0 : forall x1 : nat, vset x1, *)
(*        jj0 m = d m /\ *)
(*        (forall n0 : nat, *)
(*         val_type venv0 (jj0 :: GH ++ [jj]) *)
(*           (open (varH (length (GH ++ [jj]))) *)
(*              (open_rec (S k) (varH 0) (splice 0 T))) n0 (jj0 n0) v))) as Goal. *)
(*     split. rewrite app_length. eapply splice_retreat5. constructor. omega. eassumption. *)
(*     exists x0. split. assumption. intros. specialize (H1 n0). *)
(*     apply unvv. apply vv in H1. unfold open in *. erewrite open_permute.  *)
(*     rewrite app_comm_cons. rewrite app_length. replace (length[jj]) with (0+1).  *)
(*     rewrite plus_assoc. rewrite splice_open_permute0. eapply IHn. *)
(*     rewrite <- open_preserves_size. omega. *)
(*     eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. *)
(*     constructor. simpl. omega. omega. eassumption. erewrite open_permute. rewrite plus_0_r. *)
(*     assumption.  *)
(*     constructor. auto. constructor. auto. omega. simpl. omega. constructor. auto. constructor. auto. omega. *)
(*     destruct v; apply Goal. *)

(*   - inversion Cz. subst. rewrite app_length in *. simpl in *. apply vv. rewrite val_type_unfold. *)
(*     assert (val_type venv0 (GH ++ [jj]) (open_rec k (varH 0) (splice 0 T1)) m (d m) v /\ *)
(*         val_type venv0 (GH ++ [jj]) (open_rec k (varH 0) (splice 0 T2)) m (d m) v). destruct v; assumption. clear V. ev. *)
(*     assert (val_type venv0 GH (open_rec k (varF x) T1) m (d m) v /\ *)
(*     val_type venv0 GH (open_rec k (varF x) T2) m (d m) v) as Goal.  *)
(*     split. apply unvv. apply vv in H. eapply IHn; try eassumption; try omega. *)
(*     apply unvv. apply vv in H0. eapply IHn; try eassumption; try omega. *)
(*     destruct v; apply Goal. *)

(*   - inversion Cz. subst. simpl in *. apply vv. rewrite val_type_unfold. *)
(*     assert (val_type venv0 GH (open_rec k (varF x) T1) m (d m) v /\ *)
(*         val_type venv0 GH (open_rec k (varF x) T2) m (d m) v). destruct v; assumption. clear V. ev. *)
(*     assert (val_type venv0 (GH ++ [jj]) (open_rec k (varH 0) (splice 0 T1)) m (d m) v /\ *)
(*     val_type venv0 (GH ++ [jj]) (open_rec k (varH 0) (splice 0 T2)) m (d m) v) as Goal. *)
(*     split. apply unvv. apply vv in H. eapply IHn; try eassumption; try omega. *)
(*     apply unvv. apply vv in H0. eapply IHn; try eassumption; try omega. *)
(*     destruct v; apply Goal. *)


(* Grab Existential Variables. *)
(* apply 0. apply 0. apply 0. apply 0. *)
(* apply 0. apply 0. apply 0. apply 0. *)
(* apply 0. apply 0. apply 0. apply 0. *)
(* apply 0. apply 0. apply 0. apply 0. *)
(* Qed. *)


Lemma vtp_subst: forall T venv jj v x k GH,
  closed 1 (length GH) (length venv) T ->
  indexr x venv = Some jj ->
  (vtp venv (GH ++ [jj]) (open (varH 0) (splice 0 T)) k v <->
   vtp venv GH (open (varF x) T) k v).
Proof. intros. eapply vtp_subst2_aux. eauto. eassumption. omega. assumption. Qed.


(* used in invert_dabs *)
Lemma vtp_subst2: forall venv jj v x k  T2,
  closed 1 0 (length venv) T2 ->
  vtp venv [jj] (open (varH 0) T2) k v ->
  indexr x venv = Some jj ->
  vtp venv [] (open (varF x) T2) k v.
Proof.
  intros. assert ([jj] = ([] ++ [jj])). reflexivity.
  rewrite H2 in H0. assert (splice 0 T2 = T2). eapply closed_splice_idem.
  eassumption. omega. rewrite <- H3 in H0. eapply vtp_subst in H0. eassumption.
  simpl. assumption. assumption.
Qed.

(* used in valtp_bounds *)
Lemma vtp_subst2_general: forall venv jj v x T2 k,
  closed 1 0 (length venv) T2 ->
  indexr x venv = Some jj ->
  ( vtp venv [jj] (open (varH 0) T2) k v <->
    vtp venv [] (open (varF x) T2) k v).
Proof.
  intros. split.
  Case "->". intros. assert ([jj] = ([] ++ [jj])). simpl. reflexivity.
  rewrite H2 in H1. assert (splice 0 T2 = T2). eapply closed_splice_idem.
  eassumption. omega. rewrite <- H3 in H1. eapply vtp_subst in H1. eassumption.
  simpl. assumption. assumption.
  Case "<-". intros.  assert ([jj] = ([] ++ [jj])). simpl. reflexivity.
  assert (splice 0 T2 = T2). eapply closed_splice_idem. eassumption. omega.
  eapply vtp_subst in H1; try eassumption. rewrite <- H2 in H1. rewrite H3 in H1.
  assumption.
Qed.


(* used in vabs case of main theorem *)
Lemma vtp_subst3: forall venv v' v T2 k,
  closed 1 0 (length venv) T2 ->
  vtp (v'::venv) [] (open (varF (length venv)) T2) k v ->
  vtp venv [v'] (open (varH 0) T2) k v.
Proof.
  intros. assert (splice 0 T2 = T2) as EE. eapply closed_splice_idem. eassumption. omega.
  assert (vtp (v'::venv) ([] ++ [v']) (open (varH 0) (splice 0 T2)) k v).
  assert (indexr (length venv) (v' :: venv) = Some v'). simpl.
    replace (beq_nat (length venv) (length venv) ) with true. reflexivity.
    apply beq_nat_refl.
  eapply vtp_subst. simpl. eapply closed_upgrade_freef. eassumption. omega. eassumption.
  assumption.
  simpl in *. rewrite EE in H1. eapply valtp_shrinkM. eassumption.
  apply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
  constructor. simpl. omega.
Qed.

Lemma open_preserves_size2: forall T x j,
  tsize_flat T = tsize_flat (open_rec j (varF x) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
  - destruct v; simpl; destruct (beq_nat j i); eauto.
Qed.

Lemma valty_subst4: forall G T1 v' v k,
  closed 1 0 (length G) T1 ->
  (vtp G [v'] (open (varH 0) T1) k v <->
   vtp (v' :: G) [] (open (varF (length G)) T1) k v).
Proof.
  intros. split.
  Case "->". intros. assert (vtp (v' :: G) [v'] (open (varH 0) T1) k v).
    { eapply valtp_extend_aux with (H1 := G). eauto.
      simpl. eapply closed_open. simpl. eapply closed_inc_mult. eassumption. omega. omega.
      omega. constructor. omega. assumption. }
    assert (vtp (v' :: G) [] (open (varF (length G)) T1) k v).
    { eapply vtp_subst2_general. simpl. eapply closed_upgrade_freef. eassumption. omega.
      simpl. replace (beq_nat (length G) (length G)) with true. reflexivity. apply beq_nat_refl.
      assumption. } assumption.
  Case "<-". intros. assert (vtp (v' :: G) [v'] (open (varF (length G)) T1) k v).
    { eapply valtp_extendH. assumption. }
    assert (vtp (v' :: G) [v'] (open (varH 0) T1) k v).
    { eapply vtp_subst2_general with (x := length G). simpl. eapply closed_upgrade_freef. eassumption. omega.
      simpl. replace (beq_nat (length G) (length G)) with true. reflexivity. apply beq_nat_refl.
      eassumption. }
    eapply valtp_shrinkM. eassumption. simpl. eapply closed_open. simpl. eapply closed_upgrade_free.
    eassumption. omega. constructor. omega.
Qed.
   



(* ### Relating Value Typing and Subtyping ### *)
Lemma valtp_widen_aux: forall k G1 GH1 T1 T2,
  stp G1 GH1 T1 T2 ->
  forall H GH,
    length G1 = length H ->
    (forall x TX, indexr x G1 = Some TX ->
                   exists vx,
                     vtp H GH TX k vx) ->
    length GH1 = length GH ->
    (forall x TX, indexr x GH1 = Some TX ->
                   exists vx,
                     vtp H GH TX k vx) ->
  (forall vf,
     vtp H GH T1 k vf -> vtp H GH T2 k vf).
Proof.
Admitted.
(*   intros ? ? ? ? stp.  *)
(*   induction stp; intros G GHX LG RG LGHX RGHX kf df vf V0.  *)

  
(*   - Case "Top". *)
(*     eapply vv. rewrite val_type_unfold. destruct vf; reflexivity. *)
(*   - Case "Bot". *)
(*     rewrite val_type_unfold in V0. destruct vf; inversion V0. *)
(*   - Case "mem". *)
(*     subst.  *)
(*     rewrite val_type_unfold in V0.  *)
(*     eapply vv. rewrite val_type_unfold. *)
(*     destruct vf; destruct kf; try destruct b; try solve by inversion; ev.   *)
(*     + rewrite <-LG. rewrite <-LGHX. split. *)
(*       apply stp_closed1 in stp2. assumption. split. apply stp_closed2 in stp1. assumption. *)
(*       trivial. *)
(*     + rewrite <-LG. rewrite <-LGHX. split. *)
(*       apply stp_closed1 in stp2. assumption. split. apply stp_closed2 in stp1. assumption. *)
(*       intros. specialize (H1 dy vy). ev. split. *)
(*       intros. eapply H1. eapply unvv. eapply IHstp2; assumption. *)
(*       intros. eapply unvv. eapply IHstp1; try assumption. eapply H2. assumption. *)
   
(*   - Case "Sel1". *)
(*     subst. specialize (IHstp _ _ LG RG LGHX RGHX). *)
(*     rewrite val_type_unfold in V0. *)
(*     specialize (RG _ _ H). *)
(*     ev. rewrite H1 in V0. *)
(*     assert (x1 (S kf) (df kf) vf). destruct vf; eauto. clear V0. *)

(*     eapply unvv in H2. *)
(*     specialize (IHstp (S kf) x1 x0 H2). *)
(*     eapply unvv in IHstp. *)
(*     rewrite val_type_unfold in IHstp. *)
(*     destruct x0. inversion IHstp. ev. *)
(*     specialize (H6 df vf). ev. *)
(*     eapply vv. eapply H7. eapply H3.  *)

(*   - Case "Sel2". *)
(*     subst. specialize (IHstp _ _ LG RG LGHX RGHX). *)
(*     specialize (RG _ _ H). *)
(*     ev. specialize (H2 (S kf)). eapply unvv in H2.  *)
(*     specialize (IHstp _ _ _ H2). *)
(*     eapply unvv in IHstp. *)
(*     rewrite val_type_unfold in IHstp. *)
(*     destruct x0. inversion IHstp. ev. *)
(*     specialize (H5 df vf). ev. *)
    
(*     eapply vv. rewrite val_type_unfold. rewrite H1. *)
(*     assert (x1 (S kf) (df kf) vf). eapply H5. eapply V0. *)
(*     destruct vf; assumption. *)
    
(*   - Case "selx". *)
(*     eapply vv. eapply V0. *)

(*   (* exactly the same as sel1/sel2, modulo RG/RGHX *) *)
(*  - Case "Sela1". *)
(*     subst. specialize (IHstp _ _ LG RG LGHX RGHX). *)
(*     rewrite val_type_unfold in V0. *)
(*     specialize (RGHX _ _ H). *)
(*     ev. rewrite H1 in V0. *)
(*     assert (x1 (S kf) (df kf) vf). destruct vf; eauto. clear V0. *)

(*     eapply unvv in H2. *)
(*     specialize (IHstp (S kf) x1 x0 H2). *)
(*     eapply unvv in IHstp. *)
(*     rewrite val_type_unfold in IHstp. *)
(*     destruct x0. inversion IHstp. ev. *)
(*     specialize (H6 df vf). ev. *)
(*     eapply vv. eapply H7. eapply H3.  *)

(*   - Case "Sela2". *)
(*     subst. specialize (IHstp _ _ LG RG LGHX RGHX). *)
(*     specialize (RGHX _ _ H). *)
(*     ev. specialize (H2 (S kf)). eapply unvv in H2.  *)
(*     specialize (IHstp _ _ _ H2). *)
(*     eapply unvv in IHstp. *)
(*     rewrite val_type_unfold in IHstp. *)
(*     destruct x0. inversion IHstp. ev. *)
(*     specialize (H5 df vf). ev. *)
    
(*     eapply vv. rewrite val_type_unfold. rewrite H1. *)
(*     assert (x1 (S kf) (df kf) vf). eapply H5. eapply V0. *)
(*     destruct vf; assumption. *)
    
(*   - Case "selax". *)
(*     eapply vv. eapply V0. *)

(*   - Case "bindx". *)
(*     eapply vv. rewrite val_type_unfold. rewrite val_type_unfold in V0. *)
(*     assert (closed 1 (length GHX) (length G) T1 /\ *)
(*            (exists jj : vseta, *)
(*               jj kf = df kf /\ *)
(*               (forall n : nat, *)
(*                val_type G (jj :: GHX) (open (varH (length GHX)) T1) n  *)
(*                         (jj n) vf))). { destruct vf; assumption. } *)
(*     clear V0. *)
(*     assert (closed 1 (length GHX) (length G) T2 /\ *)
(*            (exists jj : vseta, *)
(*               jj kf = df kf /\ *)
(*               (forall n : nat, *)
(*                val_type G (jj :: GHX) (open (varH (length GHX)) T2) n  *)
(*                         (jj n) vf))). { *)
(*       ev. split. rewrite <-LG. rewrite <-LGHX. assumption. *)
(*       exists x. split. assumption. *)
(*       intros. eapply unvv. subst T2'. *)
(*       rewrite <-LGHX.  *)
(*       eapply IHstp. eapply LG.  *)

(*       (* extend RG *) *)
(*       intros ? ? IX. destruct (RG _ _ IX) as [vx0 [jj0 [IX1 FA]]]. *)
(*       exists vx0. exists jj0. split. assumption.  *)
(*       intros. eapply valtp_extendH. eapply unvv. eapply FA. simpl. rewrite LGHX. reflexivity. *)

(*       (* extend RGHX *) *)
(*       intros ? ? IX. *)
(*       { case_eq (beq_nat x0 (length GHX)); intros E. *)
(*         + simpl in IX. rewrite LGHX in IX. rewrite E in IX. inversion IX. subst TX. *)
(*           exists vf. exists x. split. simpl. rewrite E. reflexivity. *)
(*           intros. subst T1'. rewrite LGHX. eapply vv. eapply H5.  *)
(*         + assert (indexr x0 GH = Some TX) as IX0. *)
(*           simpl in IX. rewrite LGHX in IX. rewrite E in IX. inversion IX. reflexivity. *)
(*           specialize (RGHX _ _ IX0). ev. *)
(*           exists x1. exists x2. split. simpl. rewrite E. assumption. *)
(*           intros. eapply valtp_extendH. eapply unvv. eapply H6.  *)
(*       } *)
(*       subst T1'. rewrite LGHX. eapply H5.  *)
(*     }                                       *)
(*     destruct vf; assumption. *)

(*   - Case "And11". *)
(*     rewrite val_type_unfold in V0. *)
(*     destruct vf; ev; eapply IHstp; assumption.  *)
    
(*   - Case "And12". *)
(*     rewrite val_type_unfold in V0. *)
(*     destruct vf; ev; eapply IHstp; assumption.  *)
    
(*   - Case "And2". *)
(*     eapply vv. rewrite val_type_unfold. *)
(*     destruct vf. *)
(*     split; eapply unvv. eapply IHstp1; assumption. eapply IHstp2; assumption. *)
(*     split; eapply unvv. eapply IHstp1; assumption. eapply IHstp2; assumption.  *)
    
(*   - Case "Fun". *)
(*     subst.  *)
(*     rewrite val_type_unfold in V0. *)
(*     assert (val_type G GHX (TAll T3 T4) kf (df kf) vf). rewrite val_type_unfold. *)
(*     subst. destruct vf; try solve [inversion V0]. *)
(*     destruct V0 as [? [? LR]]. *)
(*     assert (closed 0 (length GHX) (length G) T3). rewrite <-LG. rewrite <-LGHX. eapply stp_closed in stp1. eapply stp1. *)
(*     assert (closed 1 (length GHX) (length G) T4). rewrite <-LG. rewrite <-LGHX. eapply H1. *)
(*     split. eauto. split. eauto.  *)
(*     intros jj vx VX0.  *)

(*     specialize (IHstp1 _ _ LG RG LGHX RGHX). *)
    
(*     assert (forall kx, val_type G GHX T1 kx (jj kx) vx) as VX1. { *)
(*       intros. specialize (IHstp1 kx jj vx). eapply unvv. eapply IHstp1. eapply VX0. } *)

(*     destruct (LR jj vx VX1) as [jj2 [v [TE VT]]]. *)

(*     exists jj2. exists v. split. eapply TE. intros. eapply unvv. *)

(*     (* now deal with function result! *) *)
(*     rewrite <-LGHX. rewrite <-LGHX in VT. *)

(*     (* broaden goal so that we can apply stp2 *) *)
(*     eapply IHstp2. eapply LG. *)

(*     (* extend RG *) *)
(*     intros ? ? IX. destruct (RG _ _ IX) as [vx0 [jj0 [IX1 FA]]]. *)
(*     exists vx0. exists jj0. split. assumption.  *)
(*     intros. eapply valtp_extendH. eapply unvv. eapply FA. simpl. rewrite LGHX. reflexivity. *)

(*     (* extend RGHX *) *)
(*     intros ? ? IX. *)
(*     { case_eq (beq_nat x (length GHX)); intros E. *)
(*       + simpl in IX. rewrite LGHX in IX. rewrite E in IX. inversion IX. subst TX. *)
(*         exists vx. exists jj. split. simpl. rewrite E. reflexivity. *)
(*         intros. eapply valtp_extendH. eapply VX0.  *)
(*       + assert (indexr x GH = Some TX) as IX0. *)
(*         simpl in IX. rewrite LGHX in IX. rewrite E in IX. inversion IX. reflexivity. *)
(*         specialize (RGHX _ _ IX0). ev. *)
(*         exists x0. exists x1. split. simpl. rewrite E. assumption. *)
(*         intros. eapply valtp_extendH. eapply unvv. eapply H6.  *)
(*     } *)
(*     eapply VT. eapply vv. eapply H. *)

(*   - Case "trans". *)
(*     specialize (IHstp1 _ _ LG RG LGHX RGHX kf df vf). *)
(*     specialize (IHstp2 _ _ LG RG LGHX RGHX kf df vf). *)
(*     eapply IHstp2. eapply unvv. eapply IHstp1. eapply V0. *)
(* Qed. *)

 
Lemma valtp_widen: forall k vf GH G1 T1 T2,
  vtp GH [] T1 k vf ->
  stp G1 [] T1 T2 ->
  R_env k GH G1 ->
  vtp GH [] T2 k vf.
Proof.
  intros * H H0 H1. destruct H1 as [L1 A]. symmetry in L1.
  eapply valtp_widen_aux; try eassumption; try reflexivity.

  - intros. specialize (A _ _ H1). ev.
    eauto.
  - intros. inversion H1.
Qed.


Lemma wf_env_extend: forall k vx G1 R1 T1,
  R_env k R1 G1 ->
  vtp (vx::R1) [] T1 k vx ->
  R_env k (vx::R1) (T1::G1).
Proof.
  intros * H H0. unfold R_env in *. destruct H as [L1 U].
  split. simpl. rewrite L1. reflexivity.
  (* split. simpl. rewrite L2. reflexivity. *)
  intros. simpl in H. case_eq (beq_nat x (length G1)); intros E; rewrite E in H.
  - inversion H. subst T1. exists vx.
    split. simpl. rewrite <-L1 in E. rewrite E. reflexivity.
    intros. auto.
  - destruct (U x TX H) as [vy0 [EV IR]].
    exists vy0.
    split. simpl. rewrite <-L1 in E. rewrite E. assumption.
    intros. eapply valtp_extend. eapply IR.
Qed.

Lemma wf_env_extend0: forall k vx G1 R1 T1,
  R_env k R1 G1 ->
  vtp R1 [] T1 k vx ->
  R_env k (vx::R1) (T1::G1).
Proof.
  (* intros. *)
  (* eapply wf_env_extend. assumption. *)
  (* eapply valtp_extend. assumption. *)
  eauto using valtp_extend, wf_env_extend.
Qed.



(* (* ### Main Theorem ### *) *)


(* (* type assignment for variables *) *)

Lemma invert_var : forall k x tenv T,
  has_type tenv (tvar x) T -> forall venv, R_env k venv tenv ->
  exists v, tevaln venv (tvar x) v /\ indexr x venv = Some v /\ vtp venv [] T k v.
Proof.
  intros * W. remember (tvar x) as e.
  induction W; intros * WFE; inversion Heqe; try subst x0.

  - Case "Var".
    destruct (indexr_safe_ex k venv env T1 x) as [v [I V]]; try assumption.
      (* as [d [v [I [D V]]]]. eauto. eauto. *)
    
    exists v.
    split_conj; try assumption.
    + exists 0. intros. destruct n. * omega.
                                    * simpl. rewrite I. eauto.

  - Case "VarPack".
    unfold R_env in WFE. ev. destruct (H3 _ _ H) as [v [I ?]]. ev.
    exists v. split. exists 0. intros. destruct n. omega. simpl. rewrite I. reflexivity.
    intros.
    assert (vtp venv [v] (open (varH 0) T1) k v). {
      intros. eapply vtp_subst2_general.
      rewrite H2. assumption. eassumption. eapply H4. }
    split. assumption. rewrite val_type_unfold. simpl. rewrite H2.
    destruct v; split; try assumption; intros; eauto using val_type_mon.


  - Case "And".
    destruct (IHW1 eq_refl venv WFE) as [v1 [E1 [I1 HVF]]].
    destruct (IHW2 eq_refl venv WFE) as [v2 [E2 [I2 HVX]]].
    rewrite I1 in I2. inversion I2. subst v2.
    exists v1.
    split_conj; try assumption.
    intros. rewrite val_type_unfold. destruct v1; (split; [apply HVF|apply HVX]).

  - Case "Sub".
    specialize (IHW Heqe venv WFE). ev. exists x0.
    split. subst e. eassumption.
    split_conj; try assumption.
    intros. eapply valtp_widen. eapply H3. eapply H. eapply WFE.
Qed.

Lemma tevaln_det: forall venv e v1 v2,
    tevaln venv e v1 -> tevaln venv e v2 -> v1 = v2.
Proof.
  unfold tevaln. intros * H1 H2.
  ev.
  assert (exists x1, x1 > x /\ x1 > x0).
  - exists (1 + max x x0).
    unfold gt, lt. simpl.
    split.
    + pose (Max.le_max_l x x0). omega.
    + pose (Max.le_max_r x x0). omega.
  - ev.
    repeat match goal with
           | H : forall n : nat, _ |- _ => specialize (H x1)
           end.
    intuition congruence.
Qed.

Ltac tevaln_det :=
  match goal with
  | H1 : tevaln ?venv ?e ?v1, H2 : tevaln ?venv ?e ?v2 |- _ =>
    assert (v1 = v2) by (eauto using tevaln_det); subst v1
  end.

(* XXX Still needed? *)
Lemma quant_swap: forall venv e T,
    (exists v, tevaln venv e v /\ forall k, vtp venv [] T k v) <->
    (forall k, exists v, tevaln venv e v /\ vtp venv [] T k v).
Proof.
  intros.
  split; split_conj; intros.
  - ev. eexists. split_conj; eauto.
  - destruct (H 0) as [? [? _]].
    eexists. split_conj; eauto.
    intro k. specialize (H k).
    ev.
    tevaln_det.
    assumption.
Qed.

(* (* main theorem *) *)
Theorem full_total_safety : forall k e tenv T,
  has_type tenv e T -> forall venv, R_env k venv tenv ->
  exists v, tevaln venv e v /\ vtp venv [] T k v.
Proof.
  intros * W.
  generalize k. clear k.
  induction W; intros * WFE.

  - Case "Var".
    destruct (invert_var k x env T1 (t_var x env T1 H H0) venv WFE)
      as [v [E [I V]]].
    exists v. split. apply E. apply V.
  - Case "VarPack".
    destruct (invert_var k x G1 (TBind T1) (t_var_pack _ x T1 T1' H H0 H1) venv WFE) as [v [E [I V]]].
    exists v. split. apply E. apply V.

  - Case "Unpack".
    rewrite <-(wf_length _ _ _ WFE) in H.
    destruct (IHW1 k venv WFE) as [vx [IW1 HVX]].

    (* assert (R_env (vx::venv) (T1'::env)) as WFE1. *)
    (* eapply wf_env_extend. assumption. rewrite H. assumption. *)

    (* specialize (IHW2 _ _ WFE1). *)
    (* destruct IHW2 as [vy [IW2 HVY]]. *)
    (* clear HVX. clear VXF. *)

    rewrite val_type_unfold in HVX.
    simpl in HVX.
    assert (forall j, j < k -> vtp venv [vx] (open (varH 0) T1) j vx) as E by (
      match_case_analysis; ev; assumption).

    (* assert (exists jj : vseta, *)
    (*           (forall n : nat, *)
    (*              vtp [jj] (open (varH 0) T1) n (jj n) vx)) as E. *)
    (* destruct vx; ev; exists x0; assumption. *)
    (* destruct E as [jj VXH]. *)
    assert (forall j, j < k -> vtp (vx::venv) [] (open (varF (length venv)) T1) j vx) as VXF. {
      assert (closed 1 0 (S (length venv)) T1).
      {
        match_case_analysis; ev; eapply closed_upgrade_freef; try eassumption; auto.
      }
      intros. eapply vtp_subst2. assumption. eapply valtp_extend. eapply E. assumption.
      eapply indexr_hit2; reflexivity. }
    
    assert (forall j, j < k -> R_env j (vx::venv) (T1'::env)) as WFE1. {
      intros. eapply wf_env_extend. shelve (* R_env is monotonic *). rewrite H. eauto using val_type_mon.
    }


    (* specialize (IHW2 _ _ _ WFE1). *)
    assert (IHW2' : forall j, j < k -> exists v, tevaln (vx :: venv) y v /\ vtp (vx :: venv) [] T2 j v)
      by eauto.
    (* { *)
    (*   intros. *)
    (*   apply IHW2. eapply WFE1. assumption. *)
    (* } *)
    destruct IHW2' as [vy [IW2 HVY]].
    clear HVX. clear VXF.

    exists vy. split. {
      destruct IW1 as [nx IWX].
      destruct IW2 as [ny IWY].
      exists (S (nx+ny)). intros. destruct n. omega. simpl.
      rewrite IWX. rewrite IWY. eauto.
      omega. omega.
    }
    intros. eapply valtp_shrink.
    eapply HVY. rewrite (wf_length2 _ _ _ WFE). assumption.

  - Case "And".
    destruct (invert_var x env (TAnd T1 T2) (t_and env x T1 T2 W1 W2) venv WFE) as [v [E [I V]]].
    exists v. split. apply E. apply V.

  - Case "Typ".

    shelve.
    (* specialize valtp_to_vseta. intros S. specialize (S [] T1). ev. *)
    
    (* exists x. eexists. split. exists 1. intros. destruct n. inversion H1. simpl. reflexivity. *)
    (* rewrite <-(wf_length2 venv renv) in H. *)
    (* intros. rewrite val_type_unfold. simpl. repeat split; try eapply H. *)
    (* destruct k. trivial. intros. destruct (H0 k (dy k) vy). split; assumption. *)
    (* eapply WFE. *)

    
  - Case "App".
    rewrite <-(wf_length _ _ WFE) in H.
    destruct (IHW1 venv WFE) as [vf [IW1 HVF]].
    destruct (IHW2 venv WFE) as [vx [IW2 HVX]].

    (* Must copy HVF for later use? *)
    specialize (HVF 1).
    rewrite val_type_unfold in HVF.
    destruct vf; try solve [inversion HVF].
    
    destruct HVF as [C1 [C2 IHF]].
    ev. destruct (IHF vx 0) as [vy [IW3 HVY]]. omega. apply HVX.
    exists vy. split. {
      (* pick large enough n. nf+nx+ny will do. *)
      destruct IW1 as [nf IWF].
      destruct IW2 as [nx IWX].
      destruct IW3 as [ny IWY].
      exists (S (nf+nx+ny)). intros. destruct n. omega. simpl.
      rewrite IWF. rewrite IWX. rewrite IWY. eauto.
      omega. omega. omega.
    }
    intros. eapply vtp_subst1. simpl in HVY. eapply HVY. eapply H.

  - Case "DApp".
    rewrite <-(wf_length2 _ _ _ WFE) in H0.
    destruct (IHW1 venv WFE) as [df [vf [IW1 HVF]]].
    destruct (invert_var x env T1 W2 venv WFE) as [dx [vx [IW2 [I [D HVX]]]]].

    specialize (HVF 0).
    rewrite val_type_unfold in HVF.
    destruct vf; try solve [inversion HVF].
    
    destruct HVF as [C1 [C2 IHF]].
    ev. destruct (IHF dx vx) as [dy [vy [IW3 HVY]]]. apply HVX.
    exists vy. split. {
      (* pick large enough n. nf+nx+ny will do. *)
      destruct IW1 as [nf IWF].
      destruct IW2 as [nx IWX].
      destruct IW3 as [ny IWY].
      exists (S (nf+nx+ny)). intros. destruct n. omega. simpl.
      rewrite IWF. rewrite IWX. rewrite IWY. eauto.
      omega. omega. omega.
    }
    intros. subst T. eapply vtp_subst2. assumption. eapply HVY. eapply D.

  - Case "Abs".
    rewrite <-(wf_length2 _ _ _ WFE) in H.
    inversion H; subst.
    (* vabs doesn't have a type member, so construct a bogus vseta *)
    exists (fun n => match n return vset n with
                     | 0 => fun v => True
                     | S n0 => (fun d v => True)
                   end).
    
    eexists. split. exists 0. intros. destruct n. omega. simpl. eauto.
    intros. rewrite val_type_unfold. repeat split; eauto.
    intros.
    assert (R_env (vx::venv) (jj::renv) (T1::env)) as WFE1. {
      eapply wf_env_extend0. eapply WFE. eapply H0. }
    specialize (IHW (vx::venv) (jj::renv) WFE1).
    destruct IHW as [d [v [EV VT]]]. rewrite <-(wf_length2 _ _ _ WFE) in VT.
    exists v. split. eapply EV.
    intros. eapply vtp_subst3. assumption. eapply VT.

  - Case "Sub".
    specialize (IHW venv WFE). ev. exists x. exists x0. split. eassumption.
    intros. eapply valtp_widen. eapply H1. eapply H. eapply WFE.

Grab Existential Variables.

Qed.