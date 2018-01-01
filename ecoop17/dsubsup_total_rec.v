(* Termination for D<:> with intersection types and recursive self types *)
(* this version includes a proof of totality  *)

(*
 DSub (D<:) + Bot + /\ + { z => ... }
 T ::= Top | Bot | x.Type | { Type: S..U } | (z: T) -> T^z | T1 /\ T2 | { z => T^z }
 t ::= x | { Type = T } | lambda x:T.t | t t | unpack(t) { x => t }
 *)

Require Import Coq.Program.Equality.

Require Import dsubsup_total_rec_base.
Require Import dsubsup_total_rec_binding.

(* ### Semantic Interpretation of Types (Logical Relations) ### *)
(* NEW DESIGN IDEA:

   The required invariants about runtime evaluation rely in crucial
   ways on transporting properties from the creation site of
   type objects to their use sites -- in particular the fact
   that only type aliases can be created (TMem T T), and that these
   cannot be recursive.

   This suggests that in the proof, we should pair each (vty T) value
   with the semantic interpretation of the type member [[ T ]].

   So [[ T ]] in general is no longer a set of values, but a set of
   (vl, vset) pairs. This leads to some complication as the type vset
   is now recursive

      Definition vset := vset -> vl -> Prop.

   which Coq wouldn't let us do (for good reasons).

   But we can do some close with an indexed variant such that

      vset (S n) := vset n -> vl -> Prop

   and quantify over n to denote all finite ones.

   As it turns out, we no longer need the previuos l/u bound selectors,
   and the TMem case can ensure that the *actual* type member of an
   object is inbetween the given bounds. This enables the case for
   intersection types.
*)

Fixpoint vset n := match n with
                     | 0 => vl -> Prop
                     | S n => vset n -> vl -> Prop
                   end.

Definition vseta := forall n, vset n.


(* this is just a helper for pattern matching *)
Inductive vset_match : nat -> Type :=
| vsmatch: forall n, vset n -> vset_match n
.


Require Coq.Program.Wf.

Program Fixpoint val_type (env: list vseta) (GH:list vseta) (T:ty) n (dd: vset n) (v:vl) {measure (tsize_flat T)}: Prop :=
  match v,T with
    | vabs env1 T0 y, TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall jj vx,
        (forall kx, val_type env GH T1 kx (jj kx) vx) ->
        exists (jj2:vseta) v, tevaln (vx::env1) y v /\ (forall k, val_type env (jj::GH) (open (varH (length GH)) T2) k (jj2 k) v)

    | vty env1 TX, TMem T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2 /\
      match (vsmatch n dd) with
        | vsmatch 0 dd => True
        | vsmatch (S n0) dd => forall (dy:vseta) vy,
                      (val_type env GH T1 n0 (dy n0) vy -> dd (dy n0) vy) /\
                      (dd (dy n0) vy -> val_type env GH T2 n0 (dy n0) vy)
      end

    | _, TSel (varF x) =>
      match indexr x env with
        | Some jj => jj (S n) dd v
        | _ => False
      end
    | _, TSel (varH x) =>
      match indexr x GH with
        | Some jj => jj (S n) dd v
        | _ => False
      end

    | _, TAnd T1 T2 =>
      val_type env GH T1 n dd v /\ val_type env GH T2 n dd v

    | _, TBind T1 =>
      closed 1 (length GH) (length env) T1 /\
      exists jj:vseta, jj n = dd /\ forall n, val_type env (jj::GH) (open (varH (length GH)) T1) n (jj n) v

    | _, TTop =>
      True
    | _,_ =>
      False
  end.

Ltac smaller_types :=
  Tactics.program_simpl; simpl;
  unfold open; try rewrite <- open_preserves_size; omega.

Ltac discriminatePlus := repeat split; intros; let Habs := fresh "Habs" in intro Habs; destruct Habs; discriminate.

Ltac valTypeObligations := smaller_types || discriminatePlus.

Solve Obligations with valTypeObligations.


(*
   The expansion of val_type, val_type_func is incomprehensible.
   We cannot (easily) unfold and reason about it. Therefore, we prove unfolding of
   val_type to its body as a lemma.
   (Note that the unfold_sub tactic relies on
   functional extensionality)
*)

Import Coq.Program.Wf.
Import WfExtensionality.

Lemma val_type_unfold': forall env GH T n dd v, val_type env GH T n dd v =
  match v,T with
    | vabs env1 T0 y, TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall jj vx,
        (forall kx, val_type env GH T1 kx (jj kx) vx) ->
        exists (jj2:vseta) v, tevaln (vx::env1) y v /\ (forall k, val_type env (jj::GH) (open (varH (length GH)) T2) k (jj2 k) v)

    | vty env1 TX, TMem T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2 /\
      match (vsmatch n dd) with
        | vsmatch 0 dd => True
        | vsmatch (S n0) dd => forall (dy:vseta) vy,
                      (val_type env GH T1 n0 (dy n0) vy -> dd (dy n0) vy) /\
                      (dd (dy n0) vy -> val_type env GH T2 n0 (dy n0) vy)
      end

    | _, TSel (varF x) =>
      match indexr x env with
        | Some jj => jj (S n) dd v
        | _ => False
      end
    | _, TSel (varH x) =>
      match indexr x GH with
        | Some jj => jj (S n) dd v
        | _ => False
      end

    | _, TAnd T1 T2 =>
      val_type env GH T1 n dd v /\ val_type env GH T2 n dd v

    | _, TBind T1 =>
      closed 1 (length GH) (length env) T1 /\
      exists jj:vseta, jj n = dd /\ forall n, val_type env (jj::GH) (open (varH (length GH)) T1) n (jj n) v

    | _, TTop =>
      True
    | _,_ =>
      False
  end.



Proof. (*
  intros. unfold val_type at 1. unfold val_type_func.
  unfold_sub val_type (val_type env GH T n dd v).
  simpl.
  ...

  We admit this lemma here for performance reasons. The invocations
  of unfold_sub. simpl. above can take Coq an hour or more to
  complete (for reasons that are not clear).

  The right-hand side of val_type_unfold has been copied and pasted
  literally from val_type, so there is no question about the
  validity of the lemma. *)
Admitted.


(* this is just to accelerate Coq -- val_type in the goal is slooow *)
Inductive vtp: list vseta -> list vseta -> ty -> forall n, vset n -> vl -> Prop :=
| vv: forall G H T n dd v, val_type G H T n dd v -> vtp G H T n dd v.


Lemma unvv: forall G H T n dd v,
  vtp G H T n dd v -> val_type G H T n dd v.
Proof.

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

intros. inversion H0. apply inj_pair2_eq_dec in H2. subst. assumption.
apply eq_nat_dec.
Qed.

Axiom prop_extensionality:
  forall (P Q: Prop), (P <-> Q) -> P = Q.
Lemma vtp_unfold_aux: forall G H T n dd v,
  vtp G H T n dd v = val_type G H T n dd v.
Proof.
  intros.
  apply prop_extensionality.
  split; intros.
  apply unvv. assumption.
  constructor. assumption.
Qed.

Require Import FunctionalExtensionality.
Lemma vtp_unfold:
  vtp = val_type.
Proof.
  repeat (apply functional_extensionality_dep; intro).
  apply vtp_unfold_aux.
Qed.

Lemma val_type_unfold: forall env GH T n dd v, vtp env GH T n dd v =
  match v,T with
    | vabs env1 T0 y, TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall jj vx,
        (forall kx, vtp env GH T1 kx (jj kx) vx) ->
        exists (jj2:vseta) v, tevaln (vx::env1) y v /\ (forall k, vtp env (jj::GH) (open (varH (length GH)) T2) k (jj2 k) v)

    | vty env1 TX, TMem T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2 /\
      match (vsmatch n dd) with
        | vsmatch 0 dd => True
        | vsmatch (S n0) dd => forall (dy:vseta) vy,
                      (vtp env GH T1 n0 (dy n0) vy -> dd (dy n0) vy) /\
                      (dd (dy n0) vy -> vtp env GH T2 n0 (dy n0) vy)
      end

    | _, TSel (varF x) =>
      match indexr x env with
        | Some jj => jj (S n) dd v
        | _ => False
      end
    | _, TSel (varH x) =>
      match indexr x GH with
        | Some jj => jj (S n) dd v
        | _ => False
      end

    | _, TAnd T1 T2 =>
      vtp env GH T1 n dd v /\ vtp env GH T2 n dd v

    | _, TBind T1 =>
      closed 1 (length GH) (length env) T1 /\
      exists jj:vseta, jj n = dd /\ forall n, vtp env (jj::GH) (open (varH (length GH)) T1) n (jj n) v

    | _, TTop =>
      True
    | _,_ =>
      False
  end.
Proof.
  intros;
    rewrite vtp_unfold;
    rewrite val_type_unfold';
    reflexivity.
Qed.

(* some quick examples *)

Example ex0 : forall n dd v, vtp [] [] (TTop) n dd v.
Proof.
  intros. rewrite val_type_unfold. destruct v; auto.
Qed.

Example ex1: forall G1 GH T n, exists (dd:vset (S n)), forall d v, vtp G1 GH T n d v <-> dd d v.
Proof.
  intros.

  simpl.
  exists (fun d v => vtp G1 GH T n d v). intros.
  split; intros; assumption.
Qed.

Example ex3: forall H T n d, vtp [] [] (TMem TBot TTop) n d (vty H T).
Proof.
  intros. rewrite val_type_unfold.
  split. constructor.
  split. constructor.
  destruct n. trivial.
  intros. split. intros. rewrite val_type_unfold in H0. destruct vy; inversion H0.
  intros. rewrite val_type_unfold. destruct vy; trivial.
Qed.


(* This lemma  establishes that vtp indeed defines a value set (vseta).
   We need this result in the t_typ/TMem case in the main proof,
   to establish a vseta equivalent to [[ T1 ]] that can be passed
   to [[ TMem T1 T1 ]].
  *)
Example valtp_to_vseta: forall G1 GH T, exists (dd:vseta),
    forall n d v, vtp G1 GH T n d v <-> dd (S n) d v.
Proof.
  intros.

  simpl.
  exists (fun n => match n return vset n with
                     | 0 => fun v => True
                     | S n0 => (fun d v => vtp G1 GH T n0 d v)
                   end).
  intros.
  split; intros; assumption.
Qed.





(* consistent environment *)
Definition R_env venv genv tenv :=
  length venv = length tenv /\
  length genv = length tenv /\
  forall x TX, indexr x tenv = Some TX ->
    (exists (jj:vseta) vx,
       indexr x venv = Some vx /\
       indexr x genv = Some jj /\
       forall n, vtp genv [] TX n (jj n) vx).


(* automation *)
Hint Unfold venv.
Hint Unfold tenv.

Hint Unfold open.

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

(*
(* instantiate it to TTop *)
Example ex20: has_type [polyId] (tapp (tvar 0) (ttyp TTop)) (TAll TTop TTop).
Proof.
  crush.
Qed.
*)

(* ############################################################ *)
(* Proofs *)
(* ############################################################ *)



(* ## Extension, Regularity ## *)

Lemma wf_length : forall vs gs ts,
                    R_env vs gs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
Qed.

Lemma wf_length2 : forall vs gs ts,
                    R_env vs gs ts ->
                    (length gs = length ts).
Proof.
  intros. destruct H. destruct H0. auto.
Qed.


Hint Immediate wf_length.



Lemma indexr_safe_ex: forall H1 GH G1 TF i,
             R_env H1 GH G1 ->
             indexr i G1 = Some TF ->
             exists d v, indexr i H1 = Some v /\ indexr i GH = Some d /\ forall n, vtp GH [] TF n (d n) v.
Proof.
  intros. destruct H. destruct H2. destruct (H3 i TF H0) as [d [v [E [V G]]]].
  exists d. exists v. split. eauto. split. eauto. intros. apply (G n).
Qed.








(* ### Value Typing / Logical Relation for Values ### *)

(* NOTE: we need more generic internal lemmas, due to contravariance *)

(* used in valtp_widen *)
Lemma valtp_closed: forall T1 df vf GH H1 n,
  vtp H1 GH T1 n (df n) vf ->
  closed 0 (length GH) (length H1) T1.
Proof.
  induction T1; intros; destruct vf;
  rewrite val_type_unfold in H; try eauto; try contradiction; ev;
    try solve [constructor; eauto];
    (* sel *)
    norepeat_match_case_analysis;
    try match_case_analysis_remember;
    try contradiction;
    eauto using indexr_max.
Qed.

Ltac intro_val_type :=
  ev;
  repeat
    match goal with
    | |- exists x, ?P => eexists
    end;
  split_conj; try eassumption.

Ltac eauto_bind := unfold open; eauto with bind.
    (* unfold open; *)
    (* eapply IHn; autorewrite with core; eauto. *)

Ltac dispatch_sel_case :=
  simpl;
  match goal with
  | |- context f [if ?x then _ else _] =>
    let L := fresh "L"
    in let Heq := fresh "Heq"
       in remember x as L eqn: Heq; destruct L; symmetry in Heq;
          apply beq_nat_true in Heq || apply beq_nat_false in Heq
  end;
  omega ||
        norepeat_match_case_analysis_goal; auto.

Ltac dispatch_sel_inv_case :=
  simpl in *;
  match goal with
  | H : context f [if ?x then _ else _] |- _ =>
    let L := fresh "L"
    in let Heq := fresh "Heq"
       in remember x as L eqn: Heq; destruct L; symmetry in Heq;
          apply beq_nat_true in Heq || apply beq_nat_false in Heq
  end;
  omega ||
        norepeat_match_case_analysis_goal; auto.


Lemma valtp_extend_aux: forall n T1 vx vf df k H1 G1,
  tsize_flat T1 < n ->
  closed 0 (length G1) (length H1) T1 ->
  (vtp H1 G1 T1 k (df k) vf <-> vtp (vx :: H1) G1 T1 k (df k) vf).
Proof.
  intros *;
  revert n T1 vx vf df k G1;
  induction n; intros * S C. { (* n = 0 *) inversion S. }

  (* Split induction hypothesis so that automation can find it: *)
  (* forall (vx : vseta) (vf : vl) (df : forall x : nat, vset x) (k : nat), *)
  (*       tsize_flat T1 < n -> *)
  (*       closed 0 (length G1) (length H1) T1 -> *)
  (*       vtp H1 G1 T1 k (df k) vf <-> vtp (vx :: H1) G1 T1 k (df k) vf *)
  assert (IHn1 :
            forall (T1 : ty) (vx : vseta) (vf : vl) (df : forall x : nat, vset x) (k : nat) (G1 : list vseta),
        tsize_flat T1 < n ->
        closed 0 (length G1) (length H1) T1 ->
        vtp (vx :: H1) G1 T1 k (df k) vf -> vtp H1 G1 T1 k (df k) vf)
    by (intros; eapply IHn; eauto).
  assert (IHn2 :
            forall (T1 : ty) (vx : vseta) (vf : vl) (df : forall x : nat, vset x) (k : nat) (G1 : list vseta),
        tsize_flat T1 < n ->
        closed 0 (length G1) (length H1) T1 ->
        vtp H1 G1 T1 k (df k) vf -> vtp (vx :: H1) G1 T1 k (df k) vf)
    by (intros; eapply IHn; eauto).
  clear IHn.

  destruct T1; split; intros V; rewrite val_type_unfold in V |- *; eauto;
    norepeat_match_case_analysis_goal;
    try solve by inversion; ev; split_conj; intros; inversion C; subst; eauto_bind.
  -
    specialize (H2 jj vx0).
    match type of H2 with
    | ?T -> _ => assert (Hv: T) by (intros; eauto); specialize (H2 Hv)
    end.
    intro_val_type; intros; eauto_bind.

  -
    (* match type of H2 with *)
    (* | forall x y, ?P -> _ => *)
    (*   assert (Hv: P) by (intros; eauto); specialize (H2 _ _ Hv) *)
    (*   (* assert (Hv: P x y) by (intros; eauto); specialize (H2 _ _ Hv) *) *)
    (* end. *)
    specialize (H2 jj vx0).
    match type of H2 with
    | ?T -> _ => assert (Hv: T) by (intros; eauto); specialize (H2 Hv)
    end.
    intro_val_type; intros; eauto_bind.
  - dispatch_sel_case.
  - dispatch_sel_case.
  - dispatch_sel_inv_case.
  - dispatch_sel_inv_case.

  - match_case_analysis_goal; trivial; intros;
    specialize (H2 dy vy); ev;
    split_conj; intros; eauto.

  - match_case_analysis_goal; trivial; intros;
    specialize (H2 dy vy); ev;
    split_conj; intros; eauto.

  - intro_val_type; intros; eauto_bind.
  - intro_val_type; intros; eauto_bind.
  - intro_val_type; intros; eauto_bind.
  - intro_val_type; intros; eauto_bind.
Qed.


(* used in wf_env_extend and in main theorem *)
Lemma valtp_extend: forall vx vf df k G1 H1 T1,
  vtp H1 G1 T1 k (df k) vf ->
  vtp (vx::H1) G1 T1 k (df k) vf.
Proof.
  intros; eapply valtp_extend_aux with (H1 := H1); eauto using valtp_closed.
Qed.

(* used in wf_env_extend *)
Lemma valtp_shrink: forall vx vf df k G1 H1 T1,
  vtp (vx::H1) G1 T1 k (df k) vf ->
  closed 0 (length G1) (length H1) T1 ->
  vtp H1 G1 T1 k (df k) vf.
Proof.
  intros; eapply valtp_extend_aux; eauto.
Qed.

Lemma valtp_shrinkM: forall vx vf df k H1 GH T1,
  vtp (vx::H1) GH T1 k (df k) vf ->
  closed 0 (length GH) (length H1) T1 ->
  vtp H1 GH T1 k (df k) vf.
Proof.
  intros; eapply valtp_extend_aux; eauto.
Qed.

Lemma valtp_splice_aux: forall n T vf H GH1 GH0 jj df k,
tsize_flat T < n -> closed 0 (length (GH1 ++ GH0)) (length H) T ->
(
  vtp H (GH1 ++ GH0) T k (df k) vf <->
  vtp H (GH1 ++ jj :: GH0) (splice (length GH0) T) k (df k) vf
).
Proof.
  intros *.
  rewrite app_length in *.
  revert n T vf H GH1 GH0 jj df k.
  induction n; intros * Sz C.
  { inversion Sz. }


  (* Ltac foo IHn := *)
    (* match type of IHn with *)
    (* | forall _ _ _ _ _ _ _ _,  _ -> _ -> ?A <-> ?B => *)
    (*   assert (IHn1: A -> B) by (intros; eapply IHn; eauto); *)
    (*   assert (IHn2: B -> A) by (intros; eapply IHn; eauto) *)
    (* end. *)
  (* foo IHn. *)

  (* Split induction hypothesis so that automation can find it. *)
  assert (IHn2 :
            forall T vf H GH1 GH0 jj df k,
              tsize_flat T < n -> closed 0 (length GH1 + length GH0) (length H) T ->
                vtp H (GH1 ++ jj :: GH0) (splice (length GH0) T) k (df k) vf ->
                vtp H (GH1 ++ GH0) T k (df k) vf)
    by (intros; eapply IHn; eauto).
  assert (IHn1 :
            forall T vf H GH1 GH0 jj df k,
              tsize_flat T < n -> closed 0 (length GH1 + length GH0) (length H) T ->
              vtp H (GH1 ++ GH0) T k (df k) vf ->
              vtp H (GH1 ++ jj :: GH0) (splice (length GH0) T) k (df k) vf)
    by (intro T0; intros; eapply IHn with (T := T0); eauto).
  clear IHn.
  destruct T; split; intros V; simpl in *; rewrite val_type_unfold in V;
    assert (length GH1 + S (length GH0) = S (length (GH1 ++ GH0))) as E;
    try rewrite app_length in *; try omega; unfold open in *;
      rewrite val_type_unfold; norepeat_match_case_analysis; eauto; try solve by inversion;
        split_conj; ev; simpl; try rewrite app_length in *; simpl;
    try solve [try inversion C; subst; try rewrite E; eauto using closed_splice]; intros.
  -
    specialize (H2 jj0 vx).
    match type of H2 with
    | ?T -> _ => assert (Hv: T) by (intros; eauto); specialize (H2 Hv)
    end.
    ev; intro_val_type; intros.
    unfold open in *;
      simpl;
      rewrite app_comm_cons;
      rewrite splice_open_permute0'.
    eapply IHn1 with (GH0 := GH0); eauto_bind.

  -
    inversion C; subst.
    specialize (H2 jj0 vx).
    match type of H2 with
    | ?T -> _ => assert (Hv: T) by (intros; eauto); specialize (H2 Hv)
    end.
    ev; intro_val_type; intros.
    rewrite app_comm_cons in *.
    eapply IHn2 with (GH0 := GH0); eauto_bind.
    specialize (Hv k0).

    unfold open in *;
      simpl in *;
      rewrite splice_open_permute0' in H4.
    eauto.

  - simpl in *.
    destruct v.
    + assumption.
    + destruct (indexr i (GH1 ++ GH0)) eqn : B; try solve by inversion.
    destruct (le_lt_dec (length GH0) i) eqn : A.
    assert (indexr (i + 1) (GH1 ++ jj :: GH0) = Some v). apply indexr_hit_high. assumption. omega.
    rewrite H0. apply V. assert (indexr (i) (GH1 ++ jj :: GH0) = Some v). apply indexr_hit_low. assumption. omega.
    rewrite H0. apply V.
    + inversion V.
    - simpl in *. destruct v; simpl; try apply V.
    destruct (indexr i (GH1 ++ GH0)) eqn : B; try solve by inversion.
    destruct (le_lt_dec (length GH0) i) eqn : A.
    assert (indexr (i + 1) (GH1 ++ jj :: GH0) = Some v). apply indexr_hit_high. assumption. omega.
    rewrite H0. apply V. assert (indexr (i) (GH1 ++ jj :: GH0) = Some v). apply indexr_hit_low. assumption. omega.
    rewrite H0. apply V.

  -  simpl in *. destruct v.
    + assumption.
    + destruct (le_lt_dec (length GH0) i) eqn : A. inversion C. subst.
      rewrite <- app_length in H4.
    eapply indexr_has in H4. ev. assert (indexr (i + 1)(GH1 ++ jj:: GH0) = Some x). apply indexr_hit_high; assumption.
    rewrite H0. rewrite H1 in V. assumption.
    assert (i < length GH0) as H4 by omega. eapply indexr_has in H4. ev. assert (indexr (i)(GH1 ++ GH0) = Some x).
    apply indexr_extend_mult. assumption. assert (indexr i (GH1 ++ jj :: GH0) = Some x). apply indexr_hit_low; assumption.
    rewrite H1. rewrite H2 in V. assumption.
    + inversion V.
    - destruct v; try solve by inversion; try assumption.
    destruct (le_lt_dec (length GH0) i) eqn : A. inversion C. subst.
    rewrite <- app_length in H4.
    eapply indexr_has in H4. ev. assert (indexr (i + 1)(GH1 ++ jj:: GH0) = Some x). apply indexr_hit_high; assumption.
    rewrite H0. rewrite H1 in V. assumption.
    assert (i < length GH0) as H4 by omega. eapply indexr_has in H4. ev. assert (indexr (i)(GH1 ++ GH0) = Some x).
    apply indexr_extend_mult. assumption. assert (indexr i (GH1 ++ jj :: GH0) = Some x). apply indexr_hit_low; assumption.
    rewrite H1. rewrite H2 in V. assumption.

  - inversion C. subst. try solve by inversion.
    simpl in *. ev.

    destruct k. auto. intros. specialize (H2 dy vy). ev. split;
    eauto.

  - inversion C. subst. try solve by inversion.
    simpl in *. ev.

    destruct k. auto.
    intros. specialize (H2 dy vy). ev.
    split; eauto.

  - inversion C. subst. simpl in *.
    intro_val_type; intros; eauto_bind.

    simpl.
    autorewrite with core.
    rewrite app_comm_cons in *.
    unfold open in *.
    apply IHn1; eauto_bind.

  - inversion C; subst. simpl in *.
    intro_val_type; intros.
    unfold open in *.
    autorewrite with core.
    rewrite app_comm_cons in *.
    eapply IHn1; eauto_bind.

  - inversion C; subst. simpl in *.
    intro_val_type; intros.
    unfold open in *.
    rewrite app_comm_cons.
    eapply IHn2 with (GH0 := GH0); eauto_bind.
    rewrite splice_open_permute0' in *.
    eauto.

  - inversion C; subst. simpl in *.
    intro_val_type; intros.
    unfold open in *.
    rewrite app_comm_cons.
    eapply IHn2 with (GH0 := GH0); eauto_bind.
    rewrite splice_open_permute0' in *.
    eauto.
Qed.


(* used in valtp_widen *)
Lemma valtp_extendH: forall vf df k H1 GH T1 jj,
  vtp H1 GH T1 k (df k) vf ->
  vtp H1 (jj::GH) T1 k (df k) vf.
Proof.
  intros. assert (jj::GH = ([] ++ jj :: GH)). simpl. reflexivity. rewrite H0.
  assert (splice (length GH) T1 = T1). apply valtp_closed in H. eapply closed_splice_idem. eassumption. omega.
  rewrite <- H2.
  eapply valtp_splice_aux with (GH0 := GH). eauto. simpl. apply valtp_closed in H. eapply closed_upgrade_free. eassumption. omega.
  simpl. assumption.
Qed.

Lemma valtp_shrinkH: forall vf df k H1 GH T1 jj,
  vtp H1 (jj::GH) T1 k (df k) vf ->
  closed 0 (length GH) (length H1) T1 ->
  vtp H1 GH T1 k (df k) vf.
Proof.
  intros.
  assert (vtp H1 ([] ++ GH) T1 k (df k) vf <->
  vtp H1 ([] ++ jj :: GH) (splice (length GH) T1) k (df k) vf).
  eapply valtp_splice_aux. eauto. simpl. assumption.
  apply H2. simpl. assert (splice (length GH) T1 = T1).
  eapply closed_splice_idem. eassumption. omega.
  rewrite H3. assumption.
Qed.




(* used in invert_abs *)
Lemma vtp_subst1: forall venv jj v d k T2,
  vtp venv [jj] (open (varH 0) T2) k (d k) v ->
  closed 0 0 (length venv) T2 ->
  vtp venv [] T2 k (d k) v.
Proof.
  intros. assert (open (varH 0) T2 = T2). symmetry. unfold open.
  eapply closed_no_open. eapply H0. rewrite H1 in H.
  eapply valtp_shrinkH. simpl. eassumption. assumption.
Qed.

Lemma vtp_subst2_aux: forall n T venv jj v x d m GH j k,
  tsize_flat T < n ->
  closed j (length GH) (length venv) T -> k < j ->
  indexr x venv = Some jj ->
  (vtp venv (GH ++ [jj]) (open_rec k (varH 0) (splice 0 T)) m (d m) v <->
   vtp venv GH (open_rec k (varF x) T) m (d m) v).
Proof.
  induction n; intros ? ? ? ? ? ? ? ? ? ? Sz Cz Bd Id. inversion Sz.
  destruct T; split; intros V; rewrite val_type_unfold in V.
  - unfold open. simpl in *. rewrite val_type_unfold. destruct v; apply V.
  - unfold open. simpl in *. rewrite val_type_unfold. destruct v; apply V.
  - unfold open. simpl in *. rewrite val_type_unfold. destruct v; apply V.
  - unfold open. simpl in *. rewrite val_type_unfold. destruct v; apply V.
  - inversion Cz. subst.
    unfold open in *. simpl in *. rewrite val_type_unfold in *. destruct v; try solve by inversion.
    ev.
    split. {rewrite app_length in *.  simpl in *. eapply splice_retreat4.
    eassumption. constructor. eapply indexr_max. eassumption. }
    split. { rewrite app_length in *. simpl in *. eapply splice_retreat4.
    eassumption. constructor. eapply indexr_max. eassumption. }

    intros. assert (forall kx : nat, vtp venv (GH ++ [jj])
      (open_rec k (varH 0) (splice 0 T1)) kx (jj0 kx) vx).
    intros. specialize (H2 kx). eapply IHn; try omega; eassumption.
    specialize (H1 _ _ H3).
    ev. exists x0. exists x1. split. assumption.
    intros. specialize (H6 k0). unfold open. erewrite open_permute.
    eapply IHn; try rewrite <- open_preserves_size; try omega; try eassumption.
    eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega.
    constructor. simpl. omega. omega.
    simpl. erewrite open_permute in H6. rewrite app_length in H6. replace (length[jj]) with (0+1) in H6.
    rewrite plus_assoc in H6. rewrite splice_open_permute0 in H6. rewrite plus_0_r in H6. assumption.
    simpl. omega. constructor. eauto. constructor. eauto. omega. constructor. eauto. constructor. eauto. omega.

  - inversion Cz. subst.
    unfold open in *. simpl in *. rewrite val_type_unfold in *. destruct v; try solve by inversion. ev.
    split. { rewrite app_length. simpl. eapply splice_retreat5. constructor. omega. eassumption. }
    split. { rewrite app_length. simpl. eapply splice_retreat5. constructor. omega. eassumption. }
    intros. assert (forall kx : nat, vtp venv GH (open_rec k (varF x) T1) kx (jj0 kx) vx).
    intros. specialize (H2 kx). eapply IHn; try omega; eassumption.
    specialize (H1 _ _ H3).
    ev. exists x0. exists x1. split. assumption.
    intros. specialize (H6 k0). rewrite app_comm_cons.
    unfold open. erewrite open_permute. rewrite app_length. replace (length [jj]) with (0+1).
    rewrite plus_assoc. rewrite splice_open_permute0. eapply IHn; try omega; try eassumption.
    rewrite <- open_preserves_size. omega.
    eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega.
    constructor. simpl. omega. omega.
    erewrite open_permute. rewrite plus_0_r. assumption.
    constructor. auto. constructor. auto. omega. simpl. omega. constructor. auto. constructor. auto. omega.

  - unfold open in *. simpl in *. rewrite val_type_unfold in *.
    destruct v; destruct v0; simpl in *; try apply V.
    + assert (indexr (i + 1) (GH ++ [jj]) = indexr i GH). {
    apply indexr_extend_end. }
    rewrite H in V. apply V.
    + destruct (beq_nat k i) eqn : A.
    simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj).
    apply indexr_hit01.
    rewrite H in V. rewrite Id. apply V. inversion V.
    + assert (indexr (i + 1) (GH ++ [jj]) = indexr i GH). apply indexr_extend_end.
    rewrite H in V. apply V.
    + destruct (beq_nat k i) eqn : A.
    simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). apply indexr_hit01.
    rewrite H in V. rewrite Id. apply V. inversion V.

  - unfold open in *. simpl in *. rewrite val_type_unfold in *.
    destruct v; destruct v0; simpl in *; try apply V.
    assert (indexr (i + 1) (GH ++ [jj]) = indexr i GH). apply indexr_extend_end.
    rewrite H. apply V.
    destruct (beq_nat k i) eqn : A.
    simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). apply indexr_hit01.
    rewrite H. rewrite Id in V. apply V. inversion V.
    assert (indexr (i + 1) (GH ++ [jj]) = indexr i GH). apply indexr_extend_end.
    rewrite H. apply V.
    destruct (beq_nat k i) eqn : A.
    simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). apply indexr_hit01.
    rewrite H. rewrite Id in V. apply V. inversion V.

  - inversion Cz. subst.
    unfold open in *. simpl in *. rewrite val_type_unfold in *. destruct v; try solve by inversion.
    ev. rewrite app_length in *.
    split. { eapply splice_retreat4. simpl in *. eassumption. constructor. apply indexr_max in Id. omega. }
    split. { eapply splice_retreat4. simpl in *. eassumption. constructor. apply indexr_max in Id. omega. }
    destruct m. auto.
    intros. specialize (H1 dy vy). ev.
    split. intros. apply H1. eapply IHn; try omega; eassumption.
    intros. specialize (H2 H3). eapply IHn; try omega; eassumption.

  - inversion Cz. subst.
    unfold open in *. simpl in *. rewrite val_type_unfold in *.
    destruct v; try solve by inversion. ev. rewrite app_length in *.
    split. { eapply splice_retreat5. constructor. omega. eassumption. }
    split. { eapply splice_retreat5. constructor. omega. eassumption. }
    destruct m. auto.
    intros. specialize (H1 dy vy). ev. split.
    intros. apply H1. eapply IHn; try omega; eassumption.
    intros. specialize (H2 H3). eapply IHn; try omega; eassumption.

  - inversion Cz. subst. simpl in *. rewrite app_length in *. rewrite val_type_unfold.
    assert (closed 1 (length GH + length [jj]) (length venv)
          (open_rec (S k) (varH 0) (splice 0 T)) /\
        (exists jj0 : forall x0 : nat, vset x0,
           jj0 m = d m /\
           (forall n0 : nat,
            vtp venv (jj0 :: GH ++ [jj])
              (open (varH (length GH + length [jj]))
                 (open_rec (S k) (varH 0) (splice 0 T))) n0 (jj0 n0) v))).
                 destruct v; try assumption. clear V. ev.
    assert (closed 1 (length GH) (length venv) (open_rec (S k) (varF x) T) /\
    (exists jj0 : forall x1 : nat, vset x1,
       jj0 m = d m /\
       (forall n0 : nat,
        vtp venv (jj0 :: GH)
          (open (varH (length GH)) (open_rec (S k) (varF x) T)) n0 (jj0 n0) v))) as Goal.
    split. eapply splice_retreat4. simpl in H. eassumption.
    constructor. eapply indexr_max. eassumption.
    exists x0. split. assumption. intros. specialize (H1 n0).
    unfold open. erewrite open_permute.  eapply IHn.
    rewrite <- open_preserves_size. omega.
    eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega.
    constructor. simpl. omega. omega. eassumption.
    unfold open in *. erewrite open_permute in H1. replace (length [jj]) with (0 + 1) in H1. rewrite plus_assoc in H1.
    rewrite splice_open_permute0 in H1. rewrite plus_0_r in H1. assumption.
    simpl. omega. constructor. auto. constructor. auto. omega. constructor. auto. constructor. auto. omega.
    destruct v; apply Goal.

  - inversion Cz. subst. simpl in *. rewrite val_type_unfold.
    assert (closed 1 (length GH) (length venv) (open_rec (S k) (varF x) T) /\
        (exists jj0 : forall x0 : nat, vset x0,
           jj0 m = d m /\
           (forall n0 : nat,
            vtp venv (jj0 :: GH)
              (open (varH (length GH)) (open_rec (S k) (varF x) T)) n0
              (jj0 n0) v))). destruct v; assumption. clear V. ev.
    assert (closed 1 (length (GH ++ [jj])) (length venv)
      (open_rec (S k) (varH 0) (splice 0 T)) /\
    (exists jj0 : forall x1 : nat, vset x1,
       jj0 m = d m /\
       (forall n0 : nat,
        vtp venv (jj0 :: GH ++ [jj])
          (open (varH (length (GH ++ [jj])))
             (open_rec (S k) (varH 0) (splice 0 T))) n0 (jj0 n0) v))) as Goal.
    split. rewrite app_length. eapply splice_retreat5. constructor. omega. eassumption.
    exists x0. split. assumption. intros. specialize (H1 n0).
    unfold open in *. erewrite open_permute.
    rewrite app_comm_cons. rewrite app_length. replace (length[jj]) with (0+1).
    rewrite plus_assoc. rewrite splice_open_permute0. eapply IHn.
    rewrite <- open_preserves_size. omega.
    eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega.
    constructor. simpl. omega. omega. eassumption. erewrite open_permute. rewrite plus_0_r.
    assumption.
    constructor. auto. constructor. auto. omega. simpl. omega. constructor. auto. constructor. auto. omega.
    destruct v; apply Goal.

  - inversion Cz. subst. rewrite app_length in *. simpl in *. rewrite val_type_unfold.
    assert (vtp venv (GH ++ [jj]) (open_rec k (varH 0) (splice 0 T1)) m (d m) v /\
        vtp venv (GH ++ [jj]) (open_rec k (varH 0) (splice 0 T2)) m (d m) v). destruct v; assumption. clear V. ev.
    assert (vtp venv GH (open_rec k (varF x) T1) m (d m) v /\
    vtp venv GH (open_rec k (varF x) T2) m (d m) v) as Goal.
    split. eapply IHn; try eassumption; try omega.
    eapply IHn; try eassumption; try omega.
    destruct v; apply Goal.

  - inversion Cz. subst. simpl in *. rewrite val_type_unfold.
    assert (vtp venv GH (open_rec k (varF x) T1) m (d m) v /\
        vtp venv GH (open_rec k (varF x) T2) m (d m) v). destruct v; assumption. clear V. ev.
    assert (vtp venv (GH ++ [jj]) (open_rec k (varH 0) (splice 0 T1)) m (d m) v /\
    vtp venv (GH ++ [jj]) (open_rec k (varH 0) (splice 0 T2)) m (d m) v) as Goal.
    split. eapply IHn; try eassumption; try omega.
    eapply IHn; try eassumption; try omega.
    destruct v; apply Goal.


Grab Existential Variables.
all: apply 0.
Qed.


Lemma vtp_subst: forall T venv jj v x d k GH,
  closed 1 (length GH) (length venv) T ->
  indexr x venv = Some jj ->
  (vtp venv (GH ++ [jj]) (open (varH 0) (splice 0 T)) k (d k) v <->
   vtp venv GH (open (varF x) T) k (d k) v).
Proof. intros. eapply vtp_subst2_aux. eauto. eassumption. omega. assumption. Qed.


(* used in invert_dabs *)
Lemma vtp_subst2: forall venv jj v x d k  T2,
  closed 1 0 (length venv) T2 ->
  vtp venv [jj] (open (varH 0) T2) k (d k) v ->
  indexr x venv = Some jj ->
  vtp venv [] (open (varF x) T2) k (d k) v.
Proof.
  intros. assert ([jj] = ([] ++ [jj])). simpl. reflexivity.
  rewrite H2 in H0. assert (splice 0 T2 = T2). eapply closed_splice_idem.
  eassumption. omega. rewrite <- H3 in H0. eapply vtp_subst in H0. eassumption.
  simpl. assumption. assumption.
Qed.

(* used in valtp_bounds *)
Lemma vtp_subst2_general: forall venv jj v x T2 d k,
  closed 1 0 (length venv) T2 ->
  indexr x venv = Some jj ->
  ( vtp venv [jj] (open (varH 0) T2) k (d k) v <->
    vtp venv [] (open (varF x) T2) k (d k) v).
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
Lemma vtp_subst3: forall venv jj v T2 d k,
  closed 1 0 (length venv) T2 ->
  vtp (jj::venv) [] (open (varF (length venv)) T2) k (d k) v ->
  vtp venv [jj] (open (varH 0) T2) k (d k) v.
Proof.
  intros. assert (splice 0 T2 = T2) as EE. eapply closed_splice_idem. eassumption. omega.
  assert (vtp (jj::venv) ([] ++ [jj]) (open (varH 0) (splice 0 T2)) k (d k) v).
  assert (indexr (length venv) (jj :: venv) = Some jj). simpl.
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

Lemma valty_subst4: forall G T1 jj v d k,
  closed 1 0 (length G) T1 ->
  (vtp G [jj] (open (varH 0) T1) k (d k) v <->
   vtp (jj :: G) [] (open (varF (length G)) T1) k (d k) v).
Proof.
  intros. split.
  Case "->". intros. assert (vtp (jj :: G) [jj] (open (varH 0) T1) k (d k) v).
    { eapply valtp_extend_aux with (H1 := G). eauto.
      simpl. eapply closed_open. simpl. eapply closed_inc_mult. eassumption. omega. omega.
      omega. constructor. omega. assumption. }
    assert (vtp (jj :: G) [] (open (varF (length G)) T1) k (d k) v).
    { eapply vtp_subst2_general. simpl. eapply closed_upgrade_freef. eassumption. omega.
      simpl. replace (beq_nat (length G) (length G)) with true. reflexivity. apply beq_nat_refl.
      assumption. } assumption.
  Case "<-". intros. assert (vtp (jj :: G) [jj] (open (varF (length G)) T1) k (d k) v).
    { eapply valtp_extendH. assumption. }
    assert (vtp (jj :: G) [jj] (open (varH 0) T1) k (d k) v).
    { eapply vtp_subst2_general with (x := length G). simpl. eapply closed_upgrade_freef. eassumption. omega.
      simpl. replace (beq_nat (length G) (length G)) with true. reflexivity. apply beq_nat_refl.
      eassumption. }
    eapply valtp_shrinkM. eassumption. simpl. eapply closed_open. simpl. eapply closed_upgrade_free.
    eassumption. omega. constructor. omega.
Qed.




(* ### Relating Value Typing and Subtyping ### *)
Lemma valtp_widen_aux: forall G1 GH1 T1 T2,
  stp G1 GH1 T1 T2 ->
  forall (H: list vseta) GH,
    length G1 = length H ->
    (forall x TX, indexr x G1 = Some TX ->
                   exists vx jj,
                     indexr x H = Some jj /\
                     (forall n, vtp H GH TX n (jj n) vx)) ->
    length GH1 = length GH ->
    (forall x TX, indexr x GH1 = Some TX ->
                   exists vx jj,
                     indexr x GH = Some jj /\
                     (forall n, vtp H GH TX n (jj n) vx)) ->
  (forall kf (df:vseta) vf,
     vtp H GH T1 kf (df kf) vf -> vtp H GH T2 kf (df kf) vf).
Proof.
  intros ? ? ? ? stp.
  induction stp; intros G GHX LG RG LGHX RGHX kf df vf V0.


  - Case "Top".
    rewrite val_type_unfold. destruct vf; reflexivity.
  - Case "Bot".
    rewrite val_type_unfold in V0. destruct vf; inversion V0.
  - Case "mem".
    subst.
    rewrite val_type_unfold in V0.
    rewrite val_type_unfold.
    destruct vf; destruct kf; try destruct b; try solve by inversion; ev.
    + rewrite <-LG. rewrite <-LGHX. split.
      apply stp_closed1 in stp2. assumption. split. apply stp_closed2 in stp1. assumption.
      trivial.
    + rewrite <-LG. rewrite <-LGHX. split.
      apply stp_closed1 in stp2. assumption. split. apply stp_closed2 in stp1. assumption.
      intros. specialize (H1 dy vy). ev. split.
      intros. eapply H1. eapply IHstp2; assumption.
      intros. eapply IHstp1; try assumption. eapply H2. assumption.

  - Case "Sel1".
    subst. specialize (IHstp _ _ LG RG LGHX RGHX).
    rewrite val_type_unfold in V0.
    specialize (RG _ _ H).
    ev. rewrite H1 in V0.
    assert (x1 (S kf) (df kf) vf). destruct vf; eauto. clear V0.


    specialize (IHstp (S kf) x1 x0 (H2 _)).

    rewrite val_type_unfold in IHstp.
    destruct x0. inversion IHstp. ev.
    specialize (H6 df vf). ev.
    eapply H7. eapply H3.

  - Case "Sel2".
    subst. specialize (IHstp _ _ LG RG LGHX RGHX).
    specialize (RG _ _ H).
    ev. specialize (H2 (S kf)).
    specialize (IHstp _ _ _ H2).

    rewrite val_type_unfold in IHstp.
    destruct x0. inversion IHstp. ev.
    specialize (H5 df vf). ev.

    rewrite val_type_unfold. rewrite H1.
    assert (x1 (S kf) (df kf) vf). eapply H5. eapply V0.
    destruct vf; assumption.

  - Case "selx".
    eapply V0.

  (* exactly the same as sel1/sel2, modulo RG/RGHX *)
 - Case "Sela1".
    subst. specialize (IHstp _ _ LG RG LGHX RGHX).
    rewrite val_type_unfold in V0.
    specialize (RGHX _ _ H).
    ev. rewrite H1 in V0.
    assert (x1 (S kf) (df kf) vf). destruct vf; eauto. clear V0.


    specialize (IHstp (S kf) x1 x0 (H2 _)).

    rewrite val_type_unfold in IHstp.
    destruct x0. inversion IHstp. ev.
    specialize (H6 df vf). ev.
    eapply H7. eapply H3.

  - Case "Sela2".
    subst. specialize (IHstp _ _ LG RG LGHX RGHX).
    specialize (RGHX _ _ H).
    ev. specialize (H2 (S kf)).
    specialize (IHstp _ _ _ H2).

    rewrite val_type_unfold in IHstp.
    destruct x0. inversion IHstp. ev.
    specialize (H5 df vf). ev.

    rewrite val_type_unfold. rewrite H1.
    assert (x1 (S kf) (df kf) vf). eapply H5. eapply V0.
    destruct vf; assumption.

  - Case "selax".
    eapply V0.

  - Case "bindx".
    rewrite val_type_unfold. rewrite val_type_unfold in V0.
    assert (closed 1 (length GHX) (length G) T1 /\
           (exists jj : vseta,
              jj kf = df kf /\
              (forall n : nat,
               vtp G (jj :: GHX) (open (varH (length GHX)) T1) n
                        (jj n) vf))). { destruct vf; assumption. }
    clear V0.
    assert (closed 1 (length GHX) (length G) T2 /\
           (exists jj : vseta,
              jj kf = df kf /\
              (forall n : nat,
               vtp G (jj :: GHX) (open (varH (length GHX)) T2) n
                        (jj n) vf))). {
      ev. split. rewrite <-LG. rewrite <-LGHX. assumption.
      exists x. split. assumption.
      intros. subst T2'.
      rewrite <-LGHX.
      eapply IHstp. eapply LG.

      (* extend RG *)
      intros ? ? IX. destruct (RG _ _ IX) as [vx0 [jj0 [IX1 FA]]].
      exists vx0. exists jj0. split. assumption.
      intros. eapply valtp_extendH. eapply FA. simpl. rewrite LGHX. reflexivity.

      (* extend RGHX *)
      intros ? ? IX.
      { case_eq (beq_nat x0 (length GHX)); intros E.
        + simpl in IX. rewrite LGHX in IX. rewrite E in IX. inversion IX. subst TX.
          exists vf. exists x. split. simpl. rewrite E. reflexivity.
          intros. subst T1'. rewrite LGHX. eapply H5.
        + assert (indexr x0 GH = Some TX) as IX0.
          simpl in IX. rewrite LGHX in IX. rewrite E in IX. inversion IX. reflexivity.
          specialize (RGHX _ _ IX0). ev.
          exists x1. exists x2. split. simpl. rewrite E. assumption.
          intros. eapply valtp_extendH. eapply H6.
      }
      subst T1'. rewrite LGHX. eapply H5.
    }
    destruct vf; assumption.

  - Case "And11".
    rewrite val_type_unfold in V0.
    destruct vf; ev; eapply IHstp; assumption.

  - Case "And12".
    rewrite val_type_unfold in V0.
    destruct vf; ev; eapply IHstp; assumption.

  - Case "And2".
    rewrite val_type_unfold.
    destruct vf.
    split. eapply IHstp1; assumption. eapply IHstp2; assumption.
    split. eapply IHstp1; assumption. eapply IHstp2; assumption.

  - Case "Fun".
    subst.
    rewrite val_type_unfold in V0.
    assert (vtp G GHX (TAll T3 T4) kf (df kf) vf). rewrite val_type_unfold.
    subst. destruct vf; try solve [inversion V0].
    destruct V0 as [? [? LR]].
    assert (closed 0 (length GHX) (length G) T3). rewrite <-LG. rewrite <-LGHX. eapply stp_closed in stp1. eapply stp1.
    assert (closed 1 (length GHX) (length G) T4). rewrite <-LG. rewrite <-LGHX. eapply H1.
    split. eauto. split. eauto.
    intros jj vx VX0.

    specialize (IHstp1 _ _ LG RG LGHX RGHX).

    assert (forall kx, vtp G GHX T1 kx (jj kx) vx) as VX1. {
      intros. specialize (IHstp1 kx jj vx). eapply IHstp1. eapply VX0. }

    destruct (LR jj vx VX1) as [jj2 [v [TE VT]]].

    exists jj2. exists v. split. eapply TE. intros.

    (* now deal with function result! *)
    rewrite <-LGHX. rewrite <-LGHX in VT.

    (* broaden goal so that we can apply stp2 *)
    eapply IHstp2. eapply LG.

    (* extend RG *)
    intros ? ? IX. destruct (RG _ _ IX) as [vx0 [jj0 [IX1 FA]]].
    exists vx0. exists jj0. split. assumption.
    intros. eapply valtp_extendH. eapply FA. simpl. rewrite LGHX. reflexivity.

    (* extend RGHX *)
    intros ? ? IX.
    { case_eq (beq_nat x (length GHX)); intros E.
      + simpl in IX. rewrite LGHX in IX. rewrite E in IX. inversion IX. subst TX.
        exists vx. exists jj. split. simpl. rewrite E. reflexivity.
        intros. eapply valtp_extendH. eapply VX0.
      + assert (indexr x GH = Some TX) as IX0.
        simpl in IX. rewrite LGHX in IX. rewrite E in IX. inversion IX. reflexivity.
        specialize (RGHX _ _ IX0). ev.
        exists x0. exists x1. split. simpl. rewrite E. assumption.
        intros. eapply valtp_extendH. eapply H6.
    }
    eapply VT. eapply H.

  - Case "trans".
    specialize (IHstp1 _ _ LG RG LGHX RGHX kf df vf).
    specialize (IHstp2 _ _ LG RG LGHX RGHX kf df vf).
    eapply IHstp2. eapply IHstp1. eapply V0.
Qed.


Lemma valtp_widen: forall kf (df:vseta) vf GH H G1 T1 T2,
  vtp GH [] T1 kf (df kf) vf ->
  stp G1 [] T1 T2 ->
  R_env H GH G1 ->
  vtp GH [] T2 kf (df kf) vf.
Proof.
  intros. destruct H2 as [L1 [L2 A]]. symmetry in L2.
  eapply valtp_widen_aux; try eassumption; try reflexivity.

  intros. specialize (A _ _ H2). ev.
  eexists. eexists. split. eassumption. eassumption.

  intros. inversion H2.
Qed.


Lemma wf_env_extend: forall vx jj G1 R1 H1 T1,
  R_env H1 R1 G1 ->
  (forall n, vtp (jj::R1) [] T1 n (jj n) vx) ->
  R_env (vx::H1) (jj::R1) (T1::G1).
Proof.
  intros. unfold R_env in *. destruct H as [L1 [L2 U]].
  split. simpl. rewrite L1. reflexivity.
  split. simpl. rewrite L2. reflexivity.
  intros. simpl in H. case_eq (beq_nat x (length G1)); intros E; rewrite E in H.
  - inversion H. subst T1. exists jj. exists vx.
    split. simpl. rewrite <-L1 in E. rewrite E. reflexivity.
    split. simpl. rewrite <-L2 in E. rewrite E. reflexivity.
    intros. eapply H0.
  - destruct (U x TX H) as [jj0 [vy0 [EV [VY IR]]]].
    exists jj0. exists vy0.
    split. simpl. rewrite <-L1 in E. rewrite E. assumption.
    split. simpl. rewrite <-L2 in E. rewrite E. assumption.
    intros. eapply valtp_extend. eapply IR.
Qed.

Lemma wf_env_extend0: forall vx jj G1 R1 H1 T1,
  R_env H1 R1 G1 ->
  (forall n, vtp R1 [] T1 n (jj n) vx) ->
  R_env (vx::H1) (jj::R1) (T1::G1).
Proof.
  intros.
  assert (forall n, vtp (jj::R1) [] T1 n (jj n) vx) as V0.
  intro. eapply valtp_extend. eapply H0.
  eapply wf_env_extend; assumption.
Qed.



(* ### Main Theorem ### *)


(* type assignment for variables *)

Lemma invert_var : forall x tenv T,
  has_type tenv (tvar x) T -> forall venv renv, R_env venv renv tenv ->
  exists (d: vseta) v, tevaln venv (tvar x) v /\ indexr x venv = Some v /\ indexr x renv = Some d /\ forall k, vtp renv [] T k (d k) v.
Proof.
  intros ? ? ? W. remember (tvar x) as e.
  induction W; intros ? ? WFE; inversion Heqe; try subst x0.

  - Case "Var".
    destruct (indexr_safe_ex venv renv env T1 x) as [d [v [I [D V]]]]. eauto. eauto.

    exists d. exists v. split. exists 0. intros. destruct n. omega. simpl. rewrite I. eauto. split. apply I. split. apply D. eapply V.

  - Case "VarPack".
    unfold R_env in WFE. ev. destruct (H4 _ _ H) as [d [v [I ?]]]. ev.
    exists d. exists v. split. exists 0. intros. destruct n. omega. simpl. rewrite I. reflexivity.
    intros.
    assert (forall n, vtp renv [d] (open (varH 0) T1) n (d n) v). {
      intros. eapply vtp_subst2_general. rewrite H3. assumption. eassumption. eapply H6. }
    split. assumption. split. assumption. intros. rewrite val_type_unfold. rewrite H3.
    destruct v; split; try assumption; exists d; (split; [reflexivity| assumption]).

  - Case "And".
    destruct (IHW1 eq_refl venv renv WFE) as [d1 [v1 [E1 [I1 [D1 HVF]]]]].
    destruct (IHW2 eq_refl venv renv WFE) as [d2 [v2 [E2 [I2 [D2 HVX]]]]].
    rewrite I1 in I2. inversion I2. subst v2.
    rewrite D1 in D2. inversion D2. subst d2.
    exists d1. exists v1.
    split. assumption. split. assumption. split. assumption.
    intros. rewrite val_type_unfold. destruct v1; (split; [apply HVF|apply HVX]).

  - Case "Sub".
    specialize (IHW Heqe venv renv WFE). ev. exists x0. exists x1. split. subst e. eassumption. split. assumption. split. assumption.
    intros. eapply valtp_widen. eapply H4. eapply H. eapply WFE.
Qed.


(* main theorem *)
Theorem full_total_safety : forall e tenv T,
  has_type tenv e T -> forall venv renv, R_env venv renv tenv ->
  exists (d: vseta) v, tevaln venv e v /\ forall k, vtp renv [] T k (d k) v.
Proof.
  intros ? ? ? W.
  induction W; intros ? ? WFE.

  - Case "Var".
    destruct (invert_var x env T1 (t_var x env T1 H H0) venv renv WFE) as [d [v [E [I [D V]]]]].
    exists d. exists v. split. apply E. apply V.
  - Case "VarPack".
    destruct (invert_var x G1 (TBind T1) (t_var_pack _ x T1 T1' H H0 H1) venv renv WFE) as [d [v [E [I [D V]]]]].
    exists d. exists v. split. apply E. apply V.


  - Case "unpack".
    rewrite <-(wf_length2 _ _ _ WFE) in H.
    destruct (IHW1 venv renv WFE) as [dx [vx [IW1 HVX]]].
    specialize (HVX 0).
    rewrite val_type_unfold in HVX.
    assert (exists jj : vseta,
              (forall n : nat,
                 vtp renv [jj] (open (varH 0) T1) n (jj n) vx)) as E.
    destruct vx; ev; exists x0; assumption.
    destruct E as [jj VXH].
    assert (forall n, vtp (jj::renv) [] (open (varF (length renv)) T1) n (jj n) vx) as VXF. {
      assert (closed 1 0 (S (length renv)) T1). { destruct vx; ev; eapply closed_upgrade_freef; try eassumption; auto. }
      intros. eapply vtp_subst2. assumption. eapply valtp_extend. eapply VXH.
      eapply indexr_hit2. reflexivity. reflexivity. }

    assert (R_env (vx::venv) (jj::renv) (T1'::env)) as WFE1.
    eapply wf_env_extend. assumption. rewrite H. assumption.

    specialize (IHW2 _ _ WFE1).
    destruct IHW2 as [dy [vy [IW2 HVY]]].
    clear HVX. clear VXF.

    exists dy. exists vy. split. {
      destruct IW1 as [nx IWX].
      destruct IW2 as [ny IWY].
      exists (S (nx+ny)). intros. destruct n. omega. simpl.
      rewrite IWX. rewrite IWY. eauto.
      omega. omega.
    }
    intros. eapply valtp_shrink.
    eapply HVY. rewrite (wf_length2 _ _ _ WFE). assumption.

  - Case "And".
    destruct (invert_var x env (TAnd T1 T2) (t_and env x T1 T2 W1 W2) venv renv WFE) as [d [v [E [I [D V]]]]].
    exists d. exists v. split. apply E. apply V.

  - Case "Typ".

    specialize valtp_to_vseta. intros S. specialize (S renv [] T1). ev.

    exists x. eexists. split. exists 1. intros. destruct n. inversion H1. simpl. reflexivity.
    rewrite <-(wf_length2 venv renv) in H.
    intros. rewrite val_type_unfold. simpl. repeat split; try eapply H.
    destruct k. trivial. intros. destruct (H0 k (dy k) vy). split; assumption.
    eapply WFE.


  - Case "App".
    rewrite <-(wf_length2 _ _ _ WFE) in H.
    destruct (IHW1 venv renv WFE) as [df [vf [IW1 HVF]]].
    destruct (IHW2 venv renv WFE) as [dx [vx [IW2 HVX]]].

    specialize (HVF 0).
    rewrite val_type_unfold in HVF.
    destruct vf; try solve [inversion HVF].

    destruct HVF as [C1 [C2 IHF]].
    ev. destruct (IHF dx vx) as [dy [vy [IW3 HVY]]]. apply HVX.

    exists dy. exists vy. split. {
      (* pick large enough n. nf+nx+ny will do. *)
      destruct IW1 as [nf IWF].
      destruct IW2 as [nx IWX].
      destruct IW3 as [ny IWY].
      exists (S (nf+nx+ny)). intros. destruct n. omega. simpl.
      rewrite IWF. rewrite IWX. rewrite IWY. eauto.
      omega. omega. omega.
    }
    intros. eapply vtp_subst1. eapply HVY. eapply H.

  - Case "DApp".
    rewrite <-(wf_length2 _ _ _ WFE) in H0.
    destruct (IHW1 venv renv WFE) as [df [vf [IW1 HVF]]].
    destruct (invert_var x env T1 W2 venv renv WFE) as [dx [vx [IW2 [I [D HVX]]]]].

    specialize (HVF 0).
    rewrite val_type_unfold in HVF.
    destruct vf; try solve [inversion HVF].

    destruct HVF as [C1 [C2 IHF]].
    ev. destruct (IHF dx vx) as [dy [vy [IW3 HVY]]]. apply HVX.
    exists dy. exists vy. split. {
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
    exists d. exists v. split. eapply EV.
    intros. eapply vtp_subst3. assumption. eapply VT.

  - Case "Sub".
    specialize (IHW venv renv WFE). ev. exists x. exists x0. split. eassumption.
    intros. eapply valtp_widen. eapply H1. eapply H. eapply WFE.

Grab Existential Variables.

Qed.
