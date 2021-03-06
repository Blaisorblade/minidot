(* Termination for D<> with intersection type and recursive type *)


(* this version includes a proof of totality (like in nano0-total.v *)

(* copied from nano4-total.v *)
(* add TMem and TSel, complicated val_type0 wf definition *)
(* copied from nano4-total1-wip.v / dsubsup.v *)
(* scale up to full D<> *)

(* some proofs are commented out with a label PERF:
   this is just to make Coq go faster through the file *)

(*
XXX first (unsuccessful) attempt at adding a store
XXX add t_unpack term

What's the current problem?

*)


(*
 DSub (D<:) + Bot
 T ::= Top | Bot | x.Type | { Type: S..U } | (z: T) -> T^z | T1 /\ T2 | { z => T^z }
 t ::= x | { Type = T } | lambda x:T.t | t t
 *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.

(* ### Syntax ### *)

Definition id := nat.

(* term variables occurring in types *)
Inductive var : Type :=
| varF : id -> var (* free, in concrete environment *)
| varH : id -> var (* free, in abstract environment  *)
| varB : id -> var (* locally-bound variable *)
.

Inductive ty : Type :=
| TTop : ty
| TBot : ty
(* (z: T) -> T^z *)
| TAll : ty -> ty -> ty
(* x.Type *)
| TSel : var -> ty
(* { Type: S..U } *)
| TMem : ty(*S*) -> ty(*U*) -> ty
| TBind  : ty -> ty (* Recursive binder: { z => T^z },
                         where z is locally bound in T *)
| TAnd : ty -> ty -> ty (* Intersection Type: T1 /\ T2 *)
.

Inductive tm : Type :=
(* x -- free variable, matching concrete environment *)
| tvar : id -> tm
(* { Type = T } *)
| ttyp : ty -> tm
(* lambda x:T.t *)
| tabs : ty -> tm -> tm
(* t t *)
| tapp : tm -> tm -> tm
| tunpack : tm -> tm -> tm                       
.

Inductive vl : Type :=
(* a closure for a lambda abstraction *)
| vabs : list vl (*H*) -> ty -> tm -> vl
(* a closure for a first-class type *)
| vty : list vl (*H*) -> ty -> vl
.

Definition tenv := list ty. (* Gamma environment: static *)
Definition venv := list vl. (* H environment: run-time *)


(* ### Representation of Bindings ### *)

(* An environment is a list of values, indexed by decrementing ids. *)

Fixpoint indexr {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (beq_nat n (length l')) then Some a else indexr n l'
  end.

Inductive closed: nat(*B*) -> nat(*H*) -> nat(*F*) -> ty -> Prop :=
| cl_top: forall i j k,
    closed i j k TTop
| cl_bot: forall i j k,
    closed i j k TBot
| cl_all: forall i j k T1 T2,
    closed i j k T1 ->
    closed (S i) j k T2 ->
    closed i j k (TAll T1 T2)
| cl_sel: forall i j k x,
    k > x ->
    closed i j k (TSel (varF x))
| cl_selh: forall i j k x,
    j > x ->
    closed i j k (TSel (varH x))
| cl_selb: forall i j k x,
    i > x ->
    closed i j k (TSel (varB x))
| cl_mem: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TMem T1 T2)
| cl_bind: forall i j k T,
    closed (S i) j k T ->
    closed i j k (TBind T)
| cl_and: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TAnd T1 T2)
.

(* open define a locally-nameless encoding wrt to TVarB type variables. *)
(* substitute var u for all occurrences of (varB k) *)
Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TBot        => TBot
    | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TSel (varF x) => TSel (varF x)
    | TSel (varH i) => TSel (varH i)
    | TSel (varB i) => if beq_nat k i then TSel u else TSel (varB i)
    | TMem T1 T2  => TMem (open_rec k u T1) (open_rec k u T2)
    | TBind T => TBind (open_rec (S k) u T)
    | TAnd T1 T2 => TAnd (open_rec k u T1) (open_rec k u T2)
  end.

Definition open u T := open_rec 0 u T.

(* Locally-nameless encoding with respect to varH variables. *)
Fixpoint subst (U : var) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TAll T1 T2   => TAll (subst U T1) (subst U T2)
    | TSel (varB i) => TSel (varB i)
    | TSel (varF i) => TSel (varF i)
    | TSel (varH i) => if beq_nat i 0 then TSel U else TSel (varH (i-1))
    | TMem T1 T2     => TMem (subst U T1) (subst U T2)
    | TBind T       => TBind (subst U T)
    | TAnd T1 T2    => TAnd (subst U T1)(subst U T2)
  end.

Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop         => True
    | TBot         => True
    | TAll T1 T2   => nosubst T1 /\ nosubst T2
    | TSel (varB i) => True
    | TSel (varF i) => True
    | TSel (varH i) => i <> 0
    | TMem T1 T2    => nosubst T1 /\ nosubst T2
    | TBind T       => nosubst T
    | TAnd T1 T2    => nosubst T1 /\ nosubst T2
  end.

(* ### Static Subtyping ### *)
(*
The first env is for looking up varF variables.
The first env matches the concrete runtime environment, and is
extended during type assignment.
The second env is for looking up varH variables.
The second env matches the abstract runtime environment, and is
extended during subtyping.
*)
Inductive stp: tenv -> tenv -> ty -> ty -> Prop :=
| stp_top: forall G1 GH T1,
    closed 0 (length GH) (length G1) T1 ->
    stp G1 GH T1 TTop
| stp_bot: forall G1 GH T2,
    closed 0 (length GH) (length G1) T2 ->
    stp G1 GH TBot T2
| stp_mem: forall G1 GH S1 U1 S2 U2,
    stp G1 GH U1 U2 ->
    stp G1 GH S2 S1 ->
    stp G1 GH (TMem S1 U1) (TMem S2 U2)
| stp_sel1: forall G1 GH TX T2 x,
    indexr x G1 = Some TX ->
    closed 0 0 (length G1) TX ->
    stp G1 GH TX (TMem TBot T2) ->
    stp G1 GH (TSel (varF x)) T2
| stp_sel2: forall G1 GH TX T1 x,
    indexr x G1 = Some TX ->
    closed 0 0 (length G1) TX ->
    stp G1 GH TX (TMem T1 TTop) ->
    stp G1 GH T1 (TSel (varF x)) 
| stp_selx: forall G1 GH v x,
    indexr x G1 = Some v ->
    stp G1 GH (TSel (varF x)) (TSel (varF x))
| stp_sela1: forall G1 GH TX T2 x,
    indexr x GH = Some TX ->
    closed 0 x (length G1) TX ->
    stp G1 GH TX (TMem TBot T2) ->
    stp G1 GH (TSel (varH x)) T2
| stp_sela2: forall G1 GH TX T1 x,
    indexr x GH = Some TX ->
    closed 0 x (length G1) TX ->
    stp G1 GH TX (TMem T1 TTop) ->
    stp G1 GH T1 (TSel (varH x)) 
| stp_selax: forall G1 GH v x,
    indexr x GH = Some v  ->
    stp G1 GH (TSel (varH x)) (TSel (varH x))

(* stp for recursive type and inersection type *)

| stp_bind1: forall GH G1 T1 T1' T2,
    stp G1 (T1'::GH) T1' T2 ->
    T1' = (open (varH (length GH)) T1) ->
    closed 1 (length GH) (length G1) T1 ->
    closed 0 (length GH) (length G1) T2 ->
    stp G1 GH (TBind T1) T2 

| stp_bind2: forall GH G1 T1 T1' T2,
    stp G1 (T1'::GH) T2 T1' ->
    T1' = (open (varH (length GH)) T1) ->
    closed 1 (length GH) (length G1) T1 ->
    closed 0 (length GH) (length G1) T2 ->
    stp G1 GH T2 (TBind T1) 

| stp_bindx: forall GH G1 T1 T1' T2 T2',
    stp G1 (T1'::GH) T1' T2' ->
    T1' = (open (varH (length GH)) T1) ->
    T2' = (open (varH (length GH)) T2) ->
    closed 1 (length GH) (length G1) T1 ->
    closed 1 (length GH) (length G1) T2 ->
    stp G1 GH (TBind T1) (TBind T2)

| stp_and11: forall GH G1 T1 T2 T,
    stp G1 GH T1 T ->
    closed 0 (length GH) (length G1) T2 ->
    stp G1 GH (TAnd T1 T2) T

| stp_and12: forall GH G1 T1 T2 T,
    stp G1 GH T2 T ->
    closed 0 (length GH) (length G1) T1 ->
    stp G1 GH (TAnd T1 T2) T

| stp_and2: forall GH G1 T1 T2 T,
    stp G1 GH T T1 ->
    stp G1 GH T T2 ->
    stp G1 GH T (TAnd T1 T2)


| stp_all: forall G1 GH T1 T2 T3 T4 x,
    stp G1 GH T3 T1 ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G1) T4 ->
    stp G1 (T3::GH) (open (varH x) T2) (open (varH x) T4) ->
    stp G1 GH (TAll T1 T2) (TAll T3 T4)
| stp_trans: forall G1 GH T1 T2 T3,
    stp G1 GH T1 T2 ->
    stp G1 GH T2 T3 ->
    stp G1 GH T1 T3
.

(* ### Type Assignment ### *)
Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_var: forall x env T1,
           indexr x env = Some T1 ->
           stp env [] T1 T1 ->
           has_type env (tvar x) T1
| t_typ: forall env T1,
           closed 0 0 (length env) T1 ->
           has_type env (ttyp T1) (TMem T1 T1)

(* recursive typing  *)
  | T_VarPack : forall G1 x T1 T1',
      (* has_type G1 (tvar x) T1' -> *)
      indexr x G1 = Some (open (varF x) T1) ->            
      T1' = (open (varF x) T1) ->
      closed 1 0 (length G1) T1 ->
      has_type G1 (tvar x) (TBind T1) 
  | T_VarUnpack : forall G1 x T1 T1',
      (* has_type G1 (tvar x) (TBind T1) -> *)
      indexr x G1 = Some (TBind T1) ->
      T1' = (open (varF x) T1) ->
      closed 0 0 (length G1) T1' ->
      has_type G1 (tvar x) T1'
(* intersection typing *)
  | t_and : forall env e T1 T2,
      has_type env e T1 ->
      has_type env e T2 ->
      has_type env e (TAnd T1 T2)
  | t_and1: forall env e T1 T2,
      has_type env e (TAnd T1 T2) ->
      has_type env e T1
  | t_and2: forall env e T1 T2,
      has_type env e (TAnd T1 T2) ->
      has_type env e T2


  | t_unpack: forall env x y T1 T1' T2,
      has_type env x (TBind T1) ->
      T1' = (open (varF (length env)) T1) ->
      has_type (T1'::env) y T2 ->
      closed 0 0 (length env) T2 ->
      has_type env (tunpack x y) T2
               
               
| t_app: forall env f x T1 T2,
           has_type env f (TAll T1 T2) ->
           has_type env x T1 ->
           closed 0 0 (length env) T2 ->
           has_type env (tapp f x) T2
| t_dapp:forall env f x T1 T2 T,
           has_type env f (TAll T1 T2) ->
           has_type env (tvar x) T1 ->
           T = open (varF x) T2 ->
           closed 0 0 (length env) T ->
           has_type env (tapp f (tvar x)) T
| t_abs: forall env y T1 T2,
           has_type (T1::env) y (open (varF (length env)) T2) ->
           closed 0 0 (length env) (TAll T1 T2) ->
           has_type env (tabs T1 y) (TAll T1 T2)
| t_sub: forall env e T1 T2,
           has_type env e T1 ->
           stp env [] T1 T2 ->
           has_type env e T2
.



(* ### Evaluation (Big-Step Semantics) ### *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
Could use do-notation to clean up syntax.
*)

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | tvar x       => Some (indexr x env)
        | ttyp T       => Some (Some (vty env T))
        | tabs T y     => Some (Some (vabs env T y))
        | tapp ef ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vty _ _)) => Some None
                | Some (Some (vabs env2 _ ey)) =>
                  teval n (vx::env2) ey
              end
          end
        | tunpack ex ey =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              teval n (vx::env) ey 
          end
      end
  end.


Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* ------------------------- NOTES -------------------------
Define value typing (val_type)
val_type0 cannot straightforwardly be defined as inductive
family, because the (forall vx, val_type0 env vx T1 -> ... )
occurrence violates the positivity restriction.
--------------------------------------------------------- *)


Fixpoint tsize_flat(T: ty) :=
  match T with
    | TTop => 1
    | TBot => 1
    | TAll T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TSel _ => 1
    | TMem T1 T2 => S (tsize_flat T1 + tsize_flat T2)	
    | TBind T => S (tsize_flat T)
    | TAnd T1 T2 => S (tsize_flat T1 + tsize_flat T2)
  end. 

Lemma open_preserves_size: forall T x j,
  tsize_flat T = tsize_flat (open_rec j (varH x) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
  - destruct v; simpl; destruct (beq_nat j i); eauto.
Qed.


(* NEW DESIGN IDEA:
  
   The required invariants about runtime evaluation rely in crucial
   ways on transporting properties from the creation site of
   type objects to their use sites -- in particular the fact
   that only type aliased can be created (TMem T T), and that these
   cannot be recursive. 

   This suggests that in the proof, we should pair each (vty T) value
   with the semantic interpretation of the type member [[ T ]].

   So [[ T ]] in general is no longer a set of values, but a set of 
   (vl, vset) pairs. This leads to some complication as the type vset 
   is now recursive: 

      Definition vset := vset -> vl -> Prop.

   which Coq wouldn't let us do (for good reasons).

   It seems like the best we can do is an indexed variant such that

    vset (S n) := vset n -> vl -> Prop

   and quantify over n to denote all finite ones.

   As it turns out, we no longer need the previuos l/u bound selectors,
   and the TMem case can ensure that the *actual* type member of an
   object is inbetween the given bounds. This enables the case for
   intersection types.

   For TBind, there is still some uncertainty.
   
*)

Definition vseta := nat -> Prop.


Require Coq.Program.Wf.

Program Fixpoint val_type (env: list vseta) (GH:list vseta) (T:ty) (STO: list (vl * vseta)) (l:nat)  {measure (tsize_flat T)}: Prop :=
  match indexr l STO,T with
    | Some (vabs env1 T0 y, _), TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall fx lx vx dx,
        val_type env GH T1 fx lx -> indexr lx fx = Some (vx,dx) -> 
        exists fy ly v dy, tevaln (vx::env1) y v /\ indexr ly fy = Some (v,dy) /\ val_type env (dx::GH) (open (varH (length GH)) T2) fy ly

    | Some (vty env1 TX, dd), TMem T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2 /\
      forall k1 k2 ly,
        k1 ++ k2 = STO ->
        (val_type env GH T1 k2 ly -> dd ly) /\
        (dd ly -> val_type env GH T2 STO ly)
    
    | Some (_,_), TSel (varF x) =>
      match indexr x env with
        | Some jj => jj l
        | _ => False
      end
    | Some (_,_), TSel (varH x) =>
      match indexr x GH with
        | Some jj => jj l
        | _ => False
      end

    | Some (_,_), TAnd T1 T2 =>
      val_type env GH T1 STO l /\ val_type env GH T2 STO l
        
    | Some (v,d), TBind T1 =>
      (* NOTE: need to investigate this more. Ideally we would like to express:

          val_type env (dd::GH) (open (varH (length GH)) T1) n (dd n) v

         But this would require dd to be of type vseta instead of vset n. 
         If we change the signature to dd:vseta, however, then we run into 
         trouble with lemma valtp_to_vseta.

      *)
               
      val_type env (d::GH) (open (varH (length GH)) T1) STO l

    | Some (_,_), TTop => 
      True
    | _,_ =>
      False
  end.

Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. unfold open. rewrite <-open_preserves_size. omega. Qed. (* TApp case: open *)
Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. omega. Qed.

(*

Next Obligation. simpl. compute. repeat split; intros; destruct H; inversion H; destruct H0; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; destruct H0; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; destruct H0; inversion H0; inversion H1. Qed.
 *)

Next Obligation. admit. Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.

                                  

                                  
(* 
   The expansion of val_type, val_type_func is incomprehensible. 
   We cannot (easily) unfold and reason about it. Therefore, we prove unfolding of
   val_type to its body as a lemma.
   (Note that the unfold_sub tactic relies on 
   functional extensionality)
*)

Import Coq.Program.Wf.
Import WfExtensionality.

Lemma val_type_unfold: forall env GH T STO l, val_type env GH T STO l =
 match indexr l STO,T with
    | Some (vabs env1 T0 y, _), TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall fx lx vx dx,
        val_type env GH T1 fx lx -> indexr lx fx = Some (vx,dx) -> 
        exists fy ly v dy, tevaln (vx::env1) y v /\ indexr ly fy = Some (v,dy) /\ val_type env (dx::GH) (open (varH (length GH)) T2) fy ly

    | Some (vty env1 TX, dd), TMem T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2 /\
      forall k1 ly,
        ly < length STO ->
        (* ly <> l -> *)
        (* (forall x r, indexr x env = Some r -> r < length STO) -> *)
        (val_type env GH T1 (k1++STO) ly -> dd ly) /\
        (dd ly -> val_type env GH T2 (k1++STO) ly)
    
    | Some (_,_), TSel (varF x) =>
      match indexr x env with
        | Some jj => jj l
        | _ => False
      end
    | Some (_,_), TSel (varH x) =>
      match indexr x GH with
        | Some jj => jj l
        | _ => False
      end

    | Some (_,_), TAnd T1 T2 =>
      val_type env GH T1 STO l /\ val_type env GH T2 STO l
        
    | Some (v,d), TBind T1 =>
      (* NOTE: need to investigate this more. Ideally we would like to express:

          val_type env (dd::GH) (open (varH (length GH)) T1) n (dd n) v

         But this would require dd to be of type vseta instead of vset n. 
         If we change the signature to dd:vseta, however, then we run into 
         trouble with lemma valtp_to_vseta.

      *)
               
      val_type env (d::GH) (open (varH (length GH)) T1) STO l

    | Some (_,_), TTop => 
      True
    | _,_ =>
      False
end.



  

Proof. admit. (* TODO
  intros. unfold val_type at 1. unfold val_type_func.
  unfold_sub val_type (val_type env GH v T i).
  simpl.
  destruct v; simpl; try reflexivity.
  destruct T.
  - destruct i; simpl; try reflexivity.
  - simpl; try reflexivity.
  - destruct i; destruct T1; simpl; reflexivity. 
  - destruct v; simpl; try reflexivity.

  (* TSel case has another match *)
  destruct (indexr i0 env); simpl; try reflexivity;
  destruct v; simpl; try reflexivity.
  (* TSelH *) 
  destruct (indexr i0 GH); simpl; try reflexivity.
  - destruct i; eauto.
  -  destruct T; simpl; try reflexivity;
     try destruct v; simpl; try reflexivity.
     destruct (indexr i0 env); simpl; try reflexivity;
       destruct v; simpl; try reflexivity.
     destruct (indexr i0 GH); simpl; try reflexivity.

     destruct i; simpl; try reflexivity. *)
Qed.


(* this is just to accelerate Coq -- val_type in the goal is slooow *)
Inductive vtp: list vseta -> list vseta -> ty -> list (vl*vseta) -> nat -> Prop :=
| vv: forall G H T n dd, val_type G H T n dd -> vtp G H T n dd.


Lemma unvv: forall G H T n dd,
  vtp G H T n dd -> val_type G H T n dd.
Proof. admit. (* PERF

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

intros. inversion H0. apply inj_pair2_eq_dec in H2. subst. assumption.
apply eq_nat_dec.*)
Qed.





(* make logical relation explicit *)
(* Definition R H G t v T := tevaln H t v /\ val_type G [] v T nil. *)


(* consistent environment *)
Definition R_env venv genv tenv f :=
  length venv = length tenv /\
  length genv = length tenv /\
  forall x TX, indexr x tenv = Some TX ->
    (exists lx vx dx,
       indexr lx f = Some (vx,dx) /\
       indexr x venv = Some vx /\
       indexr x genv = Some dx /\
       vtp genv [] TX f lx).


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
(* Proofs *)
(* ############################################################ *)


(* have to be a bit careful with contravariance, but issues seem manageable *)
Lemma valtp_extend_sto: forall n vf df k l H1 T1,
  tsize_flat T1 < n ->
  (* indexr l k = Some (v,vtp H1 [] TX k) ->  *)
  (vtp H1 [] T1 k l  ->
  vtp H1 [] T1 ((vf,df)::k) l). 
Proof.
  induction n; intros. inversion H.
  destruct T1. 
  - admit.
  - admit.
  - admit.
  - admit.
  - (* TMem *)
    (* 
    eapply unvv in H0. eapply vv. rewrite val_type_unfold in *. 
    remember (indexr l k) as IX1. destruct IX1; try contradiction.
    destruct p. destruct v. contradiction.
    assert (l < length k). eapply indexr_max. eauto. 
    assert (indexr l ((vf, df) :: k) = Some (vty l0 t,v0)) as IX. eapply indexr_extend. auto. 
    rewrite IX.
    ev. split. assumption. split. assumption.*)
    
    admit. (*
    intros. split. specialize (H4 (k1 ++ [(vf,df)]) ly H2).
    ev. rewrite <-app_assoc in H4. simpl in H4. eapply H4. 
    specialize (H4 (k1 ++ [(vf,df)]) ly H2). 
    ev. rewrite <-app_assoc in H6. simpl in H6. eapply H6. *)

    (* eapply IHn. simpl in H. omega.
    eapply vv. eapply H4. eapply H5. *)
    (* done, contravariance ok *)
  - admit. 
  - admit. 
Qed.

(* IMPORTANT BLOCKER *)

(* need in main proof, t_typ case *)
Lemma new_type: forall T1 venv renv STO vf,
                  closed 0 0 (length renv) T1 ->
                  vf = vty venv T1 ->
                  exists df, val_type renv [] (TMem T1 T1) ((vf, df) :: STO) (length STO).
Proof.
  intros.
  exists (val_type renv [] T1 ((vf, val_type renv [] TBot [])::STO)). 
  
  rewrite val_type_unfold. simpl. rewrite <-beq_nat_refl.
  rewrite H0. split. assumption. split. assumption.
  intros. split.

  intros. 

  (* HAVE: 
       val_type renv [] T1 (k1 ++ (vty venv0 T1, val_type renv [] T1 STO) :: STO) ly
     NEED:
       val_type renv [] T1 STO ly

   *)

  admit.

  admit. (* reverse direction is easy *)
Qed.




(* ## Extension, Regularity ## *)

Lemma wf_length : forall vs gs ts f,
                    R_env vs gs ts f ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
Qed.

Lemma wf_length2 : forall vs gs ts f,
                    R_env vs gs ts f ->
                    (length gs = length ts).
Proof.
  intros. destruct H. destruct H0. auto.
Qed.


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

Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.

Ltac inv_mem := match goal with
                  | H: closed 0 (length ?GH) (length ?G) (TMem ?T1 ?T2) |-
                    closed 0 (length ?GH) (length ?G) ?T2 => inversion H; subst; eauto
                  | H: closed 0 (length ?GH) (length ?G) (TMem ?T1 ?T2) |-
                    closed 0 (length ?GH) (length ?G) ?T1 => inversion H; subst; eauto
                end.

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
  admit. (*PERF
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
*)
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
  rewrite H0 in A. apply NPeano.Nat.add_cancel_r in A.
  apply concat_same_length; assumption.
Qed.

Lemma exists_GH1L: forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X) x0,
  length GL = x0 ->
  GU ++ GL = GH1 ++ GH0 ->
  length GH0 <= x0 ->
  exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ GH0.
Proof.
  intros X GU. induction GU; intros.
  - eexists. rewrite app_nil_l. split. reflexivity. simpl in H0. assumption.
  - induction GH1.

    simpl in H0.
    assert (length (a :: GU ++ GL) = length GH0) as Contra. {
      rewrite H0. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H0. inversion H0.
    specialize (IHGU GL GH1 GH0 x0 H H4 H1).
    destruct IHGU as [GH1L [IHA IHB]].
    exists GH1L. split. simpl. rewrite IHA. reflexivity. apply IHB.
Qed.

Lemma exists_GH0U: forall {X} (GH1: list X) (GH0: list X) (GU: list X) (GL: list X) x0,
  length GL = x0 ->
  GU ++ GL = GH1 ++ GH0 ->
  x0 < length GH0 ->
  exists GH0U, GH0 = GH0U ++ GL.
Proof.
  intros X GH1. induction GH1; intros.
  - simpl in H0. exists GU. symmetry. assumption.
  - induction GU.

    simpl in H0.
    assert (length GL = length (a :: GH1 ++ GH0)) as Contra. {
      rewrite H0. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H0. inversion H0.
    specialize (IHGH1 GH0 GU GL x0 H H4 H1).
    destruct IHGH1 as [GH0U IH].
    exists GH0U. apply IH.
Qed.

Lemma stp_splice : forall GX G0 G1 T1 T2 v1,
   stp GX (G1++G0) T1 T2 ->
   stp GX ((map (splice (length G0)) G1) ++ v1::G0)
       (splice (length G0) T1) (splice (length G0) T2).
Proof.
  admit. (*
  intros GX G0 G1 T1 T2 v1 H. remember (G1++G0) as G.
  revert G0 G1 HeqG.
  induction H; intros; subst GH; simpl; eauto.
  - Case "top".
    eapply stp_top.
    rewrite map_splice_length_inc.
    apply closed_splice.
    assumption.
  - Case "bot".
    eapply stp_bot.
    rewrite map_splice_length_inc.
    apply closed_splice.
    assumption.
  - Case "sel1".
    eapply stp_sel1. apply H. assumption.
    assert (splice (length G0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp. reflexivity.
  - Case "sel2".
    eapply stp_sel2. apply H. assumption.
    assert (splice (length G0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp. reflexivity.
  - Case "sela1".
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_sela1.
      apply indexr_splice_hi. eauto. eauto.
      eapply closed_splice in H0. assert (S x = x +1) as A by omega.
      rewrite <- A. eapply H0.
      eapply IHstp. eauto.
    + eapply stp_sela1. eapply indexr_splice_lo. eauto. eauto. eauto.
      assert (splice (length G0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp. eauto.
  - Case "sela2".
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_sela2.
      apply indexr_splice_hi. eauto. eauto.
      eapply closed_splice in H0. assert (S x = x +1) as A by omega.
      rewrite <- A. eapply H0.
      eapply IHstp. eauto.
    + eapply stp_sela2. eapply indexr_splice_lo. eauto. eauto. eauto.
      assert (splice (length G0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp. eauto. 
  - Case "selax".
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_selax.
      eapply indexr_splice_hi. eassumption. assumption.
    + eapply stp_selax. eapply indexr_splice_lo. eauto. eauto.
  - Case "bind1". remember (open (varH (length (map (splice (length G0)) G2 ++ v1 :: G0)))
                          (splice (length G0) T1)) as TT.
    eapply stp_bind1 with TT; try assumption.
    rewrite app_length in *. rewrite map_length in *. simpl in *.
    unfold open in HeqTT. rewrite splice_open_permute in HeqTT.
    assert ( (TT :: map (splice (length G0)) G2 ++ v1 :: G0) 
             = ((TT :: map (splice (length G0)) G2) ++ v1 :: G0) ).
             simpl. reflexivity. rewrite H3.
Lemma map_cons:
  forall (A B : Type) (f : A -> B) (a: A)( l : list A),
  map f (a :: l) = (f a) :: map f l.
Proof. intros. simpl. reflexivity. Qed.
    subst. rewrite <-map_cons. 
    eapply IHstp. simpl. unfold open. reflexivity. simpl. 
    rewrite map_splice_length_inc. eapply closed_splice. assumption. 
    rewrite map_splice_length_inc. eapply closed_splice. assumption. 
    
  - Case "bind2". remember (open (varH (length (map (splice (length G0)) G2 ++ v1 :: G0)))
                           (splice (length G0) T1)) as TT.
    eapply stp_bind2 with TT; try (rewrite map_splice_length_inc; eapply closed_splice); try assumption.
    rewrite app_length in *. rewrite map_length in *. simpl in *. unfold open in *.
    rewrite splice_open_permute in HeqTT. 
    assert ( (TT :: map (splice (length G0)) G2 ++ v1 :: G0)
             = ((TT :: map (splice (length G0)) G2) ++ v1 :: G0)). simpl. reflexivity.
    rewrite H3. subst. rewrite <- map_cons. eapply IHstp. simpl. reflexivity.             

  - Case "bindx". 
    remember (open (varH (length (map (splice (length G0)) G2 ++ v1 :: G0)))
  (splice (length G0) T1)) as TT1.
    remember (open (varH (length (map (splice (length G0)) G2 ++ v1 :: G0)))
  (splice (length G0) T2)) as TT2.
    eapply stp_bindx with TT1 TT2; try (rewrite map_splice_length_inc; eapply closed_splice); try assumption.
    rewrite app_length in *. rewrite map_length in *. simpl in *. unfold open in *.
    rewrite splice_open_permute in HeqTT1, HeqTT2. 
    assert ( (TT1 :: map (splice (length G0)) G2 ++ v1 :: G0)
               = ((TT1 :: map (splice (length G0)) G2) ++ v1 :: G0) ). simpl. reflexivity.
    rewrite H4. subst. rewrite <- map_cons. eapply IHstp. simpl. reflexivity.

  - Case "and11".
    eapply stp_and11. eapply IHstp. reflexivity. 
    rewrite app_length in *. simpl. rewrite map_length.
    rewrite <- plus_n_Sm. eapply closed_splice. assumption.
  - Case "and12".
    eapply stp_and12. eapply IHstp. reflexivity.
    rewrite app_length in *. simpl. rewrite map_length.
    rewrite <- plus_n_Sm. eapply closed_splice. assumption.

  - Case "all".
    eapply stp_all.
    eapply IHstp1. eauto. eauto. eauto.

    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.

    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.

    specialize IHstp2 with (G3:=G0) (G4:=T3 :: G2).
    simpl in IHstp2. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0). subst x.
    rewrite app_length in IHstp2. simpl in IHstp2.
    eapply IHstp2. eauto.*)
Qed.


Lemma stp_extend : forall G1 GH T1 T2 v1,
                       stp G1 GH T1 T2 ->
                       stp G1 (v1::GH) T1 T2.
Proof. Abort. (* later, if needed 
  intros. induction H; eauto using indexr_extend, closed_inc.
  - eapply stp_bind1. subst.
  assert (splice (length GH) T2 = T2) as A2. {
    eapply closed_splice_idem. eassumption. omega.
  }
  assert (splice (length GH) T4 = T4) as A4. {
    eapply closed_splice_idem. apply H2. omega.
  }
  assert (closed 0 (length GH) (length G1) T3). eapply stp_closed1. eauto.
  assert (splice (length GH) T3 = T3) as A3. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (map (splice (length GH)) [T3] ++ v1::GH =
          (T3::v1::GH)) as HGX3. {
    simpl. rewrite A3. eauto.
  }
  apply stp_all with (x:=length (v1 :: GH)).
  apply IHstp1.
  reflexivity.
  apply closed_inc. apply H1.
  apply closed_inc. apply H2.
  simpl.
  rewrite <- A2. rewrite <- A4.
  unfold open.
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. rewrite -> splice_open_permute.
  rewrite <- HGX3.
  apply stp_splice.
  simpl. unfold open in H3. rewrite <- H0. apply H3.
Qed.

Lemma stp_extend_mult : forall G T1 T2 GH GH2,
                       stp G GH T1 T2 ->
                       stp G (GH2++GH) T1 T2.
Proof.
  intros. induction GH2.
  - simpl. assumption.
  - simpl.
    apply stp_extend. assumption.
Qed.
*)
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

Lemma indexr_extend_venv : forall G G' x T,
                       indexr x G = Some T ->
                       venv_ext G' G ->
                       indexr x G' = Some T.
Proof.
  intros G G' x T H HV.
  induction HV.
  - assumption.
  - apply indexr_extend. apply IHHV. apply H.
Qed.



(* TODO: need more about about GH? *)
(* Lemma indexr_safe_ex: forall H1 GH G1 TF i,
             R_env H1 GH G1 ->
             indexr i G1 = Some TF ->
             exists d v, indexr i H1 = Some v /\ exists n, val_type GH [] TF n (d n) v.
Proof.
  intros. destruct H. destruct H2. destruct (H3 i TF H0) as [d [v [E [V G]]]].
  exists d. exists v. split; eauto. intros. ev. exists x. eapply unvv. assumption.
Qed.*)




(*
Inductive res_type: list vset -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv [] v T nil ->
      res_type venv (Some v) T.

Hint Constructors res_type.
Hint Resolve not_stuck.
*)


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
Proof. admit. (*
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
*)
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
Lemma valtp_closed: forall df GH H1 T1 n,
  val_type H1 GH T1 n (df n) ->
  closed 0 (length GH) (length H1) T1.
Proof.
  admit. (*
  intros. destruct T1; destruct vf;
  rewrite val_type_unfold in H; try eauto; try contradiction.
  - (* fun *) destruct i; ev; econstructor; assumption.
  - ev; econstructor; assumption.
  - (* sel *) destruct v.
              remember (indexr i0 H1) as L; try destruct L as [?|]; try contradiction.
              constructor. eapply indexr_max. eauto.
              remember (indexr i0 GH) as L; try destruct L as [?|]; try contradiction.
              constructor. eapply indexr_max. eauto. 
              inversion H. 
  - (* sel *) destruct v.
              remember (indexr i0 H1) as L; try destruct L as [?|]; try contradiction.
              constructor. eapply indexr_max. eauto.
              remember (indexr i0 GH) as L; try destruct L as [?|]; try contradiction.
              constructor. eapply indexr_max. eauto. 
              inversion H.
  - destruct i; try solve by inversion. destruct b.
    ev. constructor; assumption.
    ev. constructor; assumption.
  - destruct i; try solve by inversion.
    ev. constructor; assumption. 
    destruct b.
    ev. constructor; try assumption.
    ev. constructor; try assumption.
  - ev. constructor. assumption.
  - ev. constructor. assumption.
  - ev. constructor; try assumption.
  - ev. constructor; try assumption. *)
Qed.

 
Lemma valtp_extend_aux: forall n T1 vx df k H1 G1,
  tsize_flat T1 < n ->
  closed 0 (length G1) (length H1) T1 ->
  (vtp H1 G1 T1 k (df k) <-> vtp (vx :: H1) G1 T1 k (df k)).
Proof.
  admit. (*
  induction n; intros ? ? ? ? ? ? S C. inversion S.
  destruct T1; split; intros V; apply unvv in V; rewrite val_type_unfold in V.
  - apply vv. rewrite val_type_unfold. assumption.
  - apply vv. rewrite val_type_unfold. assumption.
  - apply vv. rewrite val_type_unfold. assumption.
  - apply vv. rewrite val_type_unfold. assumption.
  - destruct vf. destruct i. 
    + ev. apply vv. rewrite val_type_unfold. split.
    simpl. eapply closed_upgrade_freef. apply H. omega. split. simpl.
    eapply closed_upgrade_freef. apply H0. omega. intros.
    specialize (H2 _ _ H3).
    assert ((forall (vy : vl) (iy : sel),
      if pos iy
      then jj vy iy -> val_type H1 G1 vy T1_1 iy
      else val_type H1 G1 vy T1_1 iy -> jj vy iy)).
    { intros. destruct (pos iy) eqn : A. intros. specialize (H4 vy iy). rewrite A in H4.
      specialize (H4 H6). apply unvv. apply vv in H4. simpl in *. eapply IHn; try omega; try eassumption.
      intros. specialize (H4 vy iy). rewrite A in H4. apply H4. apply unvv. simpl in *. 
      apply vv in H6. apply IHn; try omega; try eassumption. }
    specialize (H2 H6 H5). ev. exists x. split; try assumption.
    apply unvv. apply vv in H7. apply IHn; try eassumption. unfold open. erewrite <- open_preserves_size.
    simpl in *. omega. eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
    constructor. simpl. omega.
    + apply vv. rewrite val_type_unfold. ev. repeat split; try assumption; try (eapply closed_upgrade_freef; [eassumption | simpl; auto]). 
    + apply vv. rewrite val_type_unfold. ev. repeat split; try assumption; try (eapply closed_upgrade_freef; [eassumption | simpl; auto]). 
  

- destruct vf. destruct i.
    + ev. apply vv. rewrite val_type_unfold. inversion C. subst.
    split; try assumption. split; try assumption. intros.
    specialize (H2 _ _ H3).
    assert ((forall (vy : vl) (iy : sel),
      if pos iy
      then jj vy iy -> val_type (vx :: H1) G1 vy T1_1 iy
      else val_type (vx :: H1) G1 vy T1_1 iy -> jj vy iy)).
    { intros. destruct (pos iy) eqn : A. intros. specialize (H4 vy iy). rewrite A in H4. specialize (H4 H6).
      apply unvv. apply vv in H4. simpl in *. apply IHn; try eassumption; try omega.
      specialize (H4 vy iy). rewrite A in H4. intros. apply H4. apply unvv. apply vv in H6. 
      simpl in *. eapply IHn; try eassumption; try omega. }
    specialize (H2 H6 H5). ev. exists x. split; try assumption. apply unvv. apply vv in H7. eapply IHn; try eassumption.
    unfold open. erewrite <- open_preserves_size. simpl in *. omega. simpl. eapply closed_open.
    simpl. eapply closed_upgrade_free. eassumption. omega. constructor. omega.
    + apply vv. rewrite val_type_unfold. ev. inversion C. repeat split; assumption.
    + apply vv. rewrite val_type_unfold. ev. inversion C. repeat split; assumption.


  - apply vv. rewrite val_type_unfold. destruct vf.
    + destruct v.
    destruct (indexr i0 H1) eqn : A.
    assert (indexr i0 (vx :: H1) = Some v). apply indexr_extend. assumption. rewrite H. assumption.
    inversion V. assumption. inversion V. 
    + destruct v.
    destruct (indexr i0 H1) eqn : A. 
    assert (indexr i0 (vx :: H1) = Some v). apply indexr_extend. assumption. rewrite H. assumption.
    inversion V. assumption. inversion V.

  - apply vv. rewrite val_type_unfold. destruct vf.
    + destruct v. inversion C. subst. 
    eapply indexr_has in H4. ev. assert (indexr i0 (vx:: H1) = Some x). apply indexr_extend.
    assumption. rewrite H0 in V. rewrite H. assumption. assumption. inversion V.
    + destruct v. inversion C. subst. 
    eapply indexr_has in H4. ev. assert (indexr i0 (vx:: H1) = Some x). apply indexr_extend.
    assumption. rewrite H0 in V. rewrite H. assumption. assumption. inversion V.

  - inversion C. subst. apply vv. rewrite val_type_unfold. destruct vf. destruct i. inversion V. 
    destruct b; ev. split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    apply unvv. eapply IHn with (H1 := H1). simpl in *. omega. apply H6. apply vv. assumption.
    ev. split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    apply unvv. eapply IHn with (H1 := H1). simpl in *. omega. assumption. apply vv. assumption.
    destruct i. simpl. ev. split. eapply closed_upgrade_freef; try eassumption; try omega.
    split. eapply closed_upgrade_freef; try eassumption; try omega.

    intros. destruct (pos iy) eqn : A. specialize (H2 vy iy). rewrite A in H2. intros.
    assert (val_type H1 G1 vy T1_1 iy). apply unvv. apply vv in H3. simpl in *. eapply IHn; try eassumption; try omega.
    specialize (H2 H4). apply unvv. apply vv in H2. simpl in *. eapply IHn with (H1 := H1); try eassumption; try omega.
            specialize (H2 vy iy). rewrite A in H2. intros. assert (val_type H1 G1 vy T1_2 iy).
    apply unvv. apply vv in H3. simpl in *. eapply IHn; try eassumption; try omega.
    specialize (H2 H4). simpl in *. apply unvv. apply vv in H2. eapply IHn with (H1 := H1); try eassumption; try omega.
    
    destruct b; ev. split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    split. simpl. eapply closed_upgrade_freef. eassumption. omega. 
    simpl in *. apply unvv. apply vv in H2. eapply IHn with (H1 := H1); try eassumption; try omega.
    simpl in *. split. eapply closed_upgrade_freef. eassumption. omega. 
    split. eapply closed_upgrade_freef. eassumption. omega.
    apply unvv. apply vv in H2. eapply IHn with (H1 := H1); try eassumption; try omega.

  - inversion C. subst. apply vv. rewrite val_type_unfold. destruct vf. destruct i. inversion V. destruct b. 
    split; try assumption. split; try assumption. ev. apply unvv. apply vv in H2. simpl in *. eapply IHn; try eassumption;
    try omega. 

    split; try assumption. split; try assumption. ev. apply unvv. apply vv in H2. simpl in *. eapply IHn; try eassumption;
    try omega. 

    destruct i. ev. split; try assumption. split; try assumption.
    intros. destruct (pos iy) eqn : A. specialize (H2 vy iy). rewrite A in H2. intros.
    assert (val_type (vx :: H1) G1 vy T1_1 iy ). apply unvv. apply vv in H3. simpl in *. eapply IHn with (H1 := H1); try eassumption; try omega.
    specialize (H2 H4). apply unvv. apply vv in H2. simpl in *. eapply IHn; try eassumption; try omega.
            specialize (H2 vy iy). rewrite A in H2. intros. assert (val_type (vx :: H1) G1 vy T1_2 iy).
    simpl in *. apply unvv. apply vv in H3. eapply IHn with (H1 := H1); try eassumption; try omega.
    specialize (H2 H4). apply unvv. apply vv in H2. simpl in *. eapply IHn; try eassumption; try omega.

    destruct b; ev. split; try assumption. split; try assumption.
    simpl in *. apply unvv. apply vv in H2. simpl in *. eapply IHn; try eassumption; try omega.
    split; try assumption. split; try assumption.
    simpl in *. apply unvv. apply vv in H2. simpl in *. eapply IHn; try eassumption; try omega.
  - admit. (*inversion C. subst. simpl in *. apply vv. rewrite val_type_unfold.
    destruct vf. split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    ev. intros. assert (val_type H1 (jj :: G1) (vabs l t t0) (open (varH (length G1)) T1) i).
    apply H0. intros. specialize (H2 vy iy). destruct (pos iy). intros. specialize (H2 H5). apply unvv. apply vv in H2.
    eapply IHn; try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega. 
      eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.
    intros. apply H2. apply unvv. apply vv in H5. eapply IHn with (H1 := H1); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.
    assumption.
    apply unvv. apply vv in H5. eapply IHn with (H1 := H1); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.

    split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    ev. intros. assert (val_type H1 (jj :: G1) (vty l t) (open (varH (length G1)) T1) i).
    apply H0. intros. specialize (H2 vy iy). destruct (pos iy). intros. specialize (H2 H5). apply unvv. apply vv in H2.
    eapply IHn; try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega. 
      eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.
    intros. apply H2. apply unvv. apply vv in H5. eapply IHn with (H1 := H1); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.
    assumption.
    apply unvv. apply vv in H5. eapply IHn with (H1 := H1); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.*)
  - admit. (*inversion C. subst. simpl in *. apply vv. rewrite val_type_unfold.
    destruct vf. split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    ev. intros. assert (val_type (vx :: H1) (jj :: G1) (vabs l t t0) (open (varH (length G1)) T1) i).
    apply H0. intros. specialize (H2 vy iy). destruct (pos iy). intros. specialize (H2 H5). apply unvv. apply vv in H2.
    eapply IHn with (H1 := H1); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega. 
      eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.
    intros. apply H2. apply unvv. apply vv in H5. eapply IHn with (H1 := H1); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.
    assumption.
    apply unvv. apply vv in H5. eapply IHn with (H1 := H1); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.

    split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    ev. intros. assert (val_type (vx :: H1) (jj :: G1) (vty l t) (open (varH (length G1)) T1) i).
    apply H0. intros. specialize (H2 vy iy). destruct (pos iy). intros. specialize (H2 H5). apply unvv. apply vv in H2.
    eapply IHn with (H1 := H1); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega. 
      eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.
    intros. apply H2. apply unvv. apply vv in H5. eapply IHn with (H1 := H1); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.
    assumption.
    apply unvv. apply vv in H5. eapply IHn with (H1 := H1); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.*)
  - inversion C. subst. simpl in *. apply vv. rewrite val_type_unfold. 
    destruct vf. ev. split. eapply closed_upgrade_freef. eassumption. simpl. omega.
    split. eapply closed_upgrade_freef. eassumption. simpl. omega. 
    split. apply unvv. apply vv in H2. eapply IHn with (H1 := H1); try eassumption; try omega.
    apply unvv. apply vv in H3. eapply IHn with (H1 := H1); try eassumption; try omega.
    ev.    split. eapply closed_upgrade_freef. eassumption. simpl. omega.
    split. eapply closed_upgrade_freef. eassumption. simpl. omega.
    split. apply unvv. apply vv in H2. eapply IHn with (H1 := H1); try eassumption; try omega.
    apply unvv. apply vv in H3. eapply IHn with (H1 := H1); try eassumption; try omega.
  - inversion C. subst. simpl in *. apply vv. rewrite val_type_unfold. 
    destruct vf. ev. split. eapply closed_upgrade_freef. eassumption. simpl. omega.
    split. eapply closed_upgrade_freef. eassumption. simpl. omega. 
    split. apply unvv. apply vv in H2. eapply IHn with (H1 := H1); try eassumption; try omega.
    apply unvv. apply vv in H3. eapply IHn with (H1 := H1); try eassumption; try omega.
    ev.    split. eapply closed_upgrade_freef. eassumption. simpl. omega.
    split. eapply closed_upgrade_freef. eassumption. simpl. omega.
    split. apply unvv. apply vv in H2. eapply IHn with (H1 := H1); try eassumption; try omega.
    apply unvv. apply vv in H3. eapply IHn with (H1 := H1); try eassumption; try omega.
 *)
Qed.

 

(* used in wf_env_extend and in main theorem *)
Lemma valtp_extend: forall vx  df k H1 T1,
  val_type H1 [] T1 k (df k)  ->
  vtp (vx::H1) [] T1 k (df k) . 
  
Proof.
  intros. eapply valtp_extend_aux with (H1 := H1). eauto. simpl.
  apply valtp_closed in H. simpl in *. assumption. apply vv in H. assumption.
Qed.

(* used in wf_env_extend *)
Lemma valtp_shrink: forall vx df k H1 T1,
  val_type (vx::H1) [] T1 k (df k)  ->
  closed 0 0 (length H1) T1 ->                     
  vtp H1 [] T1 k (df k) .
Proof.
  intros. apply vv in H. eapply valtp_extend_aux. eauto. simpl. assumption.
  eassumption.
Qed.

Lemma valtp_shrinkM: forall vx df k H1 GH T1,
  val_type (vx::H1) GH T1 k (df k) ->
  closed 0 (length GH) (length H1) T1 ->                     
  vtp H1 GH T1 k (df k) .
Proof.
  intros. apply vv in H. eapply valtp_extend_aux. eauto. simpl. assumption.
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
  


Lemma valtp_splice_aux: forall n T H GH1 GH0 jj df k,
tsize_flat T < n -> closed 0 (length (GH1 ++ GH0)) (length H) T ->
(  
  vtp H (GH1 ++ GH0) T k (df k)  <-> 
  vtp H (GH1 ++ jj :: GH0) (splice (length GH0) T) k (df k) 
).
Proof.
  admit. (*
  induction n; intros ? ? ? ? ? ? ? Sz C. inversion Sz.
  destruct T; split; intros V; apply unvv in V; rewrite val_type_unfold in V;
    assert (length GH1 + S (length GH0) = S(length (GH1 ++ GH0))) as E;
    try rewrite app_length; try omega.
  - apply vv. rewrite val_type_unfold. destruct vf; apply V.
  - apply vv. rewrite val_type_unfold. destruct vf; apply V.
  - apply vv. rewrite val_type_unfold. destruct vf; apply V.
  - apply vv. rewrite val_type_unfold. destruct vf; apply V.
  - destruct vf. destruct i.
    + ev. apply vv. rewrite val_type_unfold. split.
    rewrite app_length. simpl. rewrite E. apply closed_splice. apply H0.
    split. rewrite app_length. simpl. rewrite E. apply closed_splice. apply H1.
    intros. specialize (H2 _ _ H3). 
    assert ((forall (vy : vl) (iy : sel),
      if pos iy
      then jj0 vy iy -> val_type H (GH1 ++ GH0) vy T1 iy
      else val_type H (GH1 ++ GH0) vy T1 iy -> jj0 vy iy)).
    { intros. destruct (pos iy) eqn : A. intros. specialize (H4 vy iy). rewrite A in H4. specialize (H4 H6).
      apply unvv. apply vv in H4. simpl in *. eapply IHn; try eassumption; try omega. 
      specialize (H4 vy iy).  rewrite A in H4. intros. apply H4. simpl in *. apply unvv. apply vv in H6.
      eapply IHn with (GH0 := GH0); try eassumption; try try omega. }
    specialize (H2 H6 H5). ev. exists x. split; try assumption. 
    assert (jj0 ::GH1 ++ jj :: GH0 = (jj0 :: GH1) ++ jj :: GH0) as Eq by apply app_comm_cons.
    unfold open in *. rewrite app_length in *. simpl. rewrite Eq. rewrite splice_open_permute. apply unvv. apply vv in H7. 
    eapply IHn with (GH0 := GH0); try eassumption. 
    simpl in Sz. rewrite <- open_preserves_size. omega.
    apply closed_open. simpl. eapply closed_upgrade_free.
    apply H1. rewrite app_length. omega.
    constructor. simpl. rewrite app_length. omega.
    + apply vv. rewrite val_type_unfold. simpl. ev. repeat split.
      rewrite app_length. simpl. rewrite E. apply closed_splice. assumption.
      rewrite app_length. simpl. rewrite E. apply closed_splice. assumption. assumption. assumption.

    + apply vv. rewrite val_type_unfold. simpl. ev. repeat split.
      rewrite app_length. simpl. rewrite E. apply closed_splice. assumption.
      rewrite app_length. simpl. rewrite E. apply closed_splice. assumption.
      simpl in H2. rewrite H2. reflexivity. assumption.
    
  - destruct vf. simpl in V. destruct i.
    + ev. apply vv. rewrite val_type_unfold. inversion C. subst.
    split. assumption. split. assumption. intros.
    specialize (H2 _ _ H3).
    assert ((forall (vy : vl) (iy : sel),
      if pos iy
      then
       jj0 vy iy ->
       val_type H (GH1 ++ jj :: GH0) vy (splice (length GH0) T1) iy
      else
       val_type H (GH1 ++ jj :: GH0) vy (splice (length GH0) T1) iy ->
       jj0 vy iy)).
    { intros. destruct (pos iy) eqn : A. intros. specialize (H4 vy iy). rewrite A in H4. specialize (H4 H6).
      apply unvv. apply vv in H4. simpl in *. eapply IHn with (GH0 := GH0); try eassumption; try omega.
      specialize (H4 vy iy). rewrite A in H4. intros. apply H4. apply unvv. apply vv in H6. simpl in *. eapply IHn;
      try eassumption; try omega. }
    specialize (H2 H6 H5). ev. exists x. split; try assumption. apply unvv. apply vv in H7.
    assert (jj0 ::GH1 ++ jj :: GH0 = (jj0 :: GH1) ++ jj :: GH0) as Eq by apply app_comm_cons.
    unfold open in *. rewrite app_length in *. simpl in *. rewrite splice_open_permute in H7. 
    rewrite app_comm_cons. eapply IHn with (GH0 := GH0); try eassumption. simpl in *. rewrite <- open_preserves_size. omega.
    apply closed_open. simpl. eapply closed_upgrade_free. eassumption. rewrite app_length. omega. constructor. simpl. rewrite app_length.
    omega.
    + apply vv. rewrite val_type_unfold. simpl. ev. inversion C. repeat split; assumption.
    + simpl in V. apply vv. rewrite val_type_unfold. simpl. ev. inversion C. repeat split; try assumption.
    

  - apply vv. rewrite val_type_unfold. destruct vf. simpl in *. destruct v.
    + assumption. 
    + destruct (indexr i0 (GH1 ++ GH0)) eqn : B; try solve by inversion. 
    destruct (le_lt_dec (length GH0) i0) eqn : A. 
    assert (indexr (i0 + 1) (GH1 ++ jj :: GH0) = Some v). apply indexr_hit_high. assumption. omega.
    rewrite H0. apply V. assert (indexr (i0) (GH1 ++ jj :: GH0) = Some v). apply indexr_hit_low. assumption. omega.
    rewrite H0. apply V.
    + inversion V.
    + simpl in *. destruct v; simpl; try apply V.
    destruct (indexr i0 (GH1 ++ GH0)) eqn : B; try solve by inversion. 
    destruct (le_lt_dec (length GH0) i0) eqn : A. 
    assert (indexr (i0 + 1) (GH1 ++ jj :: GH0) = Some v). apply indexr_hit_high. assumption. omega.
    rewrite H0. apply V. assert (indexr (i0) (GH1 ++ jj :: GH0) = Some v). apply indexr_hit_low. assumption. omega.
    rewrite H0. apply V.

  - apply vv. rewrite val_type_unfold. destruct vf; simpl in *. destruct v.
    + assumption.
    + destruct (le_lt_dec (length GH0) i0) eqn : A. inversion C. subst.  
    eapply indexr_has in H4. ev. assert (indexr (i0 + 1)(GH1 ++ jj:: GH0) = Some x). apply indexr_hit_high; assumption. 
    rewrite H0. rewrite H1 in V. assumption. 
    assert (i0 < length GH0) as H4 by omega. eapply indexr_has in H4. ev. assert (indexr (i0)(GH1 ++ GH0) = Some x).
    apply indexr_extend_mult. assumption. assert (indexr i0 (GH1 ++ jj :: GH0) = Some x). apply indexr_hit_low; assumption. 
    rewrite H1. rewrite H2 in V. assumption.
    + inversion V.
    + destruct v; try solve by inversion; try assumption.
    destruct (le_lt_dec (length GH0) i0) eqn : A. inversion C. subst. 
    eapply indexr_has in H4. ev. assert (indexr (i0 + 1)(GH1 ++ jj:: GH0) = Some x). apply indexr_hit_high; assumption. 
    rewrite H0. rewrite H1 in V. assumption. 
    assert (i0 < length GH0) as H4 by omega. eapply indexr_has in H4. ev. assert (indexr (i0)(GH1 ++ GH0) = Some x).
    apply indexr_extend_mult. assumption. assert (indexr i0 (GH1 ++ jj :: GH0) = Some x). apply indexr_hit_low; assumption. 
    rewrite H1. rewrite H2 in V. assumption.

  - inversion C. subst. apply vv. rewrite val_type_unfold. destruct vf. simpl in *. destruct i. inversion V. destruct b. 
    ev. split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    apply unvv. eapply IHn with (GH0 := GH0). simpl in *. omega. apply H6. apply vv. assumption.

    ev. split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    apply unvv. eapply IHn with (GH0 := GH0). simpl in *. omega. assumption. apply vv. assumption.

    simpl in *. destruct i. ev.
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    intros. specialize (H2 vy iy). destruct (pos iy) eqn : A. intros. assert (val_type H (GH1 ++ GH0) vy T1 iy).
    apply unvv. apply vv in H3. eapply IHn; try eassumption; try omega. specialize (H2 H4). apply vv in H2.
    apply unvv. apply vv in H4. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    intros. assert (val_type H (GH1 ++ GH0) vy T2 iy). apply unvv. apply vv in H3. eapply IHn; try eassumption; try omega. 
    specialize (H2 H4). apply vv in H2. apply unvv. apply vv in H4. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    
    destruct b; ev. split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    apply unvv. apply vv in H2. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    apply unvv. apply vv in H2. eapply IHn with (GH0 := GH0); try eassumption; try omega.
        
  - inversion C. subst. apply vv. rewrite val_type_unfold. destruct vf. simpl in *. destruct i. inversion V. destruct b. 
    split; try assumption. split; try assumption. ev. apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega.
    split; try assumption. split; try assumption. ev. apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega.
    simpl in *. destruct i. 
    split; try assumption. split; try assumption. ev. intros. specialize (H2 vy iy). destruct (pos iy) eqn : A.
    intros. assert (val_type H (GH1 ++ jj :: GH0) vy (splice (length GH0) T1) iy).
    apply unvv. apply vv in H3. eapply IHn with (GH0 := GH0); try eassumption; try omega. 
    specialize (H2 H4). apply vv in H2. apply unvv. eapply IHn; try eassumption; try omega.
    intros. assert (val_type H (GH1 ++ jj :: GH0) vy (splice (length GH0) T2) iy).
    apply unvv. apply vv in H3. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    specialize (H2 H4). apply vv in H2. apply unvv. eapply IHn; try eassumption; try omega.

    destruct b; ev. split; try assumption. split; try assumption. ev.
    apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega.
    split; try assumption. split; try assumption. ev.
    apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega.
  - admit. (*inversion C. subst. simpl in *. apply vv. rewrite val_type_unfold.
    destruct vf; ev. split. rewrite app_length in *. simpl in *. rewrite <- plus_n_Sm.
      eapply closed_splice. assumption.
    intros. assert (val_type H (jj0 :: GH1 ++ GH0) (vabs l t t0)
       (open (varH (length (GH1 ++ GH0))) T) i).
    apply H1. intros. specialize (H2 vy iy). destruct (pos iy). intros. specialize (H2 H5). 
    apply unvv. apply vv in H2. rewrite app_comm_cons. eapply IHn with (GH0 :=GH0); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      apply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.
      unfold open in *. rewrite app_length in *. simpl in *. rewrite splice_open_permute in H2. eassumption.
    intros. eapply H2. apply unvv. apply vv in H5. rewrite app_length in *. simpl in *. unfold open.
    rewrite splice_open_permute. rewrite app_comm_cons in *.
    eapply IHn with (GH0 := GH0); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      apply closed_open. simpl. eapply closed_upgrade_free. eassumption. rewrite app_length. omega.
      constructor. simpl. rewrite app_length. omega.
    assumption. apply unvv. apply vv in H5. unfold open in *. rewrite app_length in *.
    simpl in *. rewrite splice_open_permute. rewrite app_comm_cons in *. eapply IHn with (GH0 := GH0); try eassumption; try omega.
      rewrite <- open_preserves_size. omega.
      apply closed_open. simpl. eapply closed_upgrade_free.
      eassumption. rewrite app_length. simpl. omega.
      constructor. rewrite app_length. simpl. omega.
    split. rewrite app_length in *. simpl in *. rewrite <- plus_n_Sm.
      eapply closed_splice. assumption.
    intros. assert (val_type H (jj0 :: GH1 ++ GH0) (vty l t)
       (open (varH (length (GH1 ++ GH0))) T) i).
    apply H1. intros. specialize (H2 vy iy). destruct (pos iy). intros. specialize (H2 H5). 
    apply unvv. apply vv in H2. rewrite app_comm_cons. eapply IHn with (GH0 :=GH0); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      apply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.
      unfold open in *. rewrite app_length in *. simpl in *. rewrite splice_open_permute in H2. eassumption.
    intros. eapply H2. apply unvv. apply vv in H5. rewrite app_length in *. simpl in *. unfold open.
    rewrite splice_open_permute. rewrite app_comm_cons in *.
    eapply IHn with (GH0 := GH0); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      apply closed_open. simpl. eapply closed_upgrade_free. eassumption. rewrite app_length. omega.
      constructor. simpl. rewrite app_length. omega.
    assumption. apply unvv. apply vv in H5. unfold open in *. rewrite app_length in *.
    simpl in *. rewrite splice_open_permute. rewrite app_comm_cons in *. eapply IHn with (GH0 := GH0); try eassumption; try omega.
      rewrite <- open_preserves_size. omega.
      apply closed_open. simpl. eapply closed_upgrade_free.
      eassumption. rewrite app_length. simpl. omega.
      constructor. rewrite app_length. simpl. omega. *)
  - admit. (*inversion C. subst. simpl in *. apply vv. rewrite val_type_unfold.
    destruct vf; ev. split. rewrite app_length in *. simpl in *. assumption. 
    intros. assert (val_type H (jj0 :: GH1 ++ jj :: GH0) (vabs l t t0)
       (open (varH (length (GH1 ++ jj :: GH0))) (splice (length GH0) T)) i).
    apply H1. intros. specialize (H2 vy iy). destruct (pos iy). intros. specialize (H2 H5). 
    apply unvv. apply vv in H2. rewrite app_length. simpl. unfold open. rewrite splice_open_permute.
    rewrite app_comm_cons. eapply IHn with (GH0 := GH0); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      apply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.
      unfold open in *. rewrite app_length in *. simpl in *. assumption. 
    intros. eapply H2. apply unvv. apply vv in H5. rewrite app_length in *. simpl in *. unfold open.
    rewrite app_comm_cons in *.
    eapply IHn with (GH0 := GH0); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      apply closed_open. simpl. eapply closed_upgrade_free. eassumption. rewrite app_length. omega.
      constructor. simpl. rewrite app_length. omega.
      unfold open in H5. rewrite splice_open_permute in H5. eassumption.
    assumption. apply unvv. apply vv in H5. unfold open in *. rewrite app_length in *.
    simpl in *. rewrite splice_open_permute in H5. rewrite app_comm_cons in *.
    eapply IHn with (GH0 := GH0); try eassumption; try omega.
      rewrite <- open_preserves_size. omega.
      apply closed_open. simpl. eapply closed_upgrade_free.
      eassumption. rewrite app_length. simpl. omega.
      constructor. rewrite app_length. simpl. omega.
    split. rewrite app_length in *. simpl in *. assumption. 
    intros. assert (val_type H (jj0 :: GH1 ++ jj :: GH0) (vty l t)
       (open (varH (length (GH1 ++ jj :: GH0))) (splice (length GH0) T)) i).
    apply H1. intros. specialize (H2 vy iy). destruct (pos iy). intros. specialize (H2 H5). 
    apply unvv. apply vv in H2. rewrite app_length. simpl. unfold open. rewrite splice_open_permute.
    rewrite app_comm_cons. eapply IHn with (GH0 := GH0); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      apply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
      constructor. simpl. omega.
      unfold open in *. rewrite app_length in *. simpl in *. assumption. 
    intros. eapply H2. apply unvv. apply vv in H5. rewrite app_length in *. simpl in *. unfold open.
    rewrite app_comm_cons in *.
    eapply IHn with (GH0 := GH0); try eassumption; try omega.
      unfold open. rewrite <- open_preserves_size. omega.
      apply closed_open. simpl. eapply closed_upgrade_free. eassumption. rewrite app_length. omega.
      constructor. simpl. rewrite app_length. omega.
      unfold open in H5. rewrite splice_open_permute in H5. eassumption.
    assumption. apply unvv. apply vv in H5. unfold open in *. rewrite app_length in *.
    simpl in *. rewrite splice_open_permute in H5. rewrite app_comm_cons in *.
    eapply IHn with (GH0 := GH0); try eassumption; try omega.
      rewrite <- open_preserves_size. omega.
      apply closed_open. simpl. eapply closed_upgrade_free.
      eassumption. rewrite app_length. simpl. omega.
      constructor. rewrite app_length. simpl. omega.*)
  - inversion C. subst. simpl in *. apply vv. rewrite val_type_unfold. destruct vf; ev. 
    split. rewrite app_length in *. simpl. rewrite <- plus_n_Sm. eapply closed_splice. assumption.
    split. rewrite app_length in *. simpl. rewrite <- plus_n_Sm. eapply closed_splice. eassumption.
    split. apply unvv. apply vv in H2. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    apply unvv. apply vv in H3. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    split. rewrite app_length in *. simpl.  rewrite <- plus_n_Sm. eapply closed_splice. assumption.
    split. rewrite app_length in *. simpl. rewrite <- plus_n_Sm. eapply closed_splice. eassumption.
    split. apply unvv. apply vv in H2. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    apply unvv. apply vv in H3. eapply IHn with (GH0 := GH0); try eassumption; try omega.
  - inversion C. subst. simpl in *. apply vv. rewrite val_type_unfold. destruct vf; ev. 
    split. rewrite app_length in *. simpl. assumption. 
    split. rewrite app_length in *. simpl. assumption.
    split. apply unvv. apply vv in H2. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    apply unvv. apply vv in H3. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    split. rewrite app_length in *. simpl. assumption.
    split. rewrite app_length in *. simpl. assumption.
    split. apply unvv. apply vv in H2. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    apply unvv. apply vv in H3. eapply IHn with (GH0 := GH0); try eassumption; try omega.
*)
Qed.


(* used in valtp_widen *)
Lemma valtp_extendH: forall df k H1 GH T1 jj,
  val_type H1 GH T1 k (df k)  -> 
  vtp H1 (jj::GH) T1 k (df k) .
Proof.
  intros. assert (jj::GH = ([] ++ jj :: GH)). simpl. reflexivity. rewrite H0.
  assert (splice (length GH) T1 = T1). apply valtp_closed in H. eapply closed_splice_idem. eassumption. omega.
  rewrite <- H2. 
  eapply valtp_splice_aux with (GH0 := GH). eauto. simpl. apply valtp_closed in H. eapply closed_upgrade_free. eassumption. omega.
  simpl. apply vv in H. assumption.
Qed.

Lemma valtp_shrinkH: forall df k H1 GH T1 jj,
  val_type H1 (jj::GH) T1 k (df k) ->
  closed 0 (length GH) (length H1) T1 ->                     
  vtp H1 GH T1 k (df k) .
Proof. admit. (*
  intros. 
  assert (vtp H1 ([] ++ GH) vf T1 i <-> 
  vtp H1 ([] ++ jj :: GH) vf (splice (length GH) T1) i).
  eapply valtp_splice_aux. eauto. simpl. assumption. 
  apply H2. simpl. assert (splice (length GH) T1 = T1).
  eapply closed_splice_idem. eassumption. omega. apply vv in H.
  rewrite H3. assumption. *)
Qed.




(* used in invert_abs *)
Lemma vtp_subst1: forall venv jj d k T2,
  val_type venv [jj] (open (varH 0) T2) k (d k) ->
  closed 0 0 (length venv) T2 ->
  val_type venv [] T2 k (d k).
Proof.
  intros. assert (open (varH 0) T2 = T2). symmetry. unfold open. 
  eapply closed_no_open. eapply H0. rewrite H1 in H. 
  apply unvv. eapply valtp_shrinkH. simpl. eassumption. assumption.
Qed.

Lemma vtp_subst2_aux: forall n T venv jj x d m GH j k,
  tsize_flat T < n ->
  closed j (length GH) (length venv) T -> k < j ->
  indexr x venv = Some jj ->
  (vtp venv (GH ++ [jj]) (open_rec k (varH 0) (splice 0 T)) m (d m) <->
   vtp venv GH (open_rec k (varF x) T) m (d m)).
Proof.
  admit. (* 
  induction n; intros ? ? ? ? ? ? ? ? ? Sz Cz Bd Id. inversion Sz.
  destruct T; split; intros V; apply unvv in V; rewrite val_type_unfold in V.
  - unfold open. simpl in *. apply vv. rewrite val_type_unfold. destruct v; apply V.
  - unfold open. simpl in *. apply vv. rewrite val_type_unfold. destruct v; apply V.
  - unfold open. simpl in *. apply vv. rewrite val_type_unfold. destruct v; apply V.
  - unfold open. simpl in *. apply vv. rewrite val_type_unfold. destruct v; apply V.
  - inversion Cz. subst. 
    unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. destruct v.
    destruct i.
    + ev. split. {rewrite app_length in *.  simpl in *. eapply splice_retreat4. 
    eassumption. constructor. eapply indexr_max. eassumption. }
    split. { rewrite app_length in *. simpl in *. eapply splice_retreat4.
    eassumption. constructor. eapply indexr_max. eassumption. }
    
    intros. specialize (H1 _ _ H2). assert ((forall (vy : vl) (iy : sel),
      if pos iy
      then
       jj0 vy iy ->
       val_type venv0 (GH ++ [jj]) vy (open_rec k (varH 0) (splice 0 T1)) iy
      else
       val_type venv0 (GH ++ [jj]) vy (open_rec k (varH 0) (splice 0 T1)) iy ->
       jj0 vy iy)).
    { intros. destruct (pos  iy) eqn : A. specialize (H3 vy iy). rewrite A in H3. intros. 
      specialize (H3 H7). apply unvv. apply vv in H3. eapply IHn; try eassumption; try omega.
      specialize (H3 vy iy). rewrite A in H3. intros. apply H3. apply unvv. apply vv in H7.
      eapply IHn; try eassumption; try omega. }
    specialize (H1 H7 H6). ev. exists x0. split. assumption. apply unvv. apply vv in H8.
    assert (jj0 :: GH ++ [jj] = (jj0 :: GH) ++ [jj]) as Eq.
    apply app_comm_cons. rewrite Eq in H8.
    unfold open. 
    erewrite open_permute in H8. erewrite open_permute.  
    assert ((open_rec 0 (varH (length (GH ++ [jj]))) (splice 0 T2)) =
             splice 0 (open_rec 0 (varH (length GH)) T2)). {
    rewrite app_length. simpl.
    assert ((length GH) = (length GH) + 0). omega. rewrite H9.
    apply (splice_open_permute0 0 T2 (length GH) 0).
    }
    rewrite H9 in H8.
    eapply IHn with (GH := (jj0::GH)). erewrite <- open_preserves_size. omega.
    assert (closed (S j) (S (length GH)) (length venv0) T2). eapply closed_upgrade_free.
    eassumption. omega. eapply closed_open2. eassumption. constructor. simpl. omega. omega. 
    eapply Id. apply H8. constructor. eauto. constructor. eauto. omega.
    constructor. eauto. constructor. eauto. omega. 
    + rewrite app_length in V. simpl in V. ev. repeat split.
      eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption.
      eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption.
      eauto. eauto. 
    + rewrite app_length in V. simpl in V. ev. repeat split.
      eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption.
      eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption.
      eauto. eauto. 
  
  
  - inversion Cz. subst. 
    unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. destruct v.
    destruct i.
    + ev. split. { rewrite app_length. simpl. eapply splice_retreat5. constructor. omega. 
    eassumption. }
    split. { rewrite app_length. simpl. eapply splice_retreat5. constructor.
    omega. eassumption. }
    intros. specialize (H1 _ _ H2). assert ((forall (vy : vl) (iy : sel),
      if pos iy
      then jj0 vy iy -> val_type venv0 GH vy (open_rec k (varF x) T1) iy
      else val_type venv0 GH vy (open_rec k (varF x) T1) iy -> jj0 vy iy)).
    { intros. destruct (pos  iy) eqn : A. specialize (H3 vy iy). rewrite A in H3. intros. 
      specialize (H3 H7). apply unvv. apply vv in H3. eapply IHn; try eassumption; try omega.
      specialize (H3 vy iy). rewrite A in H3. intros. apply H3. apply unvv. apply vv in H7.
      eapply IHn; try eassumption; try omega. }
    specialize (H1 H7 H6). ev. exists x0. split. assumption. apply unvv. apply vv in H8.
    assert (jj0 :: GH ++ [jj] = (jj0 :: GH) ++ [jj]) as Eq.
    apply app_comm_cons. rewrite Eq. unfold open in *. 
    erewrite open_permute in H8. erewrite open_permute.  
    assert ((open_rec 0 (varH (length (GH ++ [jj]))) (splice 0 T2)) =
             splice 0 (open_rec 0 (varH (length GH)) T2)). {
    rewrite app_length. simpl.
    assert ((length GH) = (length GH) + 0). omega. rewrite H9.
    apply (splice_open_permute0 0 T2 (length GH) 0).
    }
    rewrite H9.
    eapply IHn with (GH := (jj0::GH)). erewrite <- open_preserves_size. omega.
    assert (closed (S j) (S (length GH)) (length venv0) T2). eapply closed_upgrade_free.
    eassumption. omega. eapply closed_open2. eassumption. constructor. simpl. omega. omega. 
    eapply Id. apply H8. constructor. eauto. constructor. eauto. omega.
    constructor. eauto. constructor. eauto. omega. 
    + ev. rewrite app_length. simpl. repeat split.
      eapply splice_retreat5. constructor. omega. eauto.
      eapply splice_retreat5. constructor. omega. eauto.
      eauto. eauto. 
    + ev. rewrite app_length. simpl. repeat split.
      eapply splice_retreat5. constructor. omega. eauto.
      eapply splice_retreat5. constructor. omega. eauto.
      eauto. eauto. 

  - unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. 
    destruct v; destruct v0; simpl in *; try apply V.
    + assert (indexr (i0 + 1) (GH ++ [jj]) = indexr i0 GH). {
    apply indexr_extend_end. }   
    rewrite H in V. apply V.
    + destruct (beq_nat k i0) eqn : A. 
    simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). 
    apply indexr_hit01.
    rewrite H in V. rewrite Id. apply V. inversion V.
    + assert (indexr (i0 + 1) (GH ++ [jj]) = indexr i0 GH). apply indexr_extend_end.
    rewrite H in V. apply V.
    + destruct (beq_nat k i0) eqn : A. 
    simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). apply indexr_hit01.
    rewrite H in V. rewrite Id. apply V. inversion V.

  - unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. 
    destruct v; destruct v0; simpl in *; try apply V.
    assert (indexr (i0 + 1) (GH ++ [jj]) = indexr i0 GH). apply indexr_extend_end.
    rewrite H. apply V.
    destruct (beq_nat k i0) eqn : A. 
    simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). apply indexr_hit01.
    rewrite H. rewrite Id in V. apply V. inversion V.
    assert (indexr (i0 + 1) (GH ++ [jj]) = indexr i0 GH). apply indexr_extend_end.
    rewrite H. apply V.
    destruct (beq_nat k i0) eqn : A. 
    simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). apply indexr_hit01.
    rewrite H. rewrite Id in V. apply V. inversion V.

  - inversion Cz. subst. 
    unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. destruct i. 
    + destruct v; try solve by inversion. ev. rewrite app_length in *. split. { eapply splice_retreat4.
      simpl in *. eassumption. constructor. apply indexr_max in Id. omega. } split. { eapply splice_retreat4.
      simpl in *. eassumption. constructor. apply indexr_max in Id. omega. } 
    intros. specialize (H1 vy iy). destruct (pos iy). intros. assert (
    val_type venv0 (GH ++ [jj]) vy (open_rec k (varH 0) (splice 0 T1)) iy).
    apply vv in H2. apply unvv. eapply IHn; try eassumption; try omega. specialize (H1 H3). apply vv in H1.
    apply unvv. eapply IHn; try eassumption; try omega.
    intros. assert (
    val_type venv0 (GH ++ [jj]) vy (open_rec k (varH 0) (splice 0 T2)) iy).
    apply vv in H2. apply unvv. eapply IHn; try eassumption; try omega. specialize (H1 H3). apply vv in H1.
    apply unvv. eapply IHn; try eassumption; try omega.

    + rewrite app_length in *. destruct v. destruct b. ev. split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max.
    eassumption. split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max.
    eassumption. 
    apply vv in H1. apply unvv. eapply IHn; try eassumption; try omega.
    ev. split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max.
    eassumption. split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max.
    eassumption. 
    apply vv in H1. apply unvv. eapply IHn; try eassumption; try omega.
    destruct b; ev. split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption.
    split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption.
    apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.
    split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption.
    split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption.
    apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.

  - inversion Cz. subst. 
    unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. destruct i. 
    + destruct v; try solve by inversion. ev. rewrite app_length in *. split. { eapply splice_retreat5.
      constructor. omega. eassumption. }
    split. eapply splice_retreat5. constructor. omega. eassumption.
    intros. specialize (H1 vy iy). destruct (pos iy). intros. assert (val_type venv0 GH vy (open_rec k (varF x) T1) iy).
    apply vv in H2. apply unvv. eapply IHn; try eassumption; try omega. specialize (H1 H3). apply vv in H1.
    apply unvv. eapply IHn; try eassumption; try omega.
    intros. assert (val_type venv0 GH vy (open_rec k (varF x) T2) iy).
    apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega. specialize (H1 H3). apply vv in H1.
    apply unvv. eapply IHn; try eassumption; try omega.

    + rewrite app_length. simpl in *. destruct v. ev. destruct b; ev. 
    split. eapply splice_retreat5. constructor. omega. eassumption.
    split. eapply splice_retreat5. constructor. omega. eassumption.
    apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.
    ev. split. eapply splice_retreat5. constructor. omega. eassumption.
    split. eapply splice_retreat5. constructor. omega. eassumption.
    apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.
    destruct b; ev. split. eapply splice_retreat5. constructor. omega. eassumption.
    split. eapply splice_retreat5. constructor. omega. eassumption.
    apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.
    split. eapply splice_retreat5. constructor. omega. eassumption.
    split. eapply splice_retreat5. constructor. omega. eassumption.
    apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.

  - admit. (*inversion Cz. subst. simpl in *. rewrite app_length in *. apply vv. rewrite val_type_unfold. destruct v; ev.
    split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption. 
    intros. assert (val_type venv0 (jj0 :: GH ++ [jj]) (vabs l t t0)
       (open (varH (length GH + length [jj]))
          (open_rec (S k) (varH 0) (splice 0 T))) i). apply H0.
    intros. specialize (H1 vy iy). destruct (pos iy). intros. specialize (H1 H4).
    apply unvv. apply vv in H1. unfold open. erewrite open_permute. simpl.
    assert ((length GH) = (length GH) + 0) as W. omega. rewrite W. rewrite splice_open_permute0.
    rewrite app_comm_cons. eapply IHn; try eassumption; try omega.
      rewrite<- open_preserves_size. omega.
      eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. 
      constructor. simpl. omega. omega. 
      erewrite open_permute. simpl. unfold open in *. rewrite plus_0_r.  assumption.
      econstructor. eauto. econstructor. eauto. omega. econstructor. eauto. econstructor. eauto. omega.
    intros. apply H1. apply unvv. apply vv in H4. unfold open. erewrite open_permute.
    eapply IHn; try eassumption; try omega. 
      erewrite <-open_preserves_size. omega.
      eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega.  
      constructor. simpl. omega. omega. 
      unfold open in H4. erewrite open_permute in H4. simpl in H4. 
      assert ((length GH + 1) = (length GH + 0 + 1) ). rewrite plus_0_r. reflexivity.
      rewrite H5 in H4. rewrite splice_open_permute0 in H4. rewrite plus_0_r in H4. assumption.
      econstructor. eauto. econstructor. eauto. omega. econstructor. eauto. econstructor. eauto. omega.
    assumption. apply unvv. apply vv in H4. unfold open in *. erewrite open_permute.  eapply IHn; try eassumption.
      rewrite <- open_preserves_size. omega.
      eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. 
      constructor. simpl. omega. omega. erewrite open_permute in H4. simpl in H4. 
      assert ((length GH + 1) = (length GH + 0 + 1) ). rewrite plus_0_r. reflexivity.
      rewrite H5 in H4. rewrite splice_open_permute0 in H4. simpl. rewrite plus_0_r in H4. assumption.
      econstructor. eauto. econstructor. eauto. omega.
      econstructor. eauto. econstructor. eauto. omega. 
    split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption. 
    intros. assert (val_type venv0 (jj0 :: GH ++ [jj]) (vty l t)
       (open (varH (length GH + length [jj]))
          (open_rec (S k) (varH 0) (splice 0 T))) i). apply H0.
    intros. specialize (H1 vy iy). destruct (pos iy). intros. specialize (H1 H4).
    apply unvv. apply vv in H1. unfold open. erewrite open_permute. simpl.
    assert ((length GH) = (length GH) + 0) as W. omega. rewrite W. rewrite splice_open_permute0.
    rewrite app_comm_cons. eapply IHn; try eassumption; try omega.
      rewrite<- open_preserves_size. omega.
      eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. 
      constructor. simpl. omega. omega. 
      erewrite open_permute. simpl. unfold open in *. rewrite plus_0_r.  assumption.
      econstructor. eauto. econstructor. eauto. omega. econstructor. eauto. econstructor. eauto. omega.
    intros. apply H1. apply unvv. apply vv in H4. unfold open. erewrite open_permute.
    eapply IHn; try eassumption; try omega. 
      erewrite <-open_preserves_size. omega.
      eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega.  
      constructor. simpl. omega. omega. 
      unfold open in H4. erewrite open_permute in H4. simpl in H4. 
      assert ((length GH + 1) = (length GH + 0 + 1) ). rewrite plus_0_r. reflexivity.
      rewrite H5 in H4. rewrite splice_open_permute0 in H4. rewrite plus_0_r in H4. assumption.
      econstructor. eauto. econstructor. eauto. omega. econstructor. eauto. econstructor. eauto. omega.
    assumption. apply unvv. apply vv in H4. unfold open in *. erewrite open_permute.  eapply IHn; try eassumption.
      rewrite <- open_preserves_size. omega.
      eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. 
      constructor. simpl. omega. omega. erewrite open_permute in H4. simpl in H4. 
      assert ((length GH + 1) = (length GH + 0 + 1) ). rewrite plus_0_r. reflexivity.
      rewrite H5 in H4. rewrite splice_open_permute0 in H4. simpl. rewrite plus_0_r in H4. assumption.
      econstructor. eauto. econstructor. eauto. omega.
      econstructor. eauto. econstructor. eauto. omega.*)
  - admit. (*inversion Cz. subst. simpl in *. apply vv. rewrite val_type_unfold. destruct v; ev.
    split. rewrite app_length. simpl. eapply splice_retreat5. constructor. omega. eassumption.
    intros. assert (val_type venv0 (jj0 :: GH) (vabs l t t0)
       (open (varH (length GH)) (open_rec (S k) (varF x) T)) i). apply H0.
    intros. specialize (H1 vy iy). destruct (pos iy). intros. specialize (H1 H4). apply unvv. apply vv in H1.
    unfold open. erewrite open_permute. eapply IHn; try eassumption.
      rewrite <- open_preserves_size. omega.
      eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. 
      constructor. simpl. omega. omega. simpl. 
      unfold open in H1. erewrite open_permute in H1. rewrite app_length in H1. simpl in H1. 
      assert (length GH +1 = (length GH + 0 + 1)). rewrite plus_0_r. reflexivity. 
      rewrite H5 in H1. rewrite splice_open_permute0 in H1. rewrite plus_0_r in H1. assumption.
      econstructor. eauto. econstructor. eauto. omega.
      econstructor. eauto. econstructor. eauto. omega.
    intros. apply H1. apply unvv. apply vv in H4. unfold open. 
    erewrite open_permute. rewrite app_length. simpl. assert ((length GH + 1) = (length GH + 0+ 1)).
    rewrite plus_0_r. reflexivity. rewrite H5. rewrite splice_open_permute0. 
    rewrite app_comm_cons. eapply IHn; try eassumption.
      rewrite <- open_preserves_size. omega.
      eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. 
      constructor. simpl. omega. omega. unfold open in H4. erewrite open_permute in H4.
      rewrite plus_0_r. assumption.
      econstructor. eauto. econstructor. eauto. omega.
      econstructor. eauto. econstructor. eauto. omega.
    assumption. apply unvv. apply vv in H4. unfold open in *. rewrite app_length in *.
    simpl in *. erewrite open_permute. assert ((length GH + 1) = (length GH + 0 + 1)).
    rewrite plus_0_r. reflexivity. rewrite H5. rewrite splice_open_permute0. rewrite app_comm_cons. 
    eapply IHn; try eassumption. 
      rewrite <- open_preserves_size. omega.
      eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. 
      constructor. simpl. omega. omega. unfold open in H4. erewrite open_permute in H4.
      rewrite plus_0_r. assumption.
      econstructor. eauto. econstructor. eauto. omega.
      econstructor. eauto. econstructor. eauto. omega.
    split. rewrite app_length. simpl. eapply splice_retreat5. constructor. omega. eassumption.
    intros. assert (val_type venv0 (jj0 :: GH) (vty l t)
       (open (varH (length GH)) (open_rec (S k) (varF x) T)) i). apply H0.
    intros. specialize (H1 vy iy). destruct (pos iy). intros. specialize (H1 H4). apply unvv. apply vv in H1.
    unfold open. erewrite open_permute. eapply IHn; try eassumption.
      rewrite <- open_preserves_size. omega.
      eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. 
      constructor. simpl. omega. omega. simpl. 
      unfold open in H1. erewrite open_permute in H1. rewrite app_length in H1. simpl in H1. 
      assert (length GH +1 = (length GH + 0 + 1)). rewrite plus_0_r. reflexivity. 
      rewrite H5 in H1. rewrite splice_open_permute0 in H1. rewrite plus_0_r in H1. assumption.
      econstructor. eauto. econstructor. eauto. omega.
      econstructor. eauto. econstructor. eauto. omega.
    intros. apply H1. apply unvv. apply vv in H4. unfold open. 
    erewrite open_permute. rewrite app_length. simpl. assert ((length GH + 1) = (length GH + 0+ 1)).
    rewrite plus_0_r. reflexivity. rewrite H5. rewrite splice_open_permute0. 
    rewrite app_comm_cons. eapply IHn; try eassumption.
      rewrite <- open_preserves_size. omega.
      eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. 
      constructor. simpl. omega. omega. unfold open in H4. erewrite open_permute in H4.
      rewrite plus_0_r. assumption.
      econstructor. eauto. econstructor. eauto. omega.
      econstructor. eauto. econstructor. eauto. omega.
    assumption. apply unvv. apply vv in H4. unfold open in *. rewrite app_length in *.
    simpl in *. erewrite open_permute. assert ((length GH + 1) = (length GH + 0 + 1)).
    rewrite plus_0_r. reflexivity. rewrite H5. rewrite splice_open_permute0. rewrite app_comm_cons. 
    eapply IHn; try eassumption. 
      rewrite <- open_preserves_size. omega.
      eapply closed_open2. simpl. eapply closed_upgrade_free. eassumption. omega. 
      constructor. simpl. omega. omega. unfold open in H4. erewrite open_permute in H4.
      rewrite plus_0_r. assumption.
      econstructor. eauto. econstructor. eauto. omega.
      econstructor. eauto. econstructor. eauto. omega.*)
  - inversion Cz. subst. rewrite app_length in *. simpl in *. apply vv. rewrite val_type_unfold. destruct v; ev.
    split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption.
    split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption.
    split. apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.
    apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega.
    split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption.
    split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max. eassumption.
    split. apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.
    apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega.
  - inversion Cz. subst. simpl in *. apply vv. rewrite val_type_unfold. destruct v; ev.
    split. rewrite app_length. simpl. eapply splice_retreat5. constructor. omega. eassumption.
    split. rewrite app_length. simpl. eapply splice_retreat5. constructor. omega. eassumption.
    split. apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.
    apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega.

    split. rewrite app_length. simpl. eapply splice_retreat5. constructor. omega. eassumption.
    split. rewrite app_length. simpl. eapply splice_retreat5. constructor. omega. eassumption.
    split. apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.
    apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega.


Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0.
(*apply 0. apply 0. apply 0. apply 0.

apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0.*)*)
Qed.  


Lemma vtp_subst: forall T venv jj x d k GH,
  closed 1 (length GH) (length venv) T -> 
  indexr x venv = Some jj ->
  (vtp venv (GH ++ [jj]) (open (varH 0) (splice 0 T)) k (d k) <->
   vtp venv GH (open (varF x) T) k (d k)).
Proof. intros. eapply vtp_subst2_aux. eauto. eassumption. omega. assumption. Qed.


(* used in invert_dabs *)
Lemma vtp_subst2: forall venv jj x d k  T2,
  closed 1 0 (length venv) T2 ->
  val_type venv [jj] (open (varH 0) T2) k (d k) ->
  indexr x venv = Some jj ->
  val_type venv [] (open (varF x) T2) k (d k).
Proof.
  intros. apply vv in H0. assert ([jj] = ([] ++ [jj])). simpl. reflexivity.
  rewrite H2 in H0. assert (splice 0 T2 = T2). eapply closed_splice_idem.
  eassumption. omega. rewrite <- H3 in H0. eapply vtp_subst in H0. apply unvv. eassumption.
  simpl. assumption. assumption.
Qed.

(* used in valtp_bounds *)
Lemma vtp_subst2_general: forall venv jj x T2 d k,
  closed 1 0 (length venv) T2 ->
  indexr x venv = Some jj ->
  ( vtp venv [jj] (open (varH 0) T2) k (d k) <->
    vtp venv [] (open (varF x) T2) k (d k)).
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
Lemma vtp_subst3: forall venv jj T2 d k,
  closed 1 0 (length venv) T2 ->
  val_type (jj::venv) [] (open (varF (length venv)) T2) k (d k) ->
  val_type venv [jj] (open (varH 0) T2) k (d k).
Proof.
  admit. (*
  intros. apply unvv. assert (splice 0 T2 = T2) as EE. eapply closed_splice_idem. eassumption. omega.
  assert (vtp (jj::venv0) ([] ++ [jj]) v (open (varH 0) (splice 0 T2)) nil).
  assert (indexr (length venv0) (jj :: venv0) = Some jj). simpl. 
    replace (beq_nat (length venv0) (length venv0) ) with true. reflexivity. 
    apply beq_nat_refl. 
  eapply vtp_subst. simpl. eapply closed_upgrade_freef. eassumption. omega. eassumption.
  apply vv. assumption. 
  simpl in *. rewrite EE in H1. eapply valtp_shrinkM. apply unvv. eassumption.
  apply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
  constructor. simpl. omega. *)
Qed.

Lemma open_preserves_size2: forall T x j,
  tsize_flat T = tsize_flat (open_rec j (varF x) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
  - destruct v; simpl; destruct (beq_nat j i); eauto.
Qed.

Lemma valty_subst4: forall G T1 jj d k,
  closed 1 0 (length G) T1 ->
  (vtp G [jj] (open (varH 0) T1) k (d k) <->
   vtp (jj :: G) [] (open (varF (length G)) T1) k (d k)). 
Proof.
  admit. (* intros. split. 
  Case "->". intros. assert (vtp (jj :: G) [jj] vp (open (varH 0) T1) iy).
    { eapply valtp_extend_aux with (H1 := G). eauto. 
      simpl. eapply closed_open. simpl. eapply closed_inc_mult. eassumption. omega. omega.
      omega. constructor. omega. assumption. }
    assert (vtp (jj :: G) [] vp (open (varF (length G)) T1) iy).
    { eapply vtp_subst2_general. simpl. eapply closed_upgrade_freef. eassumption. omega.
      simpl. replace (beq_nat (length G) (length G)) with true. reflexivity. apply beq_nat_refl. 
      assumption. } assumption.
  Case "<-". intros. assert (vtp (jj :: G) [jj] vp (open (varF (length G)) T1) iy).
    { eapply valtp_extendH. apply unvv. assumption. }
    assert (vtp (jj :: G) [jj] vp (open (varH 0) T1) iy).
    { eapply vtp_subst2_general with (x := length G). simpl. eapply closed_upgrade_freef. eassumption. omega.
      simpl. replace (beq_nat (length G) (length G)) with true. reflexivity. apply beq_nat_refl. 
      eassumption. }
    eapply valtp_shrinkM. apply unvv. eassumption. simpl. eapply closed_open. simpl. eapply closed_upgrade_free.
    eassumption. omega. constructor. omega.*)
Qed.
   



(* ### Relating Value Typing and Subtyping ### *)

Lemma valtp_widen_aux: forall G1 GH1 T1 T2,
  stp G1 GH1 T1 T2 ->
  forall (H: list vseta) GH HH STO,
    length G1 = length H ->
    (forall x TX, indexr x G1 = Some TX ->
                  exists lx vx dx,
                    indexr lx STO = Some (vx,dx) /\
                    indexr x HH = Some vx /\
                    indexr x H = Some dx /\
                    vtp H GH TX STO lx) ->
    length GH1 = length GH ->
    (forall x TX, indexr x GH1 = Some TX ->
                   exists lx vx dx,
                     indexr lx STO = Some (vx,dx) /\
                     indexr x HH = Some vx /\
                     indexr x GH = Some dx /\
                     vtp H GH TX STO lx) ->
  (forall vf, 
     vtp H GH T1 STO vf -> vtp H GH T2 STO vf).
Proof.
  
  intros ? ? ? ? stp. 
  induction stp; intros G GHX HH STO LG RG LGHX RGHX vf V0. 

  
  - Case "Top".
    admit. (* eapply vv. rewrite val_type_unfold. destruct vf; reflexivity. *)
  - Case "Bot".
    admit. (* rewrite val_type_unfold in V0. destruct vf; inversion V0. *)
  - Case "mem".
    admit. (*subst. 
    rewrite val_type_unfold in V0. 
    eapply vv. rewrite val_type_unfold.
    destruct vf; destruct kf; try destruct b; try solve by inversion; ev.  
    + rewrite <-LG. rewrite <-LGHX. split.
      apply stp_closed1 in stp2. assumption. split. apply stp_closed2 in stp1. assumption.
      trivial.
    + rewrite <-LG. rewrite <-LGHX. split.
      apply stp_closed1 in stp2. assumption. split. apply stp_closed2 in stp1. assumption.
      intros. specialize (H1 dy vy). ev. split.
      intros. eapply H1. eapply unvv. eapply IHstp2; assumption.
      intros. eapply unvv. eapply IHstp1; try assumption. eapply H2. assumption. *)
   
  - Case "Sel1".
    subst. specialize (IHstp _ _ _ _ LG RG LGHX RGHX).
    specialize (RG _ _ H). ev.
    eapply unvv in V0. rewrite val_type_unfold in V0.
    destruct (indexr vf STO) as [[[|]]|]; try contradiction; eauto.
    rewrite H3 in V0. 

    specialize (IHstp _ H4).
    eapply unvv in IHstp.
    rewrite val_type_unfold in IHstp.
    destruct (indexr x0 STO) as [[[|]]|]; try contradiction. ev.
    inversion H1. subst x1 x2. specialize (H7 [] vf). ev. simpl in H7.
    (* IN THE CURRENT MODEL, WE'D HAVE TO SHOW vf <> x0 !!! *)

    admit.
    admit.


  - Case "Sel2".
    subst. specialize (IHstp _ _ _ _ LG RG LGHX RGHX).
    specialize (RG _ _ H). ev. 
    eapply vv. rewrite val_type_unfold.
    destruct (indexr vf STO) as [[[|]]|]; try contradiction; eauto.
    rewrite H3. 
    
    specialize (IHstp _ H4).
    eapply unvv in IHstp.
    rewrite val_type_unfold in IHstp.
    destruct (indexr x0 STO) as [[[|]]|]; try contradiction. ev.
    inversion H1. subst x1 x2. specialize (H7 [] vf). ev. simpl in H7.
    (* IN THE CURRENT MODEL, WE'D HAVE TO SHOW vf <> x0 !!! *)

    admit.
    admit.
    admit. 

  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
(*    
  - Case "selx".
    eapply vv. eapply V0.

  (* exactly the same as sel1/sel2, modulo RG/RGHX *)
  - Case "Sel1".
    admit.
  - Case "Sel2".
    admit. 
    
  - Case "selax".
    eapply vv. eapply V0.


  - Case "bind1". admit.
  - Case "bind2". admit.
  - Case "bindx".
    admit. 
    

  - Case "And11".
    rewrite val_type_unfold in V0.
    destruct vf; ev; eapply IHstp; assumption. 
    
  - Case "And12".
    rewrite val_type_unfold in V0.
    destruct vf; ev; eapply IHstp; assumption. 
    
  - Case "And2".
    eapply vv. rewrite val_type_unfold.
    destruct vf.
    split; eapply unvv. eapply IHstp1; assumption. eapply IHstp2; assumption.
    split; eapply unvv. eapply IHstp1; assumption. eapply IHstp2; assumption. 
    
  - Case "Fun".
    subst. 
    rewrite val_type_unfold in V0.
    assert (val_type G GHX (TAll T3 T4) kf (df kf) vf). rewrite val_type_unfold.
    subst. destruct vf; try solve [inversion V0].
    destruct V0 as [? [? LR]].
    assert (closed 0 (length GHX) (length G) T3). rewrite <-LG. rewrite <-LGHX. eapply stp_closed in stp1. eapply stp1.
    assert (closed 1 (length GHX) (length G) T4). rewrite <-LG. rewrite <-LGHX. eapply H1.
    split. eauto. split. eauto. 
    intros jj vx VX0. 

    specialize (IHstp1 _ _ LG RG LGHX RGHX).
    
    assert (exists kx, val_type G GHX T1 kx (jj kx) vx) as VX1. {
      intros. specialize (IHstp1 kx jj vx). eapply unvv. eapply IHstp1. eapply VX0. }

    destruct (LR jj vx VX1) as [jj2 [v [TE VT]]].

    exists jj2. exists v. split. eapply TE. intros. eapply unvv.

    (* now deal with function result! *)
    rewrite <-LGHX. rewrite <-LGHX in VT.

    (* broaden goal so that we can apply stp2 *)
    eapply IHstp2. eapply LG.

    (* extend RG *)
    intros ? ? IX. destruct (RG _ _ IX) as [vx0 [jj0 [IX1 FA]]].
    exists vx0. exists jj0. split. assumption. 
    intros. eapply valtp_extendH. eapply unvv. eapply FA. simpl. rewrite LGHX. reflexivity.

    (* extend LGHX *)
    (* simpl. rewrite LGHX. reflexivity. *)

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
        intros. eapply valtp_extendH. eapply unvv. eapply H6. 
    }
    eapply VT. eapply vv. eapply H.

  - Case "trans".
    specialize (IHstp1 _ _ LG RG LGHX RGHX kf df vf).
    specialize (IHstp2 _ _ LG RG LGHX RGHX kf df vf).
    eapply IHstp2. eapply unvv. eapply IHstp1. eapply V0.*)
Qed.


Lemma valtp_widen: forall kf df GH H G1 T1 T2,
  val_type GH [] T1 df kf ->
  stp G1 [] T1 T2 ->
  R_env H GH G1 df ->
  vtp GH [] T2 df kf.
Proof.
  admit. (*
  intros. destruct H2 as [L1 [L2 A]]. symmetry in L2. 
  eapply valtp_widen_aux; try eassumption; try reflexivity.

  intros. specialize (A _ _ H2). ev.
  eexists. eexists. split. eassumption. admit. eassumption.

  intros. inversion H2. *)
Qed.


Lemma wf_env_extend: forall vx lx jj STO G1 R1 H1 T1,
  R_env H1 R1 G1 STO ->
  val_type (jj::R1) [] T1 STO lx  ->
  R_env (vx::H1) (jj ::R1) (T1::G1) STO.
Proof.
  admit. (*
  intros. unfold R_env in *. destruct H as [L1 [L2 U]].
  split. simpl. rewrite L1. reflexivity.
  split. simpl. rewrite L2. reflexivity.
  intros. simpl in H. case_eq (beq_nat x (length G1)); intros E; rewrite E in H.
  - inversion H. subst T1. exists jj. exists vx.
    split. simpl. rewrite <-L1 in E. rewrite E. reflexivity.
    split. simpl. rewrite <-L2 in E. rewrite E. reflexivity.
    intros. eapply vv. eapply H0. 
  - destruct (U x TX H) as [jj0 [vy0 [EV [VY IR]]]]. 
    exists jj0. exists vy0.
    split. simpl. rewrite <-L1 in E. rewrite E. assumption.
    split. simpl. rewrite <-L2 in E. rewrite E. assumption.
    intros. eapply valtp_extend. eapply unvv. eapply IR. *)
Qed.

Lemma wf_env_extend0: forall vx lx jj STO G1 R1 H1 T1,
  R_env H1 R1 G1 STO ->
  val_type R1 [] T1 STO lx ->
  R_env (vx::H1) (jj::R1) (T1::G1) STO.
Proof.
  admit. (*
  intros.
  assert (forall n, val_type (jj::R1) [] T1 n (jj n) vx) as V0.
  intro. eapply unvv. eapply valtp_extend. eapply H0.
  eapply wf_env_extend; assumption. *)
Qed.



(* ### Inversion Lemmas ### *)





  
Theorem full_total_safety : forall e tenv T,
  has_type tenv e T -> forall venv renv f (m:nat), R_env venv renv tenv f ->
  exists f' l v,
    tevaln venv e v /\
    val_type renv [] T f' l.
Proof.
  intros ? ? ? W. 
  induction W; intros ? ? ? ? WFE.

  - Case "Var".
    unfold R_env in WFE. ev. destruct (H3 _ _ H) as [l [v ?]]. ev.
        
    exists f. exists l. exists v. 
    split. exists 1. intros. destruct n. omega. simpl. rewrite H5. reflexivity.
    eapply unvv. assumption.

  - Case "Typ".

    rename f into STO.

    remember (val_type renv [] TBot STO) as df0. 
    
    
    assert (exists vf df, val_type renv [] (TMem T1 T1) ((vf, df) :: STO) (length STO)).
    eexists. eexists. eapply new_type. admit.
    reflexivity. reflexivity. 
    
    exists ((vty venv0 T1, val_type renv [] T1 f)::f).
    exists (length f).
    exists (vty venv0 T1).
    split. exists 1. intros. destruct n. omega. simpl. reflexivity.
    rewrite val_type_unfold. simpl. rewrite <-beq_nat_refl.
    rewrite <-(wf_length2 venv0 renv env f) in H.
    split. assumption. split. assumption.
    intros. split.

    intros. 

    (* problem case ly = length f *)
    assert (ly = length f) as L. admit.
    subst ly. simpl. intros.
    { eapply unvv. destruct T1; eapply vv.
      + admit.
      + admit.
      + admit.
      + rewrite val_type_unfold in H1.
        assert (indexr (length f)
                       (k1 ++ (vty venv0 (TSel v), val_type renv [] (TSel v) f) :: f) = Some (vty venv0 (TSel v), val_type renv [] (TSel v) f)). admit.
        rewrite H2 in H1.
        rewrite val_type_unfold. 

        simpl in H0. rewrite beq_nat_refl in H0.
      + rewrite val_type_unfold in H0. simpl in H0. rewrite beq_nat_refl in H0.
        ev. specialize (H2 (length f)). ev. eapply H2.
        rewrite val_type_unfold. 
    

    intros. 
    
    exists (S m). exists f'. exists m. exists (vty venv0 T1).
    split. admit. split. omega.
    split. intros. subst f'. assert (beq_nat i m = false). eapply beq_nat_false_iff. omega. rewrite H2. reflexivity.
    split. intros. subst f'. assert (beq_nat i m = false). eapply beq_nat_false_iff. omega. rewrite H2.  eapply H0. omega. 
    split. exists 1. intros. destruct n. omega. simpl. reflexivity.

    assert (forall ly vy,  val_type renv [] T1 f ly vy  = val_type renv [] T1 f' ly vy). subst f'. 
    intros. 
    rewrite val_type_unfold. rewrite val_type_unfold. destruct vy. admit.
    destruct T1; try eauto. 
    + simpl. admit.
    + case_eq (beq_nat ly m); intros E. 

    
    rewrite <-(wf_length2 venv0 renv env f) in H.
    assert (val_type renv [] (TMem T1 T1) f m (vty venv0 T1)).
    rewrite val_type_unfold.
    split. auto. split. auto. 

    
    rewrite val_type_unfold. simpl. split. assumption. split. assumption.
    intros. 
    assert (f' m ly vy  = val_type renv [] T1 f' ly vy). subst f'. 
    assert (beq_nat m m = true). eapply beq_nat_true_iff. reflexivity.
    rewrite H1.

    rewrite val_type_unfold. rewrite val_type_unfold. destruct vy. admit.
    destruct T1; try eauto. 
    + simpl. admit.
    + case_eq (beq_nat ly m); intros E. 
    
    
    admit. 
    (* TODO: here we need more. we need to show that 
    
    intros. split. 
    
    destruct (H0 0 (dy 0) vy). assumption.
    destruct (H0 0 (dy 0) vy). assumption.
    eapply WFE.

  - Case "VarPack".
    unfold R_env in WFE. ev. destruct (H4 _ _ H) as [d [v [I ?]]]. ev.
    exists d. exists v. split. exists 0. intros. destruct n. omega. simpl. rewrite I. reflexivity.
    intros. 
    assert (val_type renv [d] (open (varH 0) T1) x0 (d x0) v). admit. (* subst *)
    exists x0. rewrite val_type_unfold.
    destruct v; exists d; split.
    reflexivity. assumption.
    reflexivity. assumption. 

  - Case "VarUnpack".
    unfold R_env in WFE. ev. destruct (H4 _ _ H) as [d [v [I ?]]]. ev.
    exists d. exists v. split. exists 0. intros. destruct n. omega. simpl. rewrite I. reflexivity.
    rename x0 into k. 
    assert (exists jj, jj k = d k /\ val_type renv (jj::nil) (open (varH 0) T1) k (jj k) v). {
    intros. 
    eapply unvv in H6. rewrite val_type_unfold in H6.
    destruct v.
    ev. exists x0. split. assumption. assumption.
    ev. exists x0. split. assumption. assumption. }

    exists k. ev. rename x0 into jj. 

    
    
    admit. (* NOT CLEAR *)


  - Case "And". admit.
  - Case "And11". admit.
  - Case "And12". admit.

  - Case "unpack". 
    rewrite <-(wf_length2 _ _ _ WFE) in H. 
    destruct (IHW1 venv0 renv WFE) as [dx [vx [IW1 HVX]]].
    specialize (HVX 0).
    rewrite val_type_unfold in HVX.
    assert (exists jj : vseta,
              (forall n : nat,
                 val_type renv [jj] (open (varH 0) T1) n (jj n) vx)) as E.
    destruct vx; ev; exists x0; assumption. 
    destruct E as [jj VXH]. 
    assert (forall n, val_type (jj::renv) [] (open (varF (length renv)) T1) n (jj n) vx) as VXF.
    admit. (* subst *)
    
    assert (R_env (vx::venv0) (jj::renv) (T1'::env)) as WFE1.
    eapply wf_env_extend. assumption. rewrite H. assumption.

    specialize (IHW2 _ _ WFE1).
    destruct IHW2 as [dy [vy [IW2 HVY]]].


    (* question: *)
    clear HVX. clear VXF. 
    assert (jj 0 = dx 0). admit. (* sure *)
    assert (forall k : nat, val_type renv [jj] T2 k (jj k) vy). admit. (* sure *)
    assert (forall k : nat, val_type renv [dx] T2 k (dx k) vy). (* big question! *)

      

    
    

    (* /question *)

    
    exists dy. exists vy. split. {
      destruct IW1 as [nx IWX].
      destruct IW2 as [ny IWY].
      exists (S (nx+ny)). intros. destruct n. omega. simpl.
      rewrite IWX. rewrite IWY. eauto.
      omega. omega.
    }
    intros. eapply unvv. eapply valtp_shrink. 
    eapply HVY. rewrite (wf_length2 _ _ _ WFE). assumption.
    
  - Case "App".
    rewrite <-(wf_length2 _ _ _ WFE) in H. 
    destruct (IHW1 venv0 renv WFE) as [df [vf [IW1 HVF]]].
    destruct (IHW2 venv0 renv WFE) as [dx [vx [IW2 HVX]]].

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
    admit. (*
    rewrite <-(wf_length2 _ _ _ WFE) in H0. 
    destruct (IHW1 venv0 renv WFE) as [vf [IW1 HVF]].
    destruct (IHW2 venv0 renv WFE) as [vx [IW2 HVX]].

    (* TODO: extract this into a lemma? *)
    assert (exists vx jj,
              indexr x venv0 = Some vx /\
              indexr x renv = Some jj /\
              jj vx nil /\
              (forall vy iy, if pos iy then jj vy iy -> vtp renv [] vy T1 iy
                             else           vtp renv [] vy T1 iy -> jj vy iy) /\
              (forall vp ip, jj vp ip -> forall vy iy, if pos iy
                             then jj vy (ip ++ lb :: iy) -> jj vy (ip ++ ub :: iy)
                             else jj vy (ip ++ ub :: iy) -> jj vy (ip ++ lb :: iy))) as B.
    { unfold R_env in WFE. ev. remember (tvar x) as E. clear W1 IHW1 IHW2 HVF HVX IW1 IW2. induction W2; inversion HeqE; try subst x0.
    + destruct (H3 _ _ H4). ev. exists x0. exists x1. split. assumption. split. assumption. split. assumption.
      split. assumption. assumption.
    + specialize (IHW2 H5 H1 H2 H3). ev.
      eexists. eexists. split. eassumption. split. eassumption. split. assumption. split.
      assert (forall vy iy, if pos iy 
                            then val_type renv [] vy T1 iy -> vtp renv [] vy T0 iy
                            else val_type renv [] vy T0 iy -> vtp renv [] vy T1 iy) as A.
      eapply valtp_widen_aux. eassumption. omega.
      intros. specialize (H3 _ _ H11). destruct H3. ev. exists x3. exists x4. repeat split; eassumption. reflexivity.
      
      intros. inversion H11.
      intros. specialize (A vy iy). specialize (H9 vy iy). destruct (pos iy).
      intros. eapply A. eapply unvv. eapply H9. assumption.
      intros. eapply H9. eapply A. eapply unvv. assumption.
      assumption. }

    ev. 
    eapply invert_dabs in HVF.
    destruct HVF as [venv1 [TX [y [HF IHF]]]].

    (* shouldn't be needed *)
    assert (x0 = vx). { destruct IW2. assert (S x2 > x2) as SS. omega. specialize (H6 (S x2) SS). simpl in H6. inversion H6. rewrite H8 in H1. inversion H1. reflexivity. }
    subst x0.                      
                      
    destruct (IHF vx H3) as [vy [IW3 HVY]].

    exists vy. split. {
      (* pick large enough n. nf+nx+ny will do. *)
      destruct IW1 as [nf IWF].
      destruct IW2 as [nx IWX].
      destruct IW3 as [ny IWY].
      exists (S (nf+nx+ny)). intros. destruct n. omega. simpl.
      rewrite IWF. subst vf. rewrite IWX. rewrite IWY. reflexivity.
      omega. omega. omega.
    }
    subst T. eapply HVY. eapply H2. intros. specialize (H4 vy iy). destruct (pos iy).
    intros. eapply unvv. eapply H4. assumption.
    intros. eapply H4. eapply vv. assumption.
    assumption.*)
    
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
    assert (R_env (vx::venv0) (jj::renv) (T1::env)) as WFE1. {
      eapply wf_env_extend0. eapply WFE. eapply H0. }
    specialize (IHW (vx::venv0) (jj::renv) WFE1).
    destruct IHW as [d [v [EV VT]]]. rewrite <-(wf_length2 _ _ _ WFE) in VT. 
    exists d. exists v. split. eapply EV. 
    intros. eapply vtp_subst3. assumption. eapply VT. 

  - Case "Sub".
    specialize (IHW venv0 renv WFE). ev. exists x. exists x0. split. eassumption.
    intros. eapply unvv. eapply valtp_widen. eapply H1. eapply H. eapply WFE. 

Grab Existential Variables.

Qed.


