(* Define syntactic typing judgments. Currently unused. *)
Require Import dot_base.

(* ### Subtyping ### *)
(*
This split into an abstract and a concrete environment
was necessary in the D<: soundness development, but is 
not required here.
*)
Inductive stp: tenv -> ty -> ty -> Prop :=
| stp_top: forall GH T1,
    closed_ty 0 (length GH) T1 ->
    stp GH T1 TTop
| stp_bot: forall GH T2,
    closed_ty 0 (length GH) T2 ->
    stp GH TBot T2
| stp_mem: forall GH S1 U1 S2 U2,
    stp GH U1 U2 ->
    stp GH S2 S1 ->
    stp GH (TMem S1 U1) (TMem S2 U2)

| stp_sel1: forall GH TX T2 x,
    indexr x GH = Some TX ->
    closed_ty 0 (length GH) TX -> (* XXX unclear if length GH is correct, the existing code is inconsistent. *)
    stp GH TX (TMem TBot T2) ->
    stp GH (TSel (varF x)) T2
| stp_sel2: forall GH TX T1 x,
    indexr x GH = Some TX ->
    closed_ty 0 (length GH) TX ->
    stp GH TX (TMem T1 TTop) ->
    stp GH T1 (TSel (varF x)) 
| stp_selx: forall GH TX x,
    indexr x GH = Some TX  ->
    stp GH (TSel (varF x)) (TSel (varF x))

(* stp for recursive types and intersection types *)
| stp_bindx: forall GH T1 T1' T2 T2',
    stp (T1'::GH) T1' T2' ->
    T1' = (open (varF (length GH)) T1) ->
    T2' = (open (varF (length GH)) T2) ->
    closed_ty 1 (length GH) T1 ->
    closed_ty 1 (length GH) T2 ->
    stp GH (TBind T1) (TBind T2)

| stp_and11: forall GH T1 T2 T,
    stp GH T1 T ->
    closed_ty 0 (length GH) T2 ->
    stp GH (TAnd T1 T2) T

| stp_and12: forall GH T1 T2 T,
    stp GH T2 T ->
    closed_ty 0 (length GH) T1 ->
    stp GH (TAnd T1 T2) T

| stp_and2: forall GH T1 T2 T,
    stp GH T T1 ->
    stp GH T T2 ->
    stp GH T (TAnd T1 T2)


| stp_all: forall GH T1 T2 T3 T4 x,
    stp GH T3 T1 ->
    x = length GH ->
    closed_ty 1 (length GH) T2 ->
    closed_ty 1 (length GH) T4 ->
    stp (T3::GH) (open (varF x) T2) (open (varF x) T4) ->
    stp GH (TAll T1 T2) (TAll T3 T4)
| stp_trans: forall GH T1 T2 T3,
    stp GH T1 T2 ->
    stp GH T2 T3 ->
    stp GH T1 T3
.

(* ### Type Assignment ### *)
Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_var: forall x env T1,
           indexr x env = Some T1 ->
           stp env T1 T1 ->
           has_type env (tvar x) T1
(* pack a recursive type  *)
| t_var_pack : forall GH x T1 T1',
           (* has_type G1 (tvar x) T1' -> *)
           indexr x GH = Some (open (varF x) T1) ->            
           T1' = (open (varF x) T1) ->
           closed_ty 1 (length GH) T1 ->
           has_type GH (tvar x) (TBind T1) 
(* unpack a recursive type: unpack(x:{z=>T^z}) { x:T^x => ... }  *)                    
| t_unpack: forall env x y T1 T1' T2,
           has_type env x (TBind T1) ->
           T1' = (open (varF (length env)) T1) ->
           has_type (T1'::env) y T2 ->
           closed_ty 0 (length env) T2 ->
           has_type env (tunpack x y) T2

(* intersection typing *)
| t_and : forall env x T1 T2,
           has_type env (tvar x) T1 ->
           has_type env (tvar x) T2 ->
           has_type env (tvar x) (TAnd T1 T2)

               
| t_typ: forall env T1,
           closed_ty 0 (length env) T1 ->
           has_type env (ttyp T1) (TMem T1 T1)
               
| t_app: forall env f x T1 T2,
           has_type env f (TAll T1 T2) ->
           has_type env x T1 ->
           closed_ty 0 (length env) T2 ->
           has_type env (tapp f x) T2
| t_dapp:forall env f x T1 T2 T,
           has_type env f (TAll T1 T2) ->
           has_type env (tvar x) T1 ->
           T = open (varF x) T2 ->
           closed_ty 0 (length env) T ->
           has_type env (tapp f (tvar x)) T
| t_abs: forall env y T1 T2,
           has_type (T1::env) y (open (varF (length env)) T2) ->
           closed_ty 0 (length env) (TAll T1 T2) ->
           has_type env (tabs T1 y) (TAll T1 T2)
| t_sub: forall env e T1 T2,
           has_type env e T1 ->
           stp env T1 T2 ->
           has_type env e T2
.



Hint Constructors has_type.
Hint Constructors stp.
