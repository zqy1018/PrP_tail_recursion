From Coq Require Import Strings.String.
From TRO Require Import Maps.
(* From TRO Require Import Smallstep. *)
From TRO Require Import Variables.

Inductive tm : Type :=
  | tm_invalid : tm
  (* pure mystlc *)
  | tm_var : string  -> tm
  | tm_app : tm -> tm  -> tm
  | tm_abs : string -> tm -> tm
  (* numbers *)
  | tm_const: nat -> tm
  | tm_add : tm -> tm -> tm
  (* a closure is a term with environment *)
  | tm_closure : tm -> (string -> tm) -> tm.
  
Definition ENV := string -> tm.

Declare Custom Entry mystlc.
Notation "<{ e }>" := e (e custom mystlc at level 99).
Notation "x" := x (in custom mystlc at level 0, x constr at level 0).
Notation "( x )" := x (in custom mystlc, x at level 99).
Notation "x y" := (tm_app x y) (in custom mystlc at level 1, left associativity).
Notation "\ x , y" :=
  (tm_abs x y) (in custom mystlc at level 90, x at level 99,
                     y custom mystlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

(* Notation "t [ env ]" := (tm_closure tm env) (in custom mystlc at level 90, t at level 99, env at level 99). *)

Notation "{ x }" := x (in custom mystlc at level 1, x constr).
Notation "x + y" := (tm_add x y) (in custom mystlc at level 1,
                                      left associativity).
Coercion tm_const : nat >-> tm.  

Inductive value : tm -> Prop :=
  | v_closure : forall x t env,
    value (tm_closure (tm_abs x t) env)
  | v_nat : forall n : nat ,
    value <{ n }>.

Definition empty_env := 
  (
    _ !-> tm_invalid
  ).


Reserved Notation "t '-->' t'" (at level 40).

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

(* env1 first *)
Definition combine (env1 env2 : ENV) :=
  fun x => 
    match (env1 x) with
    | tm_invalid => (env2 x)
    | t => t
    end.

Inductive step : tm  -> tm -> Prop :=
  (* enter a closure *)
  | ST_Closure : forall x t,
    <{ \x, t }> --> tm_closure <{ \x, t }> empty_env
  | ST_AppAbs_Closure : forall x t1 t2 env,
    value t2 ->
    tm_app (tm_closure (tm_abs x t1) env) t2 -->
      tm_closure t1 (t_update env x t2)
  (* nested closure *)
  | ST_Closure_Nested : forall t t' env1 env2,
    tm_closure t (combine env1 env2)  --> tm_closure t' (combine env1 env2) ->
    tm_closure (tm_closure t env1) env2 --> tm_closure (tm_closure t' env1) env2
  (* de-nest closure if inner closure is a value*)
  | ST_Closure_Denested_Const : forall n env1 env2,
    tm_closure (tm_closure (tm_const n) env1) env2 --> tm_closure (tm_const n) env2
  | ST_Closure_Denested_Abs : forall x t env1 env2,
    tm_closure (tm_closure <{ \x, t }> env1) env2 --> tm_closure <{ \x, t }> (combine env1 env2) 
  (* in the innermost closure *)
  | ST_Closure_Var : forall x env,
    tm_closure (tm_var x) env --> tm_closure (env x) env
  | ST_Closure_App1 : forall t1 t1' t2 env,
    tm_closure t1 env --> tm_closure t1' env ->
    tm_closure <{ t1 t2 }> env --> tm_closure <{ t1' t2 }> env
  | ST_Closure_App2 : forall t1 t2 t2' env,
    value t1 ->
    tm_closure t2 env --> tm_closure t2' env ->
    tm_closure <{ t1 t2 }> env --> tm_closure <{ t1 t2' }> env
  | ST_Closure_AppAbs: forall x t1 t2 env,
    value t2 ->
    tm_closure <{ (\x, t1) t2 }> env --> tm_closure (tm_closure t1 (t_update empty_env x t2)) env
  | ST_Closure_Closure_AppAbs: forall x t1 t2 env1 env2,
    value t2 ->
    tm_closure <{ {tm_closure <{ \x, t1 }> env1} t2 }> env2 --> tm_closure (tm_closure t1 (t_update env1 x t2)) env2
  | ST_Closure_Addconst : forall (n1 n2 : nat) env,
    tm_closure <{ n1 + n2 }> env --> tm_closure (tm_const (n1+n2)) env
  | ST_Closure_Add1 : forall t1 t1' t2 env,
    tm_closure t1 env --> tm_closure t1' env ->
    tm_closure (tm_add t1 t2) env --> tm_closure (tm_add t1' t2) env
  | ST_Closure_Add2 : forall t1 t2 t2' env,
    value t1 ->
    tm_closure t2 env --> tm_closure t2' env ->
    tm_closure (tm_add t1 t2) env --> tm_closure (tm_add t1 t2') env
  (* Get rid of a closure *)
  | ST_Closure_Val : forall v env,
    value v ->
    tm_closure v env --> v
  (* classical *)
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_Addconsts: forall n1 n2 : nat,
         <{n1 + n2}> --> <{ {n1 + n2} }>
  | ST_Add1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 + t2}> --> <{t1' + t2}>
  | ST_Add2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 + t2}> --> <{v1 + t2'}>
  where "t '-->' t'" := (step t t').

Hint Constructors value : core.
Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Theorem test0: <{(\x, \y, x + y) 3 4}> -->* tm_const 7.
Proof.
  eapply multi_step. auto.

  eapply multi_step. auto.
  
  eapply multi_step. auto.

  eapply multi_step. auto. unfold t_update at 1. simpl. unfold t_update at 1. simpl.

  eapply multi_step. auto. unfold t_update at 1. simpl.
  
  eapply multi_step. auto. simpl.

  eapply multi_step. eapply ST_Closure_Val. auto.

  eapply multi_refl.
Qed.

Definition add5 : string := "add5".
Hint Unfold add5 : core.
  
Theorem test1: 
  <{ (\add5, (add5 3) + 3) ((\x, (\y, x + y)) 5) }> -->* (tm_const 11).
Proof.
  eapply multi_step. auto.

  eapply multi_step. auto.

  eapply multi_step. auto.

  eapply multi_step. auto.

  eapply multi_step. auto. unfold t_update at 1. simpl.

  eapply multi_step. auto.

  eapply multi_step. auto. unfold combine. simpl.

  eapply multi_step. auto. unfold combine. simpl.

  eapply multi_step. auto. simpl.

  eapply multi_step. auto. 

  eapply multi_step. auto. simpl.
  
  eapply multi_step. auto.
  
  eapply multi_refl.
Qed.


Theorem test2: 
  <{ (\z, ((\y, y + z) 3)) 5 }> -->* <{8}>.
Proof.
  eapply multi_step. auto.

  eapply multi_step. auto.
  
  eapply multi_step. auto.

  eapply multi_step. auto. unfold combine at 1. simpl.

  eapply multi_step. auto. unfold combine at 1. simpl. unfold t_update at 1. simpl.

  eapply multi_step. auto.

  eapply multi_step. auto. simpl.

  eapply multi_step. auto.

  apply multi_refl.
Qed.

Theorem test3: 
  <{ (\x, ((\x, (\y, x + y)) 1 2) + x) 5 }> -->* <{8}>.
Proof.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. auto. unfold combine at 1. simpl.
  eapply multi_step. auto. unfold combine at 1. simpl.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto.
  eapply multi_step. auto. unfold t_update at 1. simpl.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto.
  eapply multi_refl.
Qed.

  


