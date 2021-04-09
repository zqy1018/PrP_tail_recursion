Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Lia.
From TRO Require Import Maps.
From Coq Require Import Lists.List.
From TRO Require Import Smallstep.

Inductive tm : Type :=
  | tm_invalid : tm
  (* pure mystlc *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> tm -> tm
  (* numbers *)
  | tm_const: nat -> tm
  | tm_add : tm -> tm -> tm
  | tm_succ    : tm -> tm
  | tm_pred    : tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
  (* fix *)
  | tm_fix  : tm -> tm
  (* mutable ref *)
  | tm_unit   : tm
  | tm_ref    : tm -> tm
  | tm_deref  : tm -> tm
  | tm_assign : tm -> tm -> tm
  | tm_loc    : nat -> tm.

(* notations *)
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

Notation "{ x }" := x (in custom mystlc at level 1, x constr).
Notation "'succ' x" := (tm_succ x) (in custom mystlc at level 0,
                                     x custom mystlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom mystlc at level 0,
                                     x custom mystlc at level 0).
Notation "x + y" := (tm_add x y) (in custom mystlc at level 1,
                                      left associativity).
(* Notation "'Nat'" := Ty_Nat (in custom mystlc at level 0). *)
Coercion tm_const : nat >-> tm.

Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom mystlc at level 89,
                    x custom mystlc at level 99,
                    y custom mystlc at level 99,
                    z custom mystlc at level 99,
                    left associativity).

Notation "'fix' t" := (tm_fix t) (in custom mystlc at level 0).

Notation "'unit'" := tm_unit (in custom mystlc at level 0).
Notation "'loc' x" := (tm_loc x) (in custom mystlc at level 2).
Notation "'ref' x" := (tm_ref x) (in custom mystlc at level 2).
Notation "'!' x " := (tm_deref x) (in custom mystlc at level 2).
Notation " e1 ':=' e2 " := (tm_assign e1 e2) (in custom mystlc at level 21).

(* value *)
Inductive value : tm -> Prop :=
  | v_abs : forall x t1,
      value <{\x, t1}>
  | v_nat : forall n : nat ,
      value <{ n }>
  | v_unit :
      value <{ unit }>
  | v_loc : forall l,
      value <{ loc l }>.

Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom mystlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_invalid => tm_invalid
  | tm_var y =>
      if eqb_string x y then s else t
  | tm_abs y t1 =>
      if eqb_string x y then t else tm_abs y (subst x s t1)
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{t1 + t2}> =>
      <{ ([x:=s] t1) + ([x:=s] t2) }>
  | <{succ t1}> =>
      <{succ [x := s] t1}>
  | <{pred t1}> =>
      <{pred [x := s] t1}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}>
  (* fix *)
  | <{fix t'}> => <{fix ([x:=s] t')}>
  (* references *)
  | <{ unit }> =>
    <{ unit }>
  | <{ ref t1 }> =>
      <{ ref ([x:=s] t1) }>
  | <{ !t1 }> =>
      <{ !([x:=s] t1) }>
  | <{ t1 := t2 }> =>
    <{ ([x:=s] t1) := ([x:=s] t2) }>
  | <{ loc _ }> =>
      t
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom mystlc).

(* store *)
Definition store := list tm.

Definition store_lookup (n:nat) (st:store) :=
  nth n st <{ unit }>.

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | List.nil    => List.nil
  | h :: t =>
    (match n with
    | O    => x :: t
    | S n' => h :: replace n' x t
    end)
  end.

Reserved Notation "t '/' st '-->' t' '/' st'"
  (at level 40, st at level 39, t' at level 39).

Inductive step : tm * store -> tm * store -> Prop :=
  | ST_AppAbs : forall x t1 v2 st,
         value v2 ->
         <{ (\x, t1) v2 }> / st --> <{ [x := v2] t1 }> / st
  | ST_App1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 t2 }> / st --> <{ t1' t2 }> / st'
  | ST_App2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 t2 }> / st --> <{ v1 t2' }> / st'
  (* numbers *)
  | ST_SuccNatural : forall (n : nat) st,
         <{ succ n }> / st --> tm_const (S n) / st
  | ST_Succ : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ succ t1 }> / st --> <{ succ t1' }> / st'
  | ST_PredNatural : forall (n : nat) st,
         <{ pred n }> / st --> tm_const (n - 1) / st
  | ST_Pred : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ pred t1 }> / st --> <{ pred t1' }> / st'
  | ST_Addconsts: forall (n1 n2 : nat) st,
         <{n1 + n2}> / st --> (tm_const (n1+n2)) / st
  | ST_Add1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{t1 + t2}> / st --> <{t1' + t2}> / st'
  | ST_Add2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{v1 + t2}> / st --> <{v1 + t2'}> / st'
  | ST_If0 : forall t1 t1' t2 t3 st st',
         t1 / st --> t1' / st' ->
         <{ if0 t1 then t2 else t3 }> / st --> <{ if0 t1' then t2 else t3 }> / st'
  | ST_If0_Zero : forall t2 t3 st,
         <{ if0 0 then t2 else t3 }> / st --> t2 / st
  | ST_If0_Nonzero : forall n t2 t3 st,
         <{ if0 {S n} then t2 else t3 }> / st --> t3 / st
  (* references *)
  | ST_RefValue : forall v st,
         value v ->
         <{ ref v }> / st --> <{ loc { Datatypes.length st } }> / (st ++ v::List.nil)
  | ST_Ref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ref t1 }> /  st --> <{ ref t1' }> /  st'
  | ST_DerefLoc : forall st l,
         l < Datatypes.length st ->
         <{ !(loc l) }> / st --> <{ { store_lookup l st } }> / st
  | ST_Deref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ! t1 }> / st --> <{ ! t1' }> / st'
  | ST_Assign : forall v l st,
         value v ->
         l < Datatypes.length st ->
         <{ (loc l) := v }> / st --> <{ unit }> / replace l v st
  | ST_Assign1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 := t2 }> / st --> <{ t1' := t2 }> / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 := t2 }> / st --> <{ v1 := t2' }> / st'

where "t '/' st '-->' t' '/' st'" := (step (t,st) (t',st')).

Hint Constructors step : core.

Definition multistep := (multi step).
Notation "t '/' st '-->*' t' '/' st'" :=
               (multistep (t,st) (t',st'))
               (at level 40, st at level 39, t' at level 39).

Definition x : string := "x".
Definition invalid_string : string := "invalid".

Definition y : string := "y".
Definition z : string := "z".
Definition k : string := "k".
Definition u : string := "k".
Definition n : string := "n".
Definition g : string := "g".
Definition s : string := "s".
Definition r : string := "r".
Definition s1 : string := "s1".
Definition s2 : string := "s2".
Definition s3 : string := "s3".
Definition s4 : string := "s4".
Definition f : string := "f".
Definition l : string := "l".
Definition l' : string := "l'".
Definition acc : string := "acc".

Hint Unfold invalid_string : core.
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Hint Unfold u : core.
Hint Unfold n : core.
Hint Unfold g : core.
Hint Unfold k : core.
Hint Unfold r : core.
Hint Unfold s : core.
Hint Unfold s1 : core.
Hint Unfold s2 : core.
Hint Unfold s3 : core.
Hint Unfold s4 : core.
Hint Unfold f : core.
Hint Unfold l : core.
Hint Unfold l' : core.
Hint Unfold acc : core.
Hint Unfold Datatypes.length: core.

(* sequence *)
Definition tseq t1 t2 :=
  <{ (\ x, t2)  t1 }>.

Notation "t1 ; t2" := (tseq t1 t2) (in custom mystlc at level 3).

Ltac reduce :=
    repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; compute)];
            try solve [apply multi_refl]).

(* some examples *)
Definition sum : tm :=
  <{
    (
    \r, \n,
      (r := \n, if0 n then 0 else ( n + ((!r) (pred n)) ));
      ( (!r) n )
    )
    (ref (\x, 1))
  }>.

Lemma sum_4 : exists st,
  <{sum 4}> / nil -->* tm_const 10 / st.
Proof.
  eexists. unfold sum. 
  reduce.
  
  (* eapply multi_step.
    eapply ST_App1.
      eapply ST_App2. auto.
        eapply ST_RefValue. auto.

  eapply multi_step.
    eapply ST_App1.
      eapply ST_AppAbs. auto.
  
  eapply multi_step.
    eapply ST_AppAbs. auto. simpl.

  eapply multi_step.
    eapply ST_App2. auto.
      eapply ST_Assign. auto. auto. simpl.

  eapply multi_step.
    eapply ST_AppAbs. auto. simpl.

  eapply multi_step.
    eapply ST_App1.
      eapply ST_DerefLoc. auto. unfold store_lookup. simpl.

  eapply multi_step.
    eapply ST_AppAbs. auto. simpl.
    
  eapply multi_step.
    eapply ST_If0_Nonzero.
  
  eapply multi_step.
    eapply ST_Add2;auto.
      eapply ST_App1.
        eapply ST_DerefLoc;auto. unfold store_lookup. simpl.
  
  eapply multi_step.
    eapply ST_Add2;auto.
      eapply ST_App2;auto.
        eapply ST_PredNatural. simpl.
      
  eapply multi_step.
    eapply ST_Add2;auto.
      eapply ST_AppAbs;auto. simpl.

  eapply multi_step.
    eapply ST_Add2;auto.
      eapply ST_If0_Zero.

  eapply multi_step.
    eapply ST_Addconsts. simpl.

  apply multi_refl. *)
Qed.

Definition sum_tail : tm :=
  <{
    (
    \r, \n,
      (r := \n, \k, if0 n 
                    then k 0 
                    else ( (!r) (pred n) (\s, k (n + s)) ));
      ( (!r) n (\s, s))
    )
    (ref unit)
  }>.

Lemma sum_tail_4 : exists st,
  <{sum_tail 4}> / nil -->* tm_const 10 / st.
Proof.
  eexists. unfold sum_tail.
  reduce.
Qed.

(*
Definition sum : tm :=
  <{
    (
    \r, \n,
      (r := \n, if0 n then 0 else ( n + ((!r) (pred n)) ));
      ( (!r) n )
    )
    (ref (\x, 1))
  }>.
*)

Definition foo_not_tail_mutable : tm :=
  <{
    (
    \r, \y, \n,
      (r := \n, if0 n 
                then (!y)
                else (y := (!y) + 1); ((!y) + ((!r) (pred n)))
      );
      ( (!r) n)
    )
    (ref unit)
    (ref 0)
  }>.

Definition foo_not_tail_mutable_dif : tm :=
  <{
    (
    \r, \y, \n,
      (
      r := \n, 
            if0 n 
            then (y := (!y) + 1)
            else (y := (!y) + 1); 
            ((!y) + ((!r) (pred n)) + (!y) + ((!r) (pred n)) + (!y))
      );
      ( (!r) n)
    )
    (ref unit)
    (ref 0)
  }>.

(* Lemma foo_not_tail_mutable_1: exists st,
  <{foo_not_tail_mutable 1}> / nil -->* tm_const 10 / st.
Proof.
  eexists. unfold foo_not_tail_mutable.
  reduce.

  eapply multi_step.
    eapply ST_App2; auto.
      eapply ST_Assign; auto. unfold Datatypes.length; auto. simpl.
    
  reduce.

  eapply multi_step.
    eapply ST_App1.
      eapply ST_DerefLoc. unfold Datatypes.length; auto. unfold store_lookup; auto. simpl.

  reduce.

  eapply multi_step.
    eapply ST_Add2;auto.
      eapply ST_App1.
        eapply ST_DerefLoc. unfold Datatypes.length. auto. unfold store_lookup; auto. simpl.

  reduce.

      eapply ST_App2;auto.
        eapply ST_Assign2;auto.
          eapply ST_Add1. eapply ST_DerefLoc. unfold Datatypes.length; auto. unfold store_lookup; auto. simpl.

  eapply multi_step.
    eapply ST_App2;auto.
      eapply ST_App2;auto.
        eapply ST_Assign1;auto.

  
Qed. *)


Definition sum_tail_mutable : tm :=
  <{
    (
    \r, \g, \n,
      (r := \n, if0 n 
                then !g 
                else (g := n + (!g)); (!r) (pred n)
      );
      ( (!r) n)
    )
    (ref unit)
    (ref 0)
  }>.

Lemma sum_tail_mutable_2 : exists st,
  <{sum_tail_mutable 2}> / nil -->* tm_const 3 / st.
Proof with eauto.
  eexists. unfold sum_tail_mutable.  
  reduce.

  eapply multi_step.
    eapply ST_App2;auto.
      eapply ST_Assign;auto. auto. unfold length. auto. simpl.
  
  reduce.

  eapply multi_step.
    eapply ST_App1.
      eapply ST_DerefLoc. unfold Datatypes.length. auto. unfold store_lookup. simpl.

  reduce.

  eapply multi_step.
    eapply ST_App1.
      eapply ST_DerefLoc. unfold Datatypes.length. auto. unfold store_lookup. simpl.
  
  reduce.

  eapply multi_step.
    eapply ST_App1.
      eapply ST_DerefLoc. unfold Datatypes.length. auto. unfold store_lookup. simpl.

  reduce.
Qed.