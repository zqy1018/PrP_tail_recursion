Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From TRO Require Import Maps.
From TRO Require Import Smallstep.

(* a simple mystlc that only has nat types and supports list, fix*)

Inductive ty : Type :=
  | Ty_Invalid : ty
  | Ty_Nat  : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_List  : ty -> ty.

Inductive tm : Type :=
  | tm_invalid : tm
  (* pure mystlc *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* numbers *)
  | tm_const: nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  (* lists *)
  | tm_nil : ty -> tm
  | tm_cons : tm -> tm -> tm
  | tm_lcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., [case t1 of | nil => t2 | x::y => t3] *)
  (* fix *)
  | tm_fix  : tm -> tm.

Declare Custom Entry mystlc.
Notation "<{ e }>" := e (e custom mystlc at level 99).
Notation "x" := x (in custom mystlc at level 0, x constr at level 0).
Notation "( x )" := x (in custom mystlc, x at level 99).
Notation "S -> T" := (Ty_Arrow S T) (in custom mystlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom mystlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom mystlc at level 90, x at level 99,
                     t custom mystlc at level 99,
                     y custom mystlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom mystlc at level 1, x constr).
Notation "'succ' x" := (tm_succ x) (in custom mystlc at level 0,
                                     x custom mystlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom mystlc at level 0,
                                     x custom mystlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom mystlc at level 1,
                                      left associativity).
Notation "'Nat'" := Ty_Nat (in custom mystlc at level 0).
Coercion tm_const : nat >-> tm.

Notation "'List' T" :=
  (Ty_List T) (in custom mystlc at level 4).
Notation "'nil' T" := (tm_nil T) (in custom mystlc at level 0, T custom mystlc at level 0).
Notation "h '::' t" := (tm_cons h t) (in custom mystlc at level 2, right associativity).
Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' x '::' y '=>' t3" :=
  (tm_lcase t1 t2 x y t3) (in custom mystlc at level 89,
                              t1 custom mystlc at level 99,
                              t2 custom mystlc at level 99,
                              x constr at level 1,
                              y constr at level 1,
                              t3 custom mystlc at level 99,
                              left associativity).

Notation "'fix' t" := (tm_fix t) (in custom mystlc at level 0).

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  (* Numbers are values: *)
  | v_nat : forall n : nat,
      value <{n}>
  (* list *)
  | v_lnil : forall T1, value <{nil T1}>
  | v_lcons : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{v1 :: v2}>.

Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom mystlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_invalid => tm_invalid
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{succ t1}> =>
      <{succ [x := s] t1}>
  | <{pred t1}> =>
      <{pred [x := s] t1}>
  | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
  (* lists *)
  | <{nil _}> =>
      t
  | <{t1 :: t2}> =>
      <{ ([x:=s] t1) :: [x:=s] t2 }>
  | <{case t1 of | nil => t2 | y1 :: y2 => t3}> =>
      <{case ( [x:=s] t1 ) of
        | nil => [x:=s] t2
        | y1 :: y2 =>
        {if eqb_string x y1 then
           t3
         else if eqb_string x y2 then t3
              else <{ [x:=s] t3 }> } }>
  (* fix *)
  | <{fix t'}> => <{fix ([x:=s] t')}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom mystlc).

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  (* numbers *)
  | ST_Succ : forall t1 t1',
         t1 --> t1' ->
         <{succ t1}> --> <{succ t1'}>
  | ST_SuccNat : forall n : nat,
         <{succ n}> --> <{ {S n} }>
  | ST_Pred : forall t1 t1',
         t1 --> t1' ->
         <{pred t1}> --> <{pred t1'}>
  | ST_PredNat : forall n:nat,
         <{pred n}> --> <{ {n - 1} }>
  | ST_Mulconsts : forall n1 n2 : nat,
         <{n1 * n2}> --> <{ {n1 * n2} }>
  | ST_Mult1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 * t2}> --> <{t1' * t2}>
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 * t2}> --> <{v1 * t2'}>
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{t1 :: t2}> --> <{t1' :: t2}>
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{v1 :: t2}> --> <{v1 :: t2'}>
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 --> t1' ->
       <{case t1 of | nil => t2 | x1 :: x2 => t3}> -->
       <{case t1' of | nil => t2 | x1 :: x2 => t3}>
  | ST_LcaseNil : forall T1 t2 x1 x2 t3,
       <{case nil T1 of | nil => t2 | x1 :: x2 => t3}> --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       <{case v1 :: vl of | nil => t2 | x1 :: x2 => t3}>
         -->  <{ [x2 := vl] ([x1 := v1] t3) }>
  (* fix *)
  | ST_Fix1 : forall t1 t1',
       t1 --> t1' ->
       <{fix t1}> --> <{fix t1'}>
  | ST_FixAbs : forall xf T1 t1,
       <{fix (\xf:T1, t1)}> --> <{[xf:=fix(\xf:T1, t1)] t1}>
  where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

Lemma testmystlc: <{3 * 5}> -->* <{15}>.
Proof.
  normalize.
Qed.

Definition x : string := "x".
Definition invalid_string : string := "invalid".

Definition y : string := "y".
Definition z : string := "z".
Definition k : string := "k".
Definition s : string := "s".
Definition f : string := "f".
Definition l : string := "l".
Definition l' : string := "l'".
Definition acc : string := "acc".

Hint Unfold invalid_string : core.
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Hint Unfold k : core.
Hint Unfold s : core.
Hint Unfold f : core.
Hint Unfold l : core.
Hint Unfold l' : core.
Hint Unfold acc : core.

Definition list := <{2::3::(nil Nat)}>.

Definition tail_cont := 
  <{fix 
      (\f:List Nat->(Nat->Nat)->Nat,
          \l:List Nat, \k:Nat->Nat,
            case l of
            | nil => k 1
            | x::l' => f l' (\s:Nat, k (x * s))
      )}>.

Definition tail := 
  <{\l:List Nat, tail_cont l <{\s:Nat,s}>}>.

Theorem test_tail: <{tail list}> -->* <{6}>.
Proof.
  unfold tail. unfold tail_cont. unfold list.
  normalize.
Qed.

Definition not_tail := 
  <{fix
      (\f:List Nat->Nat,
        \l:List Nat,
          case l of
          | nil => 1
          | x::l' => x * (f l')
      )}>.

Definition match_name(term:tm) := match term with |<{\name:_, _}> => name | _ => invalid_string end.

Definition match_type(term:tm) := match term with |<{\_:type, _}> => type | _ => Ty_Invalid end.

Definition match_next(term:tm) := match term with |<{\_:_, next}> => next | _ => tm_invalid end.

(* Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' x '::' y '=>' t3" :=
  (tm_lcase t1 t2 x y t3) (in custom mystlc at level 89,
                              t1 custom mystlc at level 99,
                              t2 custom mystlc at level 99,
                              x constr at level 1,
                              y constr at level 1,
                              t3 custom mystlc at level 99,
                              left associativity). *)

Definition to_tail(func:tm) := 
  let t_f:=(match func with |<{fix f}> => f | _ => tm_invalid end) in 
  let f_name:=match_name t_f in 
  let f_type:=match_type t_f in
  let t_case:=match_next t_f in 
  let l_name:=match_name t_case in
  let l_type:=match_type t_case in 
  let ele_type:=(match l_type with | Ty_List ele => ele | _ => Ty_Invalid end) in
  let t_case:=match_next t_case in
  let init_value:=(match t_case with 
                   | tm_lcase _ init _ _ _ => init 
                   | _ => tm_invalid end) in
  let x_name    :=(match t_case with 
                   | tm_lcase _ _ name _ _ => name
                   | _ => invalid_string end) in 
  let l'_name   :=(match t_case with 
                   | tm_lcase _ _ _ name _ => name
                   | _ => invalid_string end) in 
  let exp       :=(match t_case with 
                   |tm_lcase _ _ _ _ exp => exp
                   | _ => tm_invalid end) in 
  let exp_left  :=(match exp with
                   | tm_mult exp_left _ => exp_left
                   | _ => tm_invalid end) in
  let cont      :=<{fix
                      (\f_name:f_type,
                          \l_name:l_type, \k:ele_type->ele_type,
                            case l_name of 
                            | nil => k init_value
                            | x_name::l'_name => f l'_name (\s:Nat, k (exp_left * s)))}> in
  <{\l_name:l_type, cont l_name <{\s:ele_type,s}>}>.
(* Definition tail := 
  <{\l:List Nat, tail_cont l <{\s:Nat,s}>}>. *)

Compute (to_tail not_tail).

Definition optimized := to_tail not_tail.

Theorem test_to_tail: <{optimized list}> -->* <{6}>.
Proof.
  unfold optimized. unfold to_tail; simpl. unfold list. 
  normalize.
Qed.
