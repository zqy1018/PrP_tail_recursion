Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From TRO Require Import Maps.
From TRO Require Import Smallstep.

(* a simple STLC that only has bool types and supports if, list, fix*)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_List : ty -> ty.

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm
  (* lists *)
  | tm_nil : ty -> tm
  | tm_cons : tm -> tm -> tm
  | tm_lcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., [case t1 of | nil => t2 | x::y => t3] *)
  (* fix *)
  | tm_fix  : tm -> tm.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
(* Notation "'Bool'" := Ty_Bool (in custom stlc_ty at level 0). *)
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).

Notation "'List' T" :=
  (Ty_List T) (in custom stlc at level 4).
Notation "'nil' T" := (tm_nil T) (in custom stlc at level 0, T custom stlc at level 0).
Notation "h '::' t" := (tm_cons h t) (in custom stlc at level 2, right associativity).
Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' x '::' y '=>' t3" :=
  (tm_lcase t1 t2 x y t3) (in custom stlc at level 89,
                              t1 custom stlc at level 99,
                              t2 custom stlc at level 99,
                              x constr at level 1,
                              y constr at level 1,
                              t3 custom stlc at level 99,
                              left associativity).

Notation "'fix' t" := (tm_fix t) (in custom stlc at level 0).

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition f : string := "z".
Definition l : string := "l".
Definition l' : string := "l'".
Definition acc : string := "acc".

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Hint Unfold f : core.
Hint Unfold l : core.
Hint Unfold l' : core.
Hint Unfold acc : core.

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  (* list *)
  | v_lnil : forall T1, value <{nil T1}>
  | v_lcons : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{v1 :: v2}>.

Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
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

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
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
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
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

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Extern 2 (_ = _) => compute; reflexivity : core.

(* example *)

Definition andb := <{\x:Bool,\y:Bool,if x then y else false}>.

(*
  tail_recursion0 = 
    \l:list bool, \acc:bool, 
      case l of
      | nil : acc
      | b::l' : tail_recursion l' (if b then acc else false)
*)

(* 

  list = [true,true]

  tail recursion version:

    Definition tail_recursion0 := 
      <{fix 
          (\f:Bool->Bool->Bool,
              \l:List Bool, \acc:Bool, 
                case l of
                | nil => acc
                | x::l' => f l' (if x then acc else false)
          )}>. 

  non tail recursion version:

    Definition not_tail_recursion :=
      <{fix
        (\f:,
          \l:List Bool,
            case l of
        
        )}>
*)
Definition list := <{true::true::(nil Bool)}>.

Definition tail_recursion := 
  <{fix 
      (\f:List Bool->Bool->Bool,
          \l:List Bool, \acc:Bool,
            case l of
            | nil => acc
            | x::l' => f l' (if x then acc else false)
      )}>.

Definition not_tail_recursion := 
  <{fix
      (\f:List Bool->Bool,
        \l:List Bool,
          case l of
          | nil => true
          | x::l' => if x then (f l') else false
      )}>.

Lemma tail_reduction: <{tail_recursion list true}> -->* <{true}>.
Proof.
  unfold tail_recursion, list. (* normalize. *)
  (* 1 *)
  eapply multi_step.
    eapply ST_App1.
      eapply ST_App1.
        eapply ST_FixAbs. simpl.
  eapply multi_step.
    eapply ST_App1.
      eapply ST_AppAbs;auto. simpl.
  eapply multi_step.
    eapply ST_AppAbs;auto. simpl.
  eapply multi_step.
    eapply ST_LcaseCons;auto. simpl.
  (* 2 *)
  eapply multi_step.
    eapply ST_App1.
      eapply ST_App1.
        eapply ST_FixAbs. simpl.
  eapply multi_step.
    eapply ST_App1.
      eapply ST_AppAbs; auto. simpl.
  eapply multi_step.
    eapply ST_App2;auto.
  eapply multi_step.
    eapply ST_AppAbs;auto. simpl.
  eapply multi_step.
    eapply ST_LcaseCons;auto. simpl.
  (* 3 *)
  eapply multi_step.
    eapply ST_App1.
      eapply ST_App1.
        eapply ST_FixAbs. simpl.
  eapply multi_step.
    eapply ST_App1.
      eapply ST_AppAbs; auto. simpl.
  eapply multi_step.
    eapply ST_App2;auto.
  eapply multi_step.
    eapply ST_AppAbs;auto. simpl.
  eapply multi_step.
    eapply ST_LcaseNil.
  apply multi_refl.
Qed.

Lemma not_tail_reduction: <{not_tail_recursion list}> -->* <{true}>.
Proof.
  unfold not_tail_recursion,list.
  eapply multi_step.
    eapply ST_App1.
      eapply ST_FixAbs. simpl.
  eapply multi_step.
    eapply ST_AppAbs;auto. simpl.
  eapply multi_step.
    eapply ST_LcaseCons;auto. simpl.
  (* ... *)
  normalize.
Qed.




