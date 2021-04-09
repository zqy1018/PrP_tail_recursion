Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From TRO Require Import Maps.
From TRO Require Import Smallstep.

(* a simple mystlc that only has nat types and supports list, fix and add operation*)

Inductive tm : Type :=
  | tm_invalid : tm
  (* pure mystlc *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> tm -> tm
  (* numbers *)
  | tm_const: nat -> tm
  | tm_add : tm -> tm -> tm
  (* lists *)
  | tm_nil :  tm
  | tm_cons : tm -> tm -> tm
  | tm_lcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., [case t1 of | nil => t2 | x::y => t3] *)
  (* fix *)
  | tm_fix  : tm -> tm.

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
Notation "x + y" := (tm_add x y) (in custom mystlc at level 1,
                                      left associativity).
(* Notation "'Nat'" := Ty_Nat (in custom mystlc at level 0). *)
Coercion tm_const : nat >-> tm.

(* Notation "'List" :=
  (Ty_List T) (in custom mystlc at level 4). *)
Notation "'nil'" := (tm_nil) (in custom mystlc at level 0).
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
  | v_abs : forall x t1,
      value (tm_abs x t1)
  (* Numbers are values: *)
  | v_nat : forall n : nat,
      value <{n}>
  (* list *)
  | v_lnil : value <{nil}>
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
  | tm_abs y t1 =>
      if eqb_string x y then t else tm_abs y (subst x s t1)
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{t1 + t2}> =>
      <{ ([x:=s] t1) + ([x:=s] t2) }>
  (* lists *)
  | <{nil}> =>
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
  | ST_AppAbs : forall x t1 v2,
         value v2 ->
         <{ {tm_abs x t1} v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  (* numbers *)
  | ST_Addconsts: forall n1 n2 : nat,
         <{n1 + n2}> --> <{ {n1 + n2} }>
  | ST_Add1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 + t2}> --> <{t1' + t2}>
  | ST_Add2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 + t2}> --> <{v1 + t2'}>
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
  | ST_LcaseNil : forall t2 x1 x2 t3,
       <{case nil of | nil => t2 | x1 :: x2 => t3}> --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       <{case v1 :: vl of | nil => t2 | x1 :: x2 => t3}>
         -->  <{ [x2 := vl] ([x1 := v1] t3) }>
  (* fix *)
  | ST_Fix1 : forall t1 t1',
       t1 --> t1' ->
       <{fix t1}> --> <{fix t1'}>
  | ST_FixAbs : forall xf t1,
       <{fix ({tm_abs xf t1}) }> --> <{[xf:=fix ({tm_abs xf t1})] t1}>
  where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

Definition x : string := "x".
Definition invalid_string : string := "invalid".

Definition y : string := "y".
Definition z : string := "z".
Definition k : string := "k".
Definition u : string := "k".
Definition s : string := "s".
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
Hint Unfold k : core.
Hint Unfold s : core.
Hint Unfold s1 : core.
Hint Unfold s2 : core.
Hint Unfold s3 : core.
Hint Unfold s4 : core.
Hint Unfold f : core.
Hint Unfold l : core.
Hint Unfold l' : core.
Hint Unfold acc : core.

(* take in a nat and generate a variable name with n "a"s *)
Fixpoint create_new_name (n:nat) : string :=
  match n with
  | O => EmptyString
  | S n => "a" ++ (create_new_name n)
  end.

(* combine left tree continuation with right tree continuation *)
Fixpoint combine (l r : tm) :=
  match l with 
  | (tm_app (tm_app f l') (tm_abs s next_l)) => (tm_app (tm_app f l') (tm_abs s (combine next_l r)))
  | _ => r
  end.

(* take in a term and return 
  (recursive calls order and args,
    expression tree with recursive calls substituted by new variable names,
      recursive call counts) *)
Fixpoint to_cont_helper (t:tm) (calls:nat) :=
  match t with
  (* exp tree(inductively defined) *)
  | (tm_add lt rt) =>
      (* construct left exp tree *)
      match (to_cont_helper lt calls) with 
      | (l_cont, (l_exp, l_ret_calls)) => 
          (* construct right exp tree *)
          match (to_cont_helper rt l_ret_calls) with
          | (r_cont, (r_exp, r_ret_calls)) => (combine l_cont r_cont, (tm_add l_exp r_exp, r_ret_calls))
          end
      end
  | (tm_cons lt rt) =>
      (* construct left exp tree *)
      match (to_cont_helper lt calls) with 
      | (l_cont, (l_exp, l_ret_calls)) => 
          (* construct right exp tree *)
          match (to_cont_helper rt l_ret_calls) with
          | (r_cont, (r_exp, r_ret_calls)) => (combine l_cont r_cont, (tm_cons l_exp r_exp, r_ret_calls))
          end
      end
  (* recursive call *)
  | (tm_app f l') => 
    let new_name := create_new_name calls in (<{f l' (\new_name,new_name)}>, ((tm_var new_name), S calls))
  (* reach leaf *)
  | (tm_const n) => (tm_const n,(tm_const n, calls))
  | (tm_var s) => (tm_var s,(tm_var s,calls))
  | _ => (tm_invalid,(tm_invalid, 100))
  end.

(* extract args from to_cont_helper and construct the final result *)
Definition to_cont (t:tm) := 
  match (to_cont_helper t 1) with
  | (l_cont,(exp,_)) => combine l_cont (tm_app (tm_var k) exp)
  end.

Definition to_tail(t:tm) := 
  match t with
  | tm_fix (tm_abs f
            (tm_abs l
              (tm_lcase _ init_t _ _ not_cont))) =>
                let cont :=<{fix 
                            (\f, \l, \k,
                                case l of
                                | nil => k init_t
                                | x::l' => {to_cont not_cont}
                            )}> in
                <{\l, cont l <{\s,s}>}>
  | _ => tm_invalid
  end.

Definition list := <{3::2::nil}>.

Definition not_tail_right := 
  <{fix
      (\f,
        \l,
          case l of
          | nil => 0
          | x::l' => x + (f l')
      )}>.

Theorem proof_to_tail_right: <{ {to_tail not_tail_right} list }> -->* <{5}>.
Proof.
  unfold not_tail_right,list. simpl.
  normalize.
Qed.

Definition not_tail_left := 
  <{fix
      (\f,
        \l,
          case l of
          | nil => 0
          | x::l' => (f l') + x
      )}>.

Theorem proof_to_tail_left: <{ {to_tail not_tail_left} list}> -->* <{5}>.
Proof.
  unfold not_tail_left,list. simpl.
  normalize.
Qed.

Definition not_tail_both := 
  <{fix
      (\f,
        \l,
          case l of
          | nil => 1
          | x::l' => (f l') + (f l')
      )}>.

Theorem proof_to_tail_both: <{ {to_tail not_tail_both} list}> -->* <{4}>.
Proof.
  unfold not_tail_both,list. simpl.
  normalize.
Qed.

Definition not_tail_nested0 := 
  <{fix
      (\f,
        \l,
          case l of
          | nil => 1
          | x::l' => ((f l') + (f l')) + ((f l') + (f l'))
      )}>.

Theorem proof_to_tail_nested0: 
  <{ {to_tail not_tail_nested0} list}> -->* <{16}>.
Proof.
  unfold not_tail_nested0,list. simpl.
  normalize.
Qed.

Definition not_tail_nested1 := 
  <{fix
      (\f,
        \l,
          case l of
          | nil => 1
          | x::l' => (x + (f l')) + ((f l') + x)
      )}>.

Theorem proof_to_tail_nested1: 
  <{ {to_tail not_tail_nested1} list}> -->* <{18}>.
Proof.
  unfold not_tail_nested1,list. simpl. unfold to_cont. simpl.
  normalize.
Qed.


(* what if 5 is a variable? *)
Definition not_tail_list := 
  <{fix
      (\f,
        \l,
          case l of
          | nil => nil
          | x::l' => (x + 5)::(f l')
      )}>.

Theorem huhu : <{ {to_tail not_tail_list} list}> -->* <{8::7::nil}>.
Proof.
  unfold not_tail_list,list. simpl.
  normalize.
Qed.


