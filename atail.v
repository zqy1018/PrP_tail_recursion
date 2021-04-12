Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Frap Require Import Maps.
From Frap Require Import Smallstep.

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
      <{ ([x:=s] t1) :: [x := s] t2 }>
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
  
  | ST_invalid : <{tm_invalid}> --> <{tm_invalid}>
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

Compute (to_tail not_tail_right).

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

Compute (to_tail not_tail_left).

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

Compute (to_tail not_tail_nested0).

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

(*Reserved Notation "x '=b' y" (in custom mystlc at level 20, x constr).
*)
Inductive beta_eq: tm -> tm -> Prop :=
  | M_id : forall M,
      beta_eq M M
  | M_rapply : forall M M1 M2,
      beta_eq M1 M2 -> beta_eq (tm_app M1 M) (tm_app M2 M)
  | M_lapply : forall M M1 M2,
      beta_eq M1 M2 -> beta_eq (tm_app M M1) (tm_app M M2)

  | M_Addconsts: forall n1 n2 : nat,
      beta_eq <{n1 + n2}> <{ {n1 + n2} }>
  | M_rplus : forall M M1 M2,
      beta_eq M1 M2 -> beta_eq (tm_add M1 M) (tm_add M2 M)
  | M_lplus : forall M M1 M2,
      beta_eq M1 M2 -> beta_eq (tm_add M M1) (tm_add M M2)
  | M_rcons : forall M M1 M2,
      beta_eq M1 M2 -> beta_eq (tm_cons M1 M) (tm_cons M2 M)
  | M_lcons : forall M M1 M2,
      beta_eq M1 M2 -> beta_eq (tm_cons M M1) (tm_cons M M2)
  
  
  | M_Lcase1 : forall t1 t1' t2 x1 x2 t3,
      beta_eq t1 t1' ->
      beta_eq <{case t1 of | nil => t2 | x1 :: x2 => t3}>
      <{case t1' of | nil => t2 | x1 :: x2 => t3}>
  | M_LcaseNil : forall t2 x1 x2 t3,
      beta_eq <{case nil of | nil => t2 | x1 :: x2 => t3}> t2
  | M_LcaseCons : forall v1 vl t2 x1 x2 t3,
      value v1 ->
      value vl ->
      beta_eq <{case v1 :: vl of | nil => t2 | x1 :: x2 => t3}>
         <{ [x2 := vl] ([x1 := v1] t3) }>


  | M_subs : forall x e e1,
      beta_eq <{ {tm_abs x e} e1 }> <{ [ x := e1 ] e }>
  | M_lam : forall M,
      beta_eq <{\x,M}> <{\y,[x:=y]M}>

  
  | M_Fix1 : forall t1 t1',
      beta_eq t1 t1' ->
      beta_eq <{fix t1}>  <{fix t1'}>
  | M_FixAbs : forall xf t1,
      beta_eq <{fix ({tm_abs xf t1}) }> <{[xf:=fix ({tm_abs xf t1})] t1}>
 

  | M_comm : forall M1 M2,
      beta_eq M1 M2 -> beta_eq M2 M1
  | M_trans : forall M1 M2 M3,
      beta_eq M1 M2 -> beta_eq M2 M3 -> beta_eq M1 M3

  .
  
  (*where "x '=b' y'" := (beta_eq x y).*)
Hint Constructors beta_eq : core.

Require Export FrapWithoutSets.

Module Export SN := SetNotations(FrapWithoutSets).

Theorem beta_st_eqv1: forall M1 M2, M1 --> M2 -> beta_eq M1 M2.
Proof.
  eauto.
  (*inversion H.
  - apply M_subs with (x:=x0).
  - apply M_rapply. induction t1;inversion H0;econstructor.
    + *)
 (*
  induction M1.
  - inversion H. econstructor.
  - inversion H.
  -  inversion H.
  inversion H.*)
  induct M1;intros;inversion H;econstructor;subst.
  - apply IHM1_1. apply H3.
  - apply IHM1_2. apply H4.
  - apply IHM1_1. apply H3.
  - apply IHM1_2. apply H4.
  - apply IHM1_1. apply H3.
  - apply IHM1_2. apply H4. 
  - apply IHM1_1. apply H6.
  - apply H6.
  - apply H7.
  - apply IHM1. apply H1.

Qed. 
 (* induct M1;inversion H;econstructor;subst.
  (* beta_eq <{ M1_1 M1_2 }> M2 *)
  - subst. rewrite H0. rewrite H1. clear H0 H1 H2.
  (*print_goal.
   eapply multi_step in H ;
  [ (eauto 10; fail) | (instantiate; simpl)].*)
  admit.
  (* beta_eq <{ M1_1 M1_2 }> <{ t1' M1_2 }> *)
  - subst. admit.
  (* beta_eq <{ M1_1 M1_2 }> <{ M1_1 t2' }> *)
  - subst. admit.
  (* beta_eq <{ n1 + n2 }> (n1 + n2) *)
  - subst. admit.
  (* beta_eq <{ M1_1 + M1_2 }> <{ t1' + M1_2 }> *)
  - subst. admit.
  (* beta_eq <{ M1_1 + M1_2 }> <{ M1_1 + t2' }> *)
  - subst. admit.
  (* beta_eq <{ M1_1 :: M1_2 }> <{ t1' :: M1_2 }> *)
  - subst. admit.
  (* beta_eq <{ M1_1 :: M1_2 }> <{ M1_1 :: t2' }> *)
  - subst. admit.
  

  (* case t1' of *)
  - subst. admit.
  (* <{ case nil of | nil => M2 | s0 :: s5 => M1_3 }> --> M2 *)
  - subst. admit. 
  (* <{ case v1 :: vl of | nil => M1_2 | s0 :: s5 => M1_3 }> -->
    <{ [s5 := vl] ([s0 := v1] M1_3) }> *)
  - subst. admit.
  (* beta_eq (tm_fix M1) (tm_fix t1') *)
  - subst. admit.
  (* beta_eq (tm_fix M1) M2 *)
  - rewrite H1. rewrite H1 in H0. rewrite H0. admit.
  (*
  induction M1,M2;inversion H.
  - apply M_id.

  - rewrite H3. rewrite H0. clear H3 H0 H2.  (*H*) admit.
  - rewrite H3. rewrite H0. clear H3 H0 H2.  (*H*) admit.
  - rewrite H3. rewrite H0. clear H3 H0 H2.  (*H*) admit.

  - subst. econstructor. (*H1*) admit.
  - subst. econstructor. admit.
  
  - rewrite H3. rewrite H0. clear H3 H0 H2. (*H*) admit.
  - rewrite H3. rewrite H0. clear H3 H0 H2. (*H*) admit.
  - rewrite H3. rewrite H0. clear H3 H0 H2. (*H*) admit.
  - rewrite H3. rewrite H0. clear H3 H0 H2. (*H*) admit.
  - rewrite H3. rewrite H0. clear H3 H0 H2. (*H*) admit.
  - rewrite H3. rewrite H0. clear H3 H0 H2. (*H*) admit.
  - rewrite H3. rewrite H0. clear H3 H0 H2. (*H*) admit.

  - subst.  admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
*)
Admitted.*)

Theorem beta_st_eqv: forall M1 M2, M1 -->* M2 -> beta_eq M1 M2.
Proof.
  intros. induction H.
  - econstructor.
  - apply beta_st_eqv1 in H. apply M_trans with (M2:=y0).
    assumption. assumption.
Qed.

Theorem beta_st_eqv_church: forall M1 M2 M3, M1 -->* M3 -> M2 -->* M3 -> beta_eq M1 M2.
Proof.
  intros. 
  induction H,H0.
  - econstructor.
  - apply M_trans with (M2:=y0).
    + econstructor. apply beta_st_eqv. assumption.
    + econstructor. apply beta_st_eqv1. assumption.
  - apply M_trans with (M2:=y0).
    + apply beta_st_eqv1. assumption.
    + apply beta_st_eqv. assumption.
  - apply M_trans with (M2:=y0).
    + apply beta_st_eqv1. assumption.
    + apply IHmulti. apply multi_step with (y:=y1).
      assumption. assumption.
Qed.

(*
  induction H.
  - econstructor. apply beta_st_eqv. assumption.
  - induction H1. 
    + apply M_trans with (M2:=x1). 
      * apply beta_st_eqv1. assumption.
      * apply IHmulti. assumption.
    + apply IHmulti0.
      * 
      * assumption.
      * intros. apply IHmulti in H3. apply M_trans with (M2:=x1).
        econstructor. apply beta_st_eqv1. assumption.
        assumption. 
Qed. *)