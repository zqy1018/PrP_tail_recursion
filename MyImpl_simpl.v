Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Smallstep.
From Coq Require Import Strings.String.
From Coq Require Export Lia.
From PLF Require Import LibTactics.

Inductive op : Type :=
 | Oplus
 | Ominus
 | Omult
 .

Inductive tm : Type :=
 | var : string -> tm
 | app : tm -> tm -> tm
 | abs : string -> tm -> tm
 
 | nat_const : nat -> tm
 | op_const : op -> tm
 | test0 : tm -> tm -> tm -> tm 
 
 | tlet : string -> tm -> tm -> tm
  
 | tfix : tm -> tm
.
Coercion var: string >-> tm.
Coercion nat_const: nat >-> tm.
Coercion op_const: op >-> tm.
Fixpoint subst (x : string) (s: tm) (t:tm) :tm :=
  match t with
  | var y =>   
          if eqb x y then s else t
  | app t1 t2 =>
          app (subst x s t1) (subst x s t2)
  | abs y t1 => 
          if eqb x y then (abs y t1) else (abs y (subst x s t1))
  | nat_const n =>
          nat_const n
  | op_const o => 
          op_const o
  | test0 t1 t2 t3 =>
          test0 (subst x s t1) (subst x s t2) (subst x s t3)
  | tlet y t1 t2 => 
          tlet y (subst x s t1) (if eqb x y then t2 else (subst x s t2))      
  | tfix t1 =>
          tfix (subst x s t1) 
end.

(* have_string x t = true => t中有自由变量x *)
Fixpoint have_string (x : string) (t:tm) :bool :=
  match t with
  | var y =>   
          if eqb x y then true else false
  | app t1 t2 => if (have_string x t1) 
                  then true 
                  else have_string x t2
  | abs y t1 => 
          if eqb x y then false else have_string x t1
  | nat_const n => false
  | op_const n => false
  | test0 t1 t2 t3 => if (have_string x t1) 
                  then true 
                  else if (have_string x t2)
                      then true
                      else have_string x t3
  | tlet y t1 t2 => if eqb x y 
                      then have_string x t1
                      else if (have_string x t1) 
                          then true 
                          else have_string x t2
  | tfix t1 => have_string x t1
end.

Lemma have_string_lemma : forall (F:string) (M1 M2: tm),
  have_string F (app M1 M2) = false -> have_string F M1 = false /\ have_string F M2 = false.
Proof.
  intros.
  simpl in H.
  destruct (have_string F M1);destruct (have_string F M2);auto.
Qed.

Reserved Notation "g '|--' t" (at level 40).
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* G |-- t => 若t中有自由变元，则一定属于G，换句话说，忽略t中的来自G的变元，t就是close term*)
Inductive close_form (G:list string): tm -> Prop:=
  | close_natconst n: G |-- (nat_const n)
  | close_opconst o: G |-- (op_const o)
  | close_string (s:string) (H: List.In s G): G |-- s
  | close_abs x t (H:(x::G) |-- t): G |-- abs x t
  | close_app t1 t2 (H: G |-- t1)(H2: G |-- t2) : G |-- app t1 t2 
  | close_let x t1 t2 (H1: (x::G) |-- t2) (H2: G |-- t1): G |-- tlet x t1 t2
  | close_test0 t1 t2 t3 (H1: G |-- t1)(H2: G |-- t2) (H3: G |-- t3) : G |-- test0 t1 t2 t3
  | close_fix t (H: G |-- t): G |-- tfix t
where "G '|--' t" := (close_form G t).
Hint Constructors close_form. 
Hint Unfold List.In.


Notation "t1 '+' t2" := (app(app Oplus t1) t2).
Notation "t1 '*' t2" := (app(app Omult t1) t2).
Notation "t1 '-' t2" := (app(app Ominus t1) t2).
Inductive halt : tm -> Prop :=
  | h_abs : forall x t,
      halt (abs x t)
  | h_natconst : forall n,
      halt (nat_const n)
  | h_opconst : forall o,
      halt (op_const o)
  | h_plus : forall n,
      halt (app Oplus (nat_const n))
  | h_minus : forall n,
      halt (app Ominus (nat_const n))
  | h_mult : forall n,  
      halt (app Omult (nat_const n))
(*   | h_lnil : forall T, 
      halt (tnil T)
  | h_lcons : forall v1 vl,
      halt v1 ->
      halt vl ->
      halt (tcons v1 vl) *)
.
Hint Constructors halt. 


Inductive multi2 {X : Type} (R : relation X) : relation X :=
  | multi_refl2 : forall (x : X), multi2 R x x
  | multi_step2 : forall (x y : X),
                    R x y ->
                    multi2 R x y
  | multi_trans2 : forall (x y z : X),
                    multi2 R x y ->
                    multi2 R y z ->
                    multi2 R x z
  | multi_symm2 : forall (x y : X),
                    multi2 R x y ->
                    multi2 R y x.
Hint Constructors multi2. 
(*  *)
Inductive beta_step : tm -> tm -> Prop :=
  (* pure STLC *)
  | ST_AppAbs : forall x t1 h2,
         (* halt h2 ->  *)
         nil |-- h2 ->
         app (abs x t1) h2 --> subst x h2 t1
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         app t1 t2 --> app t1' t2
  | ST_App2 : forall h1 t2 t2',
         (* halt h1 -> *)
         t2 --> t2' ->
         app h1 t2 --> app h1 t2'
  | ST_AppAb : forall x M1 M2,
         M1 --> M2 -> abs x M1 --> abs x M2
  | ST_Fix1 : forall t1 t1',
              t1 --> t1' ->
              tfix t1 --> tfix t1'
  | ST_Fix2 : forall f t1,
              nil |-- tfix (abs f t1) ->
              tfix (abs f t1) --> subst f (tfix (abs f t1)) t1 
  | ST_Test01 : forall t1 t1' t2 t3,
              t1 --> t1' ->
              test0 t1 t2 t3 --> test0 t1' t2 t3
  | ST_Test02 : forall t1 t2 t2' t3,
              t2 --> t2' ->
              test0 t1 t2 t3 --> test0 t1 t2' t3
  | ST_Test03 : forall t1 t2 t3 t3',
              t3 --> t3' ->
              test0 t1 t2 t3 --> test0 t1 t2 t3'             
  | ST_Test0Zro : forall t2 t3,
              (test0 0 t2 t3) --> t2
  | ST_Test0NotZro : forall n t2 t3,
              (test0 (S n) t2 t3) --> t3
  | ST_Let1 : forall x t1 t2 t1',
              t1 --> t1' ->
              (tlet x t1 t2) --> (tlet x t1' t2)
  | ST_Let2 : forall x t1 t2 t2',
              t2 --> t2' ->
              (tlet x t1 t2) --> (tlet x t1 t2')
  | ST_LetValue : forall x h1 t2,
              (* halt h1 -> *)
              nil |-- h1 ->
              (tlet x h1 t2) --> (subst x h1 t2)
  | ST_Minconsts : forall n1 n2:nat,
              (app(app Ominus n1) n2) --> (n1 - n2)
  | ST_Plusconsts : forall n1 n2:nat,
              (app(app Oplus n1) n2) --> (n1 + n2)
  | ST_Multconsts: forall n1 n2:nat,
              (app(app Omult n1) n2) --> (n1 * n2)
  where "t '-->' t'" := (beta_step t t').
Hint Constructors beta_step. 

Notation multi_beta_step := (multi2 beta_step).
Notation "t1 '-->*' t2" := (multi_beta_step t1 t2) (at level 40).

Reserved Notation "t1 '=b' t2" (at level 40).

Inductive beta_equiv :tm -> tm -> Prop:=
  | beta_refl x: x =b x 
  | beta_symm x y: x =b y -> y =b x
  | beta_trans x y z: x =b y -> y =b z -> x =b z
  | beta_l t1 t1' t2: t1 =b t1' -> app t1 t2 =b app t1' t2
  | beta_r t1 t2 t2': t2 =b t2' -> app t1 t2 =b app t1 t2' 
  | beta_appabs x t h:
                nil |-- h->
                (app (abs x t) h) =b (subst x h t)
  | beta_abs x t t':
                t =b t' ->
                abs x t =b abs x t'
  | beta_fix1 t1 t1': t1 =b t1' -> tfix t1 =b tfix t1'
  | beta_fixabs f t2:
              nil |-- tfix(abs f t2) -> 
              tfix (abs f t2) =b subst f (tfix (abs f t2)) t2 
  | beta_test01: forall t1 t1' t2 t3,
              t1 =b t1' ->
              (test0 t1 t2 t3) =b (test0 t1' t2 t3)
  | beta_test02: forall t1 t2 t2' t3,
              t2 =b t2' ->
              (test0 t1 t2 t3) =b (test0 t1 t2' t3)
  (* add test0zro and test0nonzro *)
  | beta_test0Zro: forall t2 t3,
              test0 0 t2 t3 =b t2
  | beta_test0NonZro: forall n t2 t3,
              test0 (S n) t2 t3 =b t3

  | beta_test03: forall t1 t2 t3 t3',
              t3 =b t3' ->
              (test0 t1 t2 t3) =b (test0 t1 t2 t3')
  | beta_let1 : forall x t1 t2 t1',
              t1 =b t1' ->
              (tlet x t1 t2) =b (tlet x t1' t2)
  | beta_let2 : forall x t1 t2 t2',
              t2 =b t2' ->
              (tlet x t1 t2) =b (tlet x t1 t2')
  | beta_letvalue : forall x h1 t2,
              nil |-- h1->
              (tlet x h1 t2) =b (subst x h1 t2)
where "t1 '=b' t2" := (beta_equiv t1 t2).
Hint Constructors beta_equiv. 

Lemma beta_rl : forall t1 t1' t2 t2',
  t1 =b t1' ->
  t2 =b t2' ->
  app t1 t2 =b app t1' t2'.
Proof.
  intros.
  eapply beta_trans.
  - apply beta_l. apply H.
  - eapply beta_trans. apply beta_r. apply H0.
  apply beta_refl.
  Qed.

Lemma beta_let : forall x t1 t1' t2 t2',
  t1 =b t1' ->
  t2 =b t2' ->
  (tlet x t1 t2) =b (tlet x t1' t2').
Proof.
  intros.
  eapply beta_trans.
  apply beta_let1.
  apply H.
  auto.
Qed.

Lemma beta_test0 : forall t1 t1' t2 t2' t3 t3',
  t1 =b t1' ->
  t2 =b t2' ->
  t3 =b t3' ->
  (test0 t1 t2 t3) =b (test0 t1' t2' t3').
Proof.
  intros.
  eapply beta_trans.
  apply beta_test01.
  apply H.
  eapply beta_trans.
  apply beta_test02.
  apply H0.
  auto.
Qed.

Hint Resolve beta_rl. 
Hint Resolve beta_let. 
Hint Resolve beta_test0. 


Open Scope string_scope.
Definition x := "x".
Definition y := "y".
Definition z := "z".
Definition f := "f".
Definition c := "c".
Definition k := "k".
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.
Hint Unfold f.
Hint Unfold c.
Hint Unfold k.

(* Theorem halt_lemma: forall t,
  [] |-- t ->
  exists h, halt h /\ t -->* h.
Proof.
  intros.
  induction t;inversion H.
  - simpl in H1. destruct H1.
  - subst. apply IHt1 in H1. apply IHt2 in H3.
    destruct H1. destruct H3. destruct H0. destruct H1.
    inversion H0.
    + subst. admit.
    +  
  - subst. exists (abs s t). split;auto.
  - exists n. split;auto.
  - exists o. split;auto.
  - subst. simpl in H0. destruct H0.
  - exists t. subst. split;auto.
  - exists t. subst. split;auto.

Qed. *)


Theorem one_step_to_beta_eq: forall M1 M2, M1 --> M2 -> M1 =b M2.
Proof.
  intros.
  induction H;auto.
Qed.

Theorem step_to_beta_eq: forall M1 M2, M1 -->* M2 -> M1 =b M2.
Proof.
  intros.
  induction H;auto.
  - apply one_step_to_beta_eq in H;eauto.
  - eauto.
Qed.

Hint Resolve step_to_beta_eq.

Theorem beta_eq_to_step: forall M1 M2, M1 =b M2 -> M1 -->* M2.
Proof.
  intros.
  induction H;auto;eauto;induction IHbeta_equiv;auto;eauto 8.
Qed.  


Definition is_var_F (F:string) (m:tm):=
  match m with
  | var f => if eqb f F
              then true
              else false
  | _ => false
  end.

Fixpoint trans_M (F:string)(k t:tm) :=
    match (have_string F t) with
    | false => app k t
    | true => match t with 
               (* F m => F' m k  *)
              (* | app (var f) m => 
                      if eqb f F
                      then app (app F m) k
                      else app k t *)
              | app m1 m2 => 
                    if have_string F m1 
                    then if is_var_F F m1 
                      then app (app F m2) k
                      else if have_string F m2
                            then
                              tlet "s1" 
                                (abs "res1"
                                  (tlet "s2"
                                    (abs "res2" (app k (app "res1" "res2")))
                                    (trans_M F "s2" m2)))
                                (trans_M F "s1" m1)
                            else
                                tlet "s1"
                                  (abs "res1" (app k (app "res1" m2)))
                                (trans_M F "s1" m1)
                    else if have_string F m2
                          then
                              tlet "s1"
                                (abs "res1" (app k (app m1 "res1")))
                              (trans_M F "s1" m2)
                          else 
                            app k t
              | _ => app k t
              end
    end.

    
Definition trans_to_tail_recursion (F:tm):=
    match F with
    | tfix (abs f
            (abs a t )) => match t with
                            | test0 t1 t2 t3 => tfix (abs f
                                                (abs a 
                                                    (abs "k"
                                                    (test0 t1
                                                        (app "k" t2)
                                                        (trans_M f "k" t3 )))))
                            | _ => F
                            end
    | _ => F
    end.

(* Notation multib := (multi beta_equiv).

Theorem multib_eq_be : forall (t1 t2:tm),
    multib t1 t2 <-> t1 =b t2.
Proof.
    split; intros.
    * induction H.  
    - apply beta_refl.
    - apply (beta_trans x0 y0 z0).
        + apply H.
        + apply IHmulti.
    * eapply multi_step.
    apply H. eapply multi_refl.
    Qed.

Theorem multib_comm : forall (t1 t2:tm),
  multib t1 t2 -> multib t2 t1.
Proof.
  intros.
  apply multib_eq_be. apply multib_eq_be in H.
  apply beta_symm. apply H.
  Qed. *)

(* 符合转化函数分支的形式 *)
Inductive match_subtm (F:string): tm -> Prop:=
  | match_natconst n: match_subtm F (nat_const n)
  | match_string (s:string) (H:eqb F s = false): match_subtm F s 
  | match_appF m(H:have_string F m = false) (H2:match_subtm F m): match_subtm F (app F m) 
  | match_app m1 m2 (H1: have_string F m1 = false) (H2:match_subtm F m2): match_subtm F (app m1 m2) 
  | match_app2 m1 m2 (H1: have_string F m1 = true) (H2: match_subtm F m1) (H3: match_subtm F m2) : match_subtm F (app m1 m2)
.
Hint Constructors match_subtm.

Lemma close_lemma1: forall (t1 t2:tm) (G:list string),
  G |-- app t1 t2 -> G |-- t1 /\ G |-- t2
.
Proof.
  intros.
  inversion H.
  auto.
  Qed.

Lemma close_lemma2: forall (t1 t2:tm) (G:list string) (x:string),
  G |-- (abs x (app t1 t2)) -> (x::G) |-- t1 /\ (x::G) |-- t2
.
Proof.
  intros.
  inversion H.
  subst.
  apply close_lemma1 in H1.
  apply H1.
  Qed.    

 
Lemma cons_lemma : forall (x:string) (l1 l2:list string),
  (x :: l1 ++ l2)%list = ((x :: l1) ++ l2)%list.
Proof. 
  intros.
  assert(H: (x0 :: l1 ++ l2)%list = ([x0] ++ l1 ++ l2)%list).
  {simpl. reflexivity. }
  rewrite H. rewrite (List.app_assoc [x0] l1 l2). simpl. reflexivity.
  Qed.

Lemma close_lemma3: forall (t:tm) (l1 l2 G:list string),
  (G++l1++l2)%list |-- t -> (G++l2++l1)%list |-- t.
Proof.
  intro t.
  induction t;intros;try auto.
  - apply close_string. inversion H.
    simpl in H1. simpl. apply List.in_app_or in H1. apply List.in_or_app. destruct H1.
    + auto.
    + apply List.in_app_or in H1. right. apply List.in_or_app. destruct H1; try auto.
  - apply close_lemma1 in H. destruct H. apply close_app; auto.
  - apply close_abs. inversion H. subst. 
    rewrite cons_lemma in H1. apply IHt in H1. auto. 
  - inversion H. apply close_test0;auto. 
  - inversion H. apply close_let. 
    + subst. rewrite cons_lemma in H0. apply IHt2 in H0. auto.
    + auto.
  - inversion H. auto.
  Qed.

Lemma close_lemma4: forall (t:tm) (x:string) (G:list string) ,
  G |-- t -> (x::G) |-- t.
Proof.
  induction t;intros;inversion H;subst;try auto.
  - apply close_abs. 
    assert(H2: ([s] ++ [x0] ++ G)%list = (s::x0::G) ).
    {simpl. reflexivity. }
    rewrite <- H2. apply close_lemma3. rewrite List.app_assoc. 
    assert(H4: (([s] ++ G) ++ [x0])%list = ([] ++ ([s] ++ G) ++ [x0])%list).
    {simpl. reflexivity. }
    rewrite H4. apply close_lemma3. simpl. auto.
  - apply close_let. 
    + assert(H2: ([s] ++ [x0] ++ G)%list = (s::x0::G) ).
    {simpl. reflexivity. }
    rewrite <- H2. apply close_lemma3. rewrite List.app_assoc. 
    assert(H5: (([s] ++ G) ++ [x0])%list = ([] ++ ([s] ++ G) ++ [x0])%list).
    {simpl. reflexivity. }
    rewrite H5. apply close_lemma3. simpl. auto.
    + auto.
  Qed.  


Lemma close_lemma5: forall (t:tm)(F:string) (G:list string) ,
  G |-- t -> ~ List.In F G -> have_string F t = false.
Proof.
  induction t;intros; inversion H;subst;auto.
  - simpl. destruct(eqb_spec F s).
    + subst. congruence. 
    + reflexivity. 
  - apply (IHt1 F G) in H3. 
    + apply (IHt2 F G) in H4. 
      * simpl. rewrite H3. auto.
      * auto.
    + auto.
  - simpl. destruct (eqb_spec F s).
    + reflexivity.
    + apply (IHt F (s::G)). 
      * auto.
      * unfold not. intros. simpl in H1. destruct H1.
        ** congruence.
        ** congruence.
  - simpl. 
    apply (IHt1 F G) in H4;
    apply (IHt2 F G) in H5;
    apply (IHt3 F G) in H6;auto.
    rewrite H4. rewrite H5. auto.
  - simpl. destruct (eqb_spec F s).
    + apply (IHt1 F G);auto.
    + apply (IHt1 F G) in H5;
      apply (IHt2 F (s::G)) in H3;
      auto.
      * rewrite H3. rewrite H5. reflexivity.
      * unfold not. intros. simpl in H1. destruct H1; try congruence.
      * unfold not. intros. simpl in H1. destruct H1; try congruence.
  - simpl. apply (IHt F G); auto.
  Qed.      

Lemma close_lemma6: forall (t: tm) (F:string),
  nil |-- t -> have_string F t = false.
Proof.
  intros.
  apply (close_lemma5 t F nil).
  
  - auto.
  - simpl. unfold not. intros. auto. 
  Qed.

Lemma subst_lemma1 : forall (f t: tm) (F:string), 
  (have_string F f) = false -> subst F t f =b f.
Proof.
  intros.
  induction f0.
  - simpl. simpl in H. destruct (F =? s ) eqn:E1. 
    + discriminate.
    + apply beta_refl.
  - simpl. eapply beta_trans. apply beta_l. apply IHf0_1. simpl in H. destruct (have_string F f0_1) eqn:E1. discriminate. reflexivity.
    eapply beta_trans. apply beta_r. apply IHf0_2. simpl in H. destruct (have_string F f0_1) eqn:E1. discriminate. apply H. auto. 
  - simpl. simpl in H. destruct (F =? s) eqn:E1. apply beta_refl. apply beta_abs. apply IHf0. apply H.
  - simpl. apply beta_refl.
  - simpl. apply beta_refl.
  - simpl. Print beta_equiv. simpl in H. destruct (have_string F f0_1) eqn:E1; destruct (have_string F f0_2) eqn:E2;try discriminate H.
    + assert (HH1: false = false). {auto. }
      apply IHf0_1 in HH1.
      assert (HH2: false = false). {auto. }
      apply IHf0_2 in HH2.
      apply IHf0_3 in H.
      eapply beta_trans. apply beta_test01. apply HH1. 
      eapply beta_trans. apply beta_test02. apply HH2.
      auto.
  - simpl. destruct (F =? s) eqn:E1. 
    + apply beta_let1. apply IHf0_1. simpl in H. rewrite E1 in H. apply H. 
    + simpl in H. rewrite E1 in H. destruct (have_string F f0_1) eqn:E2. discriminate. apply beta_let.  apply IHf0_1. reflexivity. apply IHf0_2. apply H.  
  - simpl. Print beta_equiv. apply beta_fix1. apply IHf0. simpl in H. apply H.
  Qed.  

Lemma subst_lemma2 : forall t1 t1' f s,
  nil |-- s-> 
  t1 =b t1' ->
  subst f s t1 =b subst f s t1'.
Proof.
  intros.
  apply (beta_abs f0 _ _) in H0.
  apply (beta_l _ _ s) in H0. 
  assert(H2:subst f0 s t1 =b app(abs f0 t1) s ).
  { auto. }
  assert(H3: subst f0 s t1' =b app(abs f0 t1') s ).
  {auto. }
  apply (beta_trans (subst f0 s t1) (app (abs f0 t1) s) (app (abs f0 t1') s) H2) in H0.
  apply beta_symm in H3. apply (beta_trans (subst f0 s t1) (app (abs f0 t1') s) (subst f0 s t1')).
  + auto.
  + auto.
Qed.




Lemma subst_lemma3:forall t1 f s1 s1',
  s1 =b s1' -> subst f s1 t1 =b subst f s1' t1.
Proof.
  intros.
  induction t1.
  - simpl. destruct (eqb_spec f0 s).
    + apply H.
    + apply beta_refl.
  - simpl. apply beta_rl. apply IHt1_1. apply IHt1_2.
  - simpl. destruct (eqb_spec f0 s).
    + apply beta_refl.
    + apply beta_abs. apply IHt1.
  - simpl. apply beta_refl.
  - simpl. apply beta_refl.
  - simpl. apply beta_test0.
    apply IHt1_1. apply IHt1_2. apply IHt1_3.
  - simpl. apply beta_let. apply IHt1_1. destruct (eqb_spec f0 s).
    + apply beta_refl.
    + apply IHt1_2.
  - simpl. apply beta_fix1. apply IHt1.
Qed. 

Lemma subst_lemma5:forall (f1 f2:string) (t1 t2:tm),
  eqb f1 f2 = false ->
  have_string f1 t1 = false->
  have_string f1 t2 = false->
  have_string f1 (subst f2 t1 t2) = false.
Proof.
  intros.
  induction t2.
  - simpl. destruct (f2 =? s). apply H0. apply H1.
  - simpl in H1. destruct (have_string f1 t2_1) eqn:E1. discriminate. apply IHt2_2 in H1. 
    simpl. rewrite H1. assert(HH1: false = false). {reflexivity. } apply IHt2_1 in HH1. rewrite HH1. reflexivity.
  - simpl. destruct (f2 =? s) eqn:E1. apply H1. simpl. destruct (f1=?s)eqn:E2. reflexivity. apply IHt2. simpl in H1. rewrite E2 in H1. apply H1.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. simpl in H1. destruct (have_string f1 t2_1) eqn:E1. discriminate. destruct (have_string f1 t2_2) eqn:E2. destruct H1. assert (HH1: true = true). { reflexivity. }
    apply IHt2_1 in HH1. rewrite HH1. reflexivity.  assert (HH1: false = false). { reflexivity. } apply IHt2_1 in HH1. rewrite HH1. 
    assert (HH2: false = false). { reflexivity. } apply IHt2_2 in HH2. rewrite HH2. apply IHt2_3. apply H1.
  - simpl. destruct (f1 =? s) eqn:E1. apply IHt2_1. simpl in H1. rewrite E1 in H1. apply H1. 
    simpl in H1. rewrite E1 in H1. destruct (have_string f1 t2_1) eqn:E2. discriminate. assert (HH1: false = false). { reflexivity. }  apply IHt2_1 in HH1.
    rewrite HH1. destruct (f2 =? s). apply H1. apply IHt2_2. apply H1.
  - simpl. apply IHt2. simpl in H1. apply H1.
  Qed.    

Lemma subst_lemma6 :forall (F1 F2:string) (t1 t2 M:tm),
  nil |-- t1->
  nil |-- t2->
  eqb F1 F2 = false->
  subst F1 t1 (subst F2 t2 M) =b subst F2 t2 (subst F1 t1 M).
Proof.
  intros.
  induction M;simpl;auto.
  - simpl. destruct (F2 =? s) eqn:E1; destruct (F1 =? s)eqn:E2.
    + apply eqb_eq in E1. apply eqb_eq in E2. apply eqb_neq in H1. subst. congruence. 
    + simpl. rewrite E1. apply subst_lemma1. apply close_lemma6;auto.
    + simpl. rewrite E2. apply beta_symm. apply subst_lemma1. apply close_lemma6;auto.
    + simpl. rewrite E1. rewrite E2. auto.
  - simpl. destruct (F2 =? s) eqn:E1; destruct (F1 =? s)eqn:E2;simpl; rewrite E1; rewrite E2;auto.
  - destruct (F2 =? s) eqn:E1; destruct (F1 =? s)eqn:E2;simpl;try rewrite E1;try rewrite E2;auto.
  Qed.

Lemma close_lemma7: forall (t:tm),
  nil |-- t ->
  have_string "s1" t = false /\ 
  have_string "s2" t = false /\
  have_string "s" t = false /\
  have_string "res1" t = false /\
  have_string "res2" t = false /\
  have_string "f" t = false /\
  have_string "a" t = false.
Proof.
  intros.
  repeat split; apply close_lemma6; auto.
Qed.

Lemma close_lemma8: forall (f t t': tm) (F:string), 
  nil|-- f -> subst F t f =b subst F t' f.
Proof.
  intros.
  assert(H1:subst F t f0 =b f0). 
  {
    apply subst_lemma1.
    apply close_lemma6.
    apply H.
  }
  assert(H2:subst F t' f0 =b f0).
  {
    apply subst_lemma1.
    apply close_lemma6.
    apply H.
  }
  eauto.
Qed.

Lemma close_lemma9: forall G M1 M2,
  G |-- (app M1 M2) ->
  G |-- M1 /\ G |-- M2.
Proof.
  intros.
  inversion H.
  auto.
Qed.

Lemma have_string_lemma1 : forall (F A:string) (t M:tm),
  (eqb F A) = false->
  [] |-- t ->
  have_string F (subst A t M) = have_string F M.
Proof.
  intros.
  induction M;simpl;auto.
  - destruct (eqb_spec A s).
    + subst. rewrite H. apply close_lemma6. auto.
    + simpl. auto.
  - rewrite IHM1. rewrite IHM2. auto.
  - destruct (eqb_spec A s).
    + simpl. auto.
    + simpl. rewrite IHM. auto.
  - rewrite IHM1. rewrite IHM2. rewrite IHM3. auto.
  - rewrite IHM1. destruct (eqb_spec A s).
    + auto.
    + rewrite IHM2. auto.
Qed.            

Lemma close_lemma10 : forall t G,
  nil |-- t->
  G |-- t.
Proof.
  intros.
  induction G.
  - auto.
  - apply close_lemma4. auto.
Qed. 

Lemma close_lemma11 : forall x s G t,
  (x :: s :: G)%list |-- t->
  (s :: x :: G)%list |-- t.
Proof.
  intros.
  assert(HH:([]++(x0::[s]) ++G)%list |--t ).
  {simpl. auto.  }
  apply close_lemma3 in HH.
  simpl in HH.
  assert(HH1:(G++[x0]++[s])%list |-- t).
  {simpl. auto. }
  apply close_lemma3 in HH1.
  simpl in HH1.
  assert(HH2:([]++G++[s;x0])%list |-- t).
  {simpl. auto. }
  apply close_lemma3 in HH2.
  simpl in HH2.
  auto.
Qed.

Lemma close_lemma12 : forall t G x,
  G |-- abs x t ->
  List.In x G ->
  G |-- t.
Proof.
  intro t.
  induction t;intros;auto.
  - inversion H.
    subst. inversion H2. subst. apply close_string.
    destruct H3. 
    + subst. auto.
    + auto.
  - apply close_lemma2 in H. destruct H. apply close_app.
    + apply (IHt1 G x0);auto.
    + apply (IHt2 G x0);auto.
  - apply close_abs. apply (IHt (s::G) x0).
    + inversion H. inversion H2. subst. apply close_abs. apply close_lemma11. auto.
    + simpl. right. auto.
  -  inversion H. subst. inversion H2. subst. 
    apply close_abs in H5. apply close_abs in H6. apply close_abs in H7. apply IHt1 in H5;auto. apply IHt2 in H6;auto. apply IHt3 in H7;auto.
  - apply close_let. inversion H. inversion H2. subst.
    + apply close_lemma11 in H6. apply close_abs in H6. apply IHt2 in H6. auto.
      * simpl. right. auto.
    + inversion H. inversion H2. subst. apply (IHt1 G x0);auto.
  - apply close_fix. inversion H. inversion H2. subst. apply (IHt G x0);auto.
Qed. 

Lemma close_lemma13 : forall M x G t,
  nil |-- t ->
  (x::G) |-- M -> 
  G |-- subst x t M.
Proof.
  intro M.
  induction M;intros;simpl;auto.
  - simpl. destruct (eqb_spec x0 s).
    + apply close_lemma10. auto.
    + inversion H0. simpl in H2. destruct H2.
      * congruence.
      * auto.
  - simpl. apply close_app. 
    + apply IHM1;auto. inversion H0. destruct H2. auto.
    + apply IHM2;auto. inversion H0. destruct H2. auto.
  - simpl. destruct (eqb_spec x0 s).
    + subst. apply close_lemma12 in H0. 
      * auto.
      * simpl. left. auto.
    + apply close_abs. apply IHM;auto. inversion H0. apply close_lemma11. auto.
  -  inversion H0. subst. apply close_test0;auto.
  - inversion H0. subst. apply close_let.
    + destruct (eqb_spec x0 s).
      * subst. apply close_abs in H3. apply close_lemma12 in H3;auto. 
      * apply IHM2;auto. apply close_lemma11. auto.
    + apply IHM1;auto.
  - inversion H0. subst. apply close_fix. apply IHM;auto.
Qed.               

Hint Resolve subst_lemma1.
Ltac find_have_string_f :=
  match goal with
    H1: have_string _ (app _ _) = false
    |- _ => apply have_string_lemma in H1
  end.

Ltac find_and :=
  match goal with
    H1: _ /\ _
    |- _ => destruct H1
  end.
Ltac match_env := try apply close_app;try apply close_abs;try apply close_let;try apply close_lemma13.
Ltac match_list := repeat(apply List.not_in_cons; split);auto;apply eqb_neq;auto.   

Theorem have_string_lemma2 : forall (f s:string) ,
  have_string f s = true <-> (f =? s) = true.
Proof.
  intros.
  split.
  - intros. unfold have_string in H. destruct (f0 =? s);auto.
  - intros. unfold have_string. rewrite H. auto.
Qed.  


Theorem subst_lemma7 : forall M F t t1 ,
  F = "f" ->
  nil |-- t->
  match_subtm F M->
  have_string "s1" M = false->
  subst "s1" t (trans_M F t1 M) =b trans_M F (subst "s1" t t1) M.
Proof.
  intros M F.
  induction M;intros.
  - simpl. inversion H1. rewrite H4. subst. remember "s1". simpl. destruct (eqb_spec s0 s). 
    + simpl in H2. rewrite e in H2. rewrite eqb_refl in H2. discriminate. 
    + auto.
  - inversion H1;subst;repeat find_have_string_f;repeat find_and. 
    + simpl. auto.
    + simpl. simpl in H2. rewrite H5. destruct (have_string "f" M2) eqn:E2. 
      * simpl. assert (HH: (subst "s1" t M1) =b M1). { auto. } auto.  
      * simpl. assert (HH: (subst "s1" t M1) =b M1). {auto. }  
        assert (HH2: (subst "s1" t M2) =b M2). {auto. } 
        eauto.     
    + simpl. rewrite H5. destruct (have_string "f" M2) eqn:E2.
      * assert(HH: subst "s1" t (trans_M "f" "s2" M2) =b (trans_M "f" "s2" M2)). {apply IHM2;auto. }
        destruct (is_var_F "f" M1) eqn:E1;simpl;auto.
      * assert(HH:(subst "s1" t M2) =b M2). {auto. }
        destruct (is_var_F "f" M1) eqn:E1;simpl;auto.
  - inversion H1.
  - simpl. auto.
  - simpl. auto.
  - inversion H1. 
  - inversion H1.
  - inversion H1.
  Qed.       

Theorem subst_lemma8: forall M F t t1 ,
  F = "f" ->
  nil |-- t->
  match_subtm F M->
  have_string "s2" M = false->
  subst "s2" t (trans_M F t1 M) =b trans_M F (subst "s2" t t1) M.
Proof.
  intros M F.
  induction M;intros.
  - simpl. inversion H1. rewrite H4. subst. remember "s2". simpl. destruct (eqb_spec s0 s). 
    + simpl in H2. rewrite e in H2. rewrite eqb_refl in H2. discriminate. 
    + auto.
  - inversion H1; subst;repeat find_have_string_f; repeat find_and.
    + simpl. auto. 
    + simpl. rewrite H5. subst. destruct (have_string "f" M2) eqn:E2.
      * simpl. 
        assert (HH:  (subst "s2" t M1) =b M1). {auto. } 
        assert (HH2: subst "s2" t (trans_M "f" "s1" M2) =b (trans_M "f" "s1" M2)). {apply IHM2;auto. }
        apply beta_let;auto.
      * simpl.  assert (HH: (subst "s2" t M1) =b M1). {auto. }  
        assert (HH2: (subst "s2" t M2) =b M2). {auto. }
        eauto.
    + simpl. rewrite H5.
      assert(HH: (subst "s2" t (trans_M "f" "s1" M1)) =b (trans_M "f" "s1" M1)). {apply IHM1;auto. } 
      destruct (have_string "f" M2) eqn:E2.
      * simpl. destruct (is_var_F "f" M1);simpl;auto.
      * simpl. destruct (is_var_F "f" M1);simpl;auto.
        ** assert(HH2: subst "s2" t (trans_M "f" "s1" M1) =b (trans_M "f" "s1" M1)). {auto. }
          assert(HH3: (subst "s2" t M2) =b M2). {auto. }
          auto.
  - inversion H1.
  - auto.
  - auto.
  - inversion H1.
  - inversion H1.
  - inversion H1.
Qed.  

Hint Unfold List.In.
Hint Unfold not.
Hint Resolve subst_lemma5.
Hint Resolve close_lemma8.
Hint Resolve close_lemma10.
Hint Resolve close_lemma6.
Hint Resolve close_lemma11.
Hint Resolve close_lemma13.
Hint Resolve close_lemma4.

Lemma is_var_F_lemma : forall (F:string) (M:tm),
  is_var_F F M = true -> M = F.
Proof.
  intros.
  unfold is_var_F in H.
  destruct M eqn:E1; rewrite <- E1;try discriminate.
  - subst. destruct (eqb_spec s F).
    + subst. reflexivity.
    + discriminate.
Qed.
Hint Resolve is_var_F_lemma.

Theorem close_lemma14: forall F M G t,
  F = "f"->
  G|--t->
  G|--M->
  match_subtm F M->
  G|-- trans_M F t M.
Proof.
  intros F M.
  induction M;intros.
  - inversion H2. simpl. rewrite H4. auto.
  - inversion H2. 
    + simpl. rewrite eqb_refl. subst. auto.
    + inversion H1. simpl. rewrite H5. subst.
      destruct (have_string "f" M2) eqn:E2;repeat match_env;auto. 
    + simpl. inversion H1. rewrite H5. destruct (is_var_F F M1) eqn:E2.
      * repeat match_env;auto. apply is_var_F_lemma in E2. subst. auto.
      * destruct (have_string F M2) eqn:E1;subst;repeat match_env;auto.
  - inversion H2.
  - simpl. auto.
  - simpl. auto.
  - inversion H2.
  - inversion H2.
  - inversion H2.
Qed. 
  
Hint Resolve close_lemma14. 

            
Theorem close_lemma15: forall G M G2,
  G|--M ->
  (forall s, List.In s G -> List.In s G2) ->
  G2|-- M.
Proof.
  intros G.
  induction G;intros.
  - apply close_lemma10. auto. 
  - apply (close_lemma12 _ _ a). 
    + apply IHG;auto. 
    + apply H0. auto.
Qed.

Theorem close_lemma16 :forall x G t,
  G |-- t -> (G++[x]) |-- t.
Proof.
  intros.
  assert(HH:(nil++G ++ [x0]) |-- t ).
  {apply close_lemma3. simpl. apply close_lemma4. auto. }
  simpl in HH. auto.
  Qed.

Hint Resolve close_lemma16.



Theorem m_k_2 : forall (f f' M k m:tm)(F A:string),
  match_subtm F M ->
  F = "f" ->
  A = "a" ->
  (forall k' m',
  app k' (app f m') =b app (app f' m') k') ->
  nil |-- f ->
  nil |-- f'->
  nil |-- m ->
  nil |-- k ->
  (F::A::nil)%list |-- M->
  subst F f' (subst A m (trans_M F k M )) =b app k (subst F f (subst A m M)).
 Proof.
  intros. 
  generalize dependent k0.
  assert(HH1: []|--f0). {auto. }
  assert(HH2: []|--f'). {auto. }
  assert(HH3: []|--m). {auto. }
  apply close_lemma7 in HH1.
  apply close_lemma7 in HH2.
  apply close_lemma7 in HH3.
  repeat find_and.
  induction M; intros;try inversion H.
  - assert(HH4: []|--k0). {auto. }
    apply close_lemma7 in HH4. repeat find_and. simpl. rewrite H30. simpl. apply beta_rl. 
    + subst. eauto.
    + destruct (eqb_spec A s);auto.
      * simpl. rewrite H30. auto.
  - inversion H7. assert(HH4: []|--k0). {auto. }
    apply close_lemma7 in HH4. repeat find_and.
    + subst. simpl.
      assert(HH: subst "f" f' (subst "a" m M2) =b (subst "a" m M2)). {auto. }
      eapply beta_trans.
      apply beta_symm.
      apply H2.
      apply beta_rl;eauto.
      * apply beta_rl;eauto.
  - inversion H7. simpl. repeat find_and. rewrite H31. destruct (have_string F M2) eqn:E2.
    + subst. inversion H.   
      * congruence. 
      * simpl. assert(HHH: (["a"; "f"]++["res1"])%list |-- M1). { auto. } 
        eapply beta_trans. apply beta_let1. apply beta_abs. apply beta_l. 
        assert(EE1: subst "f" f' (subst "a" m k0) =b k0). { eapply beta_trans. apply subst_lemma1;auto. auto. }
        apply EE1. 
        eapply beta_trans. apply beta_letvalue. repeat match_env; auto.  
        eapply beta_trans. apply subst_lemma6; auto. repeat match_env;auto.
        eapply beta_trans. apply subst_lemma2. auto. apply subst_lemma6;auto. repeat match_env;auto. 
        eapply beta_trans. 
        apply subst_lemma2. auto. apply subst_lemma2. auto. apply subst_lemma7;auto. 
                            repeat match_env;auto.
                            apply (close_lemma5 _ _ ["f";"a"]);auto.
                            match_list.
        eapply beta_trans. apply IHM2;auto. repeat match_env;auto.
        simpl.
        eapply beta_trans. apply beta_appabs. 
                            repeat match_env;auto. 
        simpl. 
        assert (HH: subst "res1" (subst "f" f0 (subst "a" m M2)) k0 =b k0). {auto. }
        assert (HH2: subst "res1" (subst "f" f0 (subst "a" m M2))
        (subst "f" f' (subst "a" m M1)) =b (subst "a" m M1)). { eapply beta_trans. apply subst_lemma1. auto. auto. }
        assert (HH3: (subst "f" f0 (subst "a" m M1)) =b (subst "a" m M1)). {auto. }
        apply beta_rl;auto. apply beta_rl;eauto.
      * congruence.
    + simpl.  
      assert (HH1: (subst F f' (subst A m k0)) =b k0). { eapply beta_trans. apply subst_lemma1;auto. auto. }
      assert (HH2: subst F f' (subst A m M1) =b subst A m M1). { subst. auto. }
      assert (HH3: subst F f' (subst A m M2) =b subst A m M2). { subst. auto. }
      assert (HH4: subst F f0 (subst A m M1) =b subst A m M1). { subst. auto. }
      assert (HH5: subst F f0 (subst A m M2) =b subst A m M2). { subst. auto. }
      subst. apply beta_rl;auto. apply beta_rl;eauto. 
  - simpl. rewrite H31. destruct (have_string F M2) eqn:E2.
    + subst. inversion H7. 
      assert(HH1: (["a"; "f"]++["s2"])%list |-- M2). { auto. }
      assert(HH2: (["a"; "f";"s2"]++["res1"])%list |-- M2). { auto. }
      assert(HH3: (["a"; "f"]++["res2"])%list |-- M1). { auto. }
      assert(HH4: (["a"; "f"]++["res1"])%list |-- M2). { auto. }
      destruct (is_var_F "f" M1) eqn:E3. 
      * apply is_var_F_lemma in E3. subst. simpl. inversion H32. simpl in H1. congruence.
      * 
        eapply beta_trans. apply beta_letvalue. simpl. repeat match_env;auto 10.
        fold subst. simpl. 
        eapply beta_trans. apply subst_lemma6;auto. repeat match_env;auto 10.
        eapply beta_trans. apply subst_lemma2. auto. apply subst_lemma6;auto. repeat match_env;auto 10.
        eapply beta_trans. apply subst_lemma2. auto. apply subst_lemma2. auto.
                            apply subst_lemma7;auto.
                            repeat match_env;auto 10.
                            apply (close_lemma5 _ _ ["f";"a"]);auto.
                            match_list.
        eapply beta_trans. apply IHM1;auto. repeat match_env;auto 10.
        simpl. 
        eapply beta_trans. apply beta_appabs;auto.
        simpl.
        eapply beta_trans. apply beta_letvalue. repeat match_env;auto 10.
        eapply beta_trans. apply subst_lemma6;auto. repeat match_env;auto 10. 
        eapply beta_trans. apply subst_lemma2. auto. apply subst_lemma6;auto. repeat match_env;auto 10.
        eapply beta_trans. apply subst_lemma2. auto. apply subst_lemma2. auto. apply subst_lemma6;auto. repeat match_env;auto 10.
        eapply beta_trans. apply subst_lemma2. auto. apply subst_lemma2. auto. apply subst_lemma2. auto.
                            apply subst_lemma8;auto. 
                            repeat match_env;auto 10.
                            apply (close_lemma5 _ _ ["f";"a"]);auto.
                            match_list.
        simpl.
        eapply beta_trans. apply subst_lemma2. auto. apply IHM2;auto. repeat match_env;auto.
        simpl. 
        eapply beta_trans. apply beta_appabs. repeat match_env;auto.
        simpl.
        apply beta_rl.
        ** eapply beta_trans. 
            assert(HHH: have_string "res2" M1 = false). {apply (close_lemma5 _ _ ["f";"a"]);auto. match_list.  } 
            apply subst_lemma1. repeat apply subst_lemma5;auto. 
            eapply beta_trans. apply subst_lemma2. auto. 
                              apply subst_lemma1. repeat apply subst_lemma5;auto.
            eapply beta_trans. apply subst_lemma2. auto. 
                              apply subst_lemma1. repeat apply subst_lemma5;auto. 
            eapply beta_trans. apply subst_lemma1;auto. auto.
        ** apply beta_rl;auto 10.
            eapply beta_trans. assert(HHH: have_string "res2" M1 = false). {apply (close_lemma5 _ _ ["f";"a"]);auto. match_list.  } 
            apply subst_lemma1. repeat apply subst_lemma5;auto.
            auto 10.
    + subst. inversion H7. 
      assert(HHH: (["a"; "f"]++["res1"])%list |-- M2). { auto. } 
      assert(EE1: subst "f" f' (subst "a" m k0) =b k0). { eapply beta_trans. apply     subst_lemma1;auto. auto. }
      destruct (is_var_F "f" M1) eqn:E3. 
      * apply is_var_F_lemma in E3. subst. simpl. inversion H32. simpl in H1. congruence.
      *  eapply beta_trans. apply beta_let1. simpl. apply beta_abs. 
                          apply beta_l. apply EE1.
        eapply beta_trans. apply beta_letvalue. repeat match_env;auto.
        eapply beta_trans. apply subst_lemma6;auto. repeat match_env;auto.
        eapply beta_trans. apply subst_lemma2. auto. apply subst_lemma6;auto. repeat match_env;auto.
        eapply beta_trans. apply subst_lemma2. auto. apply subst_lemma2. auto. 
                          apply subst_lemma7;auto. 
                          repeat match_env;auto.
                          apply (close_lemma5 _ _ ["f";"a"]);auto.
                          match_list.
        simpl. 
        eapply beta_trans. apply IHM1;auto.
                          repeat match_env;auto.
        eapply beta_trans. apply beta_appabs. repeat match_env;auto.
        simpl. 
        apply beta_rl;auto.
        apply beta_rl;auto.
        assert(HH2: 
          subst "res1" (subst "f" f0 (subst "a" m M1)) (subst "f" f' (subst "a" m M2)) 
            =b subst "a" m M2). 
        {eapply beta_trans. apply subst_lemma1;auto. auto. }
        eauto.
  - simpl. subst. apply beta_rl;auto. eapply beta_trans. apply subst_lemma1;auto. auto.
Qed.


