Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Smallstep.
From Coq Require Import Strings.String.

Inductive ty : Type :=
  | Nat : ty
  | Arrow : ty -> ty -> ty
(*   | List : ty -> ty *)
  | Cont : ty -> ty
.

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
(*   | tnil : ty -> tm
  | tcons : tm -> tm -> tm
  | tlcase : tm -> tm -> string -> string -> tm -> tm *)
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
(*   | tnil T =>
          tnil T
  | tcons t1 t2 =>
          tcons (subst x s t1) (subst x s t2)
  | tlcase t1 t2 y1 y2 t3 =>
          tlcase (subst x s t1) (subst x s t2) y1 y2 (if eqb y1 x then t3 else if eqb y2 x then t3 else (subst x s t3)) *)  
end.

Inductive halt : tm -> Prop :=
  | h_abs : forall x t,
      halt (abs x t)
  | h_natconst : forall n,
      halt (nat_const n)
  | h_opconst : forall o,
      halt (op_const o)
  | h_plus : forall n,
      halt (app Oplus n)
  | h_minus : forall n,
      halt (app Ominus n)
  | h_mult : forall n,  
      halt (app Omult n)
(*   | h_lnil : forall T, 
      halt (tnil T)
  | h_lcons : forall v1 vl,
      halt v1 ->
      halt vl ->
      halt (tcons v1 vl) *)
.
Hint Constructors halt.

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x t h,
                halt h ->
                step (app (abs x t) h) (subst x h t)
  | ST_App1 : forall t1 t1' t2,
              step t1 t1' ->
              step (app t1 t2) (app t1' t2)
  | ST_App2 : forall h1 t2 t2',
              halt h1 ->
              step t2 t2' ->
              step (app h1 t2) (app h1 t2')
  | ST_Minconsts : forall n1 n2:nat,
              step (app(app Ominus n1) n2) (n1 - n2)
  | ST_Plusconsts : forall n1 n2:nat,
              step (app(app Oplus n1) n2) (n1 + n2)
  | ST_Multconsts: forall n1 n2:nat,
              step (app(app Omult n1) n2) (n1 * n2)
  | ST_Test01: forall t1 t1' t2 t3,
              step t1 t1' ->
              step (test0 t1 t2 t3) (test0 t1' t2 t3)
  | ST_Test0Zro : forall t2 t3,
              step (test0 0 t2 t3) t2
  | ST_Test0NotZro: forall n t2 t3,
              step (test0 (S n) t2 t3) t3
  | ST_Let1 : forall x t1 t2 t1',
              step t1 t1' ->
              step (tlet x t1 t2) (tlet x t1' t2)
  | ST_LetValue : forall x h1 t2,
              halt h1 ->
              step (tlet x h1 t2) (subst x h1 t2)
  | ST_Fix1 : forall t1 t1',
              step t1 t1' ->
              step (tfix t1) (tfix t1')
  | ST_FixAbs: forall xf t2,
              step (tfix (abs xf t2)) (subst xf (tfix (abs xf t2)) t2)
(*   | ST_Cons1 : forall t1 t1' t2,
              step t1 t1' ->
              step (tcons t1 t2) (tcons t1' t2)
  | ST_Cons2 : forall h1 t2 t2',
              halt h1 -> 
              step t2 t2' ->
              step (tcons h1 t2) (tcons h1 t2')
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
              step t1 t1' ->
              step (tlcase t1 t2 x1 x2 t3) (tlcase t1' t2 x1 x2 t3)
  | ST_LcaseNil : forall T t2 x1 x2 t3,
              step (tlcase (tnil T) t2 x1 x2 t3) t2
  | ST_LcaseCons : forall h1 hl t2 x1 x2 t3,
              halt h1 ->
              halt hl ->
              step (tlcase (tcons h1 hl) t2 x1 x2 t3) (subst x2 hl (subst x1 h1 t3)) *)
.
Hint Constructors step.
Notation multistep := (multi step).
Notation "t1 '+' t2" := (app(app Oplus t1) t2).
Notation "t1 '*' t2" := (app(app Omult t1) t2).
Notation "t1 '-' t2" := (app(app Ominus t1) t2).

Reserved Notation "t1 '=b' t2" (at level 40).

Inductive beta_equiv :tm -> tm -> Prop:=
  | beta_refl x: x =b x 
  | beta_symm x y: x =b y -> y =b x
  | beta_trans x y z: x =b y -> y =b z -> x =b z
  | beta_reduction x t y: halt y -> (app (abs x t) y =b subst x y t)
  | beta_l t1 t1' t2: t1 =b t1' -> app t1 t2 =b app t1' t2
  | beta_r t1 t2 t2': t2 =b t2' -> app t1 t2 =b app t1 t2' 
  | beta_appabs x t h:
                halt h ->
                (app (abs x t) h) =b (subst x h t)
  | beta_fix1 t1 t1': t1 =b t1' -> tfix t1 =b tfix t1'
  | beta_fixabs f t2: tfix (abs f t2) =b subst f (tfix (abs f t2)) t2 
  | beta_test01: forall t1 t1' t2 t3,
              t1 =b t1' ->
              (test0 t1 t2 t3) =b (test0 t1' t2 t3)
  | beta_test0Zro t2 t3 : 
              (test0 0 t2 t3) =b t2
  | beta_test0NotZro n t2 t3: 
              (test0 (S n) t2 t3) =b t3
where "t1 '=b' t2" := (beta_equiv t1 t2).
Hint Constructors beta_equiv.

Definition test :=
  (0+1)+1
.
Compute test.

Example cal:
 multistep test 2.
Proof.
  unfold test. normalize.  
  Qed.

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

Notation idB :=
  (abs x (var x)).


Notation idBB :=
  (abs x (var x)).

Example reduces1 :
  multistep (app idB 4) (4).
Proof.
  normalize.
  Qed.


Lemma step_example1 :
  multistep (app idBB idB) idB.
Proof.
  normalize.
  Qed.

Lemma step_example2 :
  multistep (app idBB (app idBB idB)) idB.
Proof.
  normalize.
  Qed.


Definition fact :=
  tfix
    (abs "f" 
      (abs "a" 
        (test0
           (var "a")
           1
           ((var "a") *
            (app (var "f") ((var "a") - 1)))))).



Example reduces2 :
  multistep (app fact 4) 24.
Proof.
  unfold fact.
  normalize.
  Qed.

Definition fact2 :=
  tfix
    (abs "f" 
      (abs "a" 
        (test0
           (var "a")
           1
           ((app (var "f") ((var "a") - 1)) *
              (var "a"))))).

Definition fact_pls :=
  tfix
    (abs "f" 
      (abs "a"
        (test0
           (var "a")
           1
           ("a" + "a" * (app "f" ("a" - 1)))))).

Definition mlt_pls_cont := 
  tfix 
    (abs f 
      (abs x 
        (abs c
          (test0
            (var x)
            (app c 1)
            (app 
              (app f (x - 1))
              (abs "s" 
                (app c 
                  (x + x * "s")))))))).

(** 0 -> 1, 1 -> 2, 2 -> 6, 3 -> 21 , 4 -> 88**)
Example reduces3 :
  multistep (app fact_pls (4)) (88).
Proof.
  unfold fact_pls.
  normalize.
  Qed.

Example reduces4:
  multistep (app (app mlt_pls_cont 4) (abs "s" "s")) ( 88).
Proof.
  unfold mlt_pls_cont.
  normalize.
  Qed.


Definition mlt_cont := 
  tfix 
    (abs f 
      (abs x 
        (abs c 
          (test0
            (var x)
            (app (var c) 1)
            (app 
              (app (var f) (x - 1))
              (abs "s" 
                (app (var c) 
                  ((var "s") * (var x))))))))).



Example test_mlt_cont :
  multistep (app (app mlt_cont 4) (abs "s" (var "s"))) 24.
Proof.
  unfold mlt_cont.
  normalize.
  Qed.
(* 
Definition l := "l".
Definition hd := "hd".
Definition tail := "tail".

Definition test_list :=
  tlet l
    (tcons (5) (tcons (6) (tnil Nat)))
    (tlcase (var l)
       (0)
       x y ((var x) * (var x))).

Example reduce_list :
  multistep test_list 25.
Proof.
  unfold test_list.
  normalize.
  Qed.


Definition list_sample :=
  tcons 3 (tcons 5 (tcons 7 (tcons 9 (tnil Nat)))). 

Definition sum_list :=
  tfix 
    (abs f (Arrow (List Nat) Nat)
      (abs l (List Nat)
        (tlcase l 
          (0)
          hd tail ((var hd) + 
                       (app (var f) (var tail)))))).
Example test_sum_list :
  multistep (app sum_list list_sample) 24.
Proof.
  unfold sum_list.
  unfold list_sample.
  normalize.
  Qed.


Definition sum_list_cont :=
  tfix
    (abs f (Arrow (List Nat) Nat)
      (abs l (List Nat)
        (abs c (Cont (List Nat))
          (tlcase l 
            (app (var c) 0)
            hd tail
            (app 
              (app (var f) 
                (var tail))
              (abs "s" (Cont Nat) (app (var c) ((var hd) + (var "s"))))))))).

Definition sum_list_cont2 :=
  tfix
   (abs "f" (Arrow (List Nat) Nat)
      (abs "l" (List Nat)
         (abs "c" (Cont (List Nat))
            (tlcase "l" (app "c" 0) "hd" "tail"
               (tlet "fs" (abs "s" (Cont Nat) (app "c" ("hd" + "s"))) (app (app "f" "tail") "fs")))))).

Example test_sum_list_cont :
  multistep (app ( app sum_list_cont list_sample) (abs "s" (Cont Nat) (var "s"))) 24.
Proof.
  unfold sum_list_cont.
  unfold list_sample.
  normalize.
  Qed.

Example test_sum_list_cont2 :
  multistep (app ( app sum_list_cont2 list_sample) (abs "s" (Cont Nat) (var "s"))) 24.
Proof.
  unfold sum_list_cont2.
  unfold list_sample.
  normalize.
  Qed. *)
(**
Definition fact :=
  tfix
    (abs "f" (Arrow Nat Nat)
      (abs "a" Nat
        (test0
           (var "a")
           (const 1)
           (mlt
              (var "a")
              (app (var "f") (prd (var "a"))))))).


Definition mlt_cont := 
  tfix 
    (abs f (Arrow Nat (Cont Nat))
      (abs x Nat
        (abs c (Cont Nat)
          (test0
            x
            (app c 1)
            (app 
              (app f (x - 1))
              (abs "s" (Cont Nat) 
                (app c 
                  ("s" * x)))))))). 
Definition sum_list :=
  tfix 
    (abs f (Arrow (List Nat) Nat)
      (abs l (List Nat)
        (tlcase l 
          (0)
          hd tail (pls (var hd) 
                       (app (var f) (var tail)))))).
Definition sum_list_cont :=
  tfix
    (abs f (Arrow (List Nat) (Cont Nat))
      (abs l (List Nat)
        (abs c (Cont Nat)
          (tlcase l 
            (app (var c) 0)
            hd tail
            (app 
              (app (var f) 
                (var tail))
              (abs "s" (Cont Nat) (app (var c) (pls (var hd) (var "s"))))))))).s
**)

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
                      then false
                      else if (have_string x t1) 
                          then true 
                          else have_string x t2
  | tfix t1 => have_string x t1

(*   | tnil T => false
  | tcons t1 t2 => if (have_string x t1) 
                    then true 
                    else have_string x t2

  | tlcase t1 t2 y1 y2 t3 => if (have_string x t1) 
                              then true 
                              else if (have_string x t2)
                                  then true
                                  else if eqb y1 x 
                                      then false
                                      else if eqb y2 x 
                                        then false
                                        else have_string x t3   *)
end.

Fixpoint has_app_F (t:tm) :bool :=
  match t with
  | app (var f) m => true
  | app m1 m2 => if has_app_F m1 
                  then true
                  else if has_app_F m2
                  then true
                  else false
  | _ => false
end.


Fixpoint trans_M (F:string)(k t:tm) :=
  match (have_string F t) with
  | false => app k t
  | true => match t with 
             (* F m => F' m k  *)
            | app (var f) m => 
                    if eqb f F
                    then app (app F m) k
                    else app k t
            | app m1 m2 => if have_string F m1 
                  then if have_string F m2
                        then
                          tlet "fs1"
                            (abs "s1"  
                              (tlet "fs2" 
                                (abs "s2" (app k (app "s1" "s2")))
                                (trans_M F "fs2" m2)))
                            (trans_M F "fs1" m1)
                        else
                            (trans_M F (abs "s" (app k (app "s" m2))) m1)
                  else if have_string F m2
                        then
                            (trans_M F (abs "s" (app k (app m1 "s")))  m2)
                        else 
                          app k t
            | _ => app k t
            end
  end.
(* Fixpoint trans_M (f : string) (k t3:tm) :=
  match t3 with 
  | app (var y) m => app t3 k
  | app m1 m2 => if have_string f m1 
                  then if have_string f m2
                        then
                          tlet "fs1"
                            (abs "s1" (Cont Nat) 
                              (tlet "fs2" 
                                (abs "s2" (Cont Nat) (app k (app "s1" "s2")))
                                (trans_M f "fs2" m2)))
                            (trans_M f "fs1" m1)
                        else
                          tlet "fs" 
                            (abs "s" (Cont Nat) (app k (app "s" m2))) 
                            (trans_M f "fs" m1)
                  else if have_string f m2
                        then
                          tlet "fs" 
                            (abs "s" (Cont Nat) (app k (app m1 "s"))) 
                            (trans_M f "fs" m2)
                        else 
                          app t3 k
  | _ => app t3 k
  end. *)

Search (string).
Print concat.
Search list.


Fixpoint l_have_string (l:list string) (k:string) : bool :=
  match l with
  | nil => false
  | cons x l' => if eqb x k
             then true
             else l_have_string l' k
  end.

Fixpoint gen_sym_loop (l:list string) (k:string) (n:nat): string :=
  match n with
  | O => k
  | S n' => if(l_have_string l k) 
            then gen_sym_loop l (k++k) n'
            else k
  end.


Definition gen_sym (l:list string): string :=
  gen_sym_loop l "k" (Datatypes.length l).

Definition trans_to_tail_recursion (F:tm):=
  match F with
  | tfix (abs f
       (abs a t )) => match t with
                        | test0 t1 t2 t3 => tfix (abs f
                                              (abs a 
                                                (abs (gen_sym (cons a (cons f nil)))
                                                  (test0 t1
                                                    (app (gen_sym (cons a (cons f nil))) t2)
                                                    (trans_M f (gen_sym (cons a (cons f nil))) t3)))))
                    
(*                         | tlcase t1 t2 y1 y2 t3 => tfix (abs f Tf
                                                    (abs a Ta
                                                      (abs k (Cont Ta)
                                                        (tlcase t1 
                                                          (app k t2)
                                                          y1 y2
                                                          (trans_M f k t3))))) *)
                        | _ => F
                        end
  | _ => F
  end.



Definition is_recursion (F:tm): Prop :=
  match F with
 | tfix (abs f 
       (abs a t )) =>  if eqb f a 
                        then False
                       else 
                        match t with
                        | test0 (var b) t2 t3 => if eqb a b
                                                then if have_string f t2 
                                                  then False
                                                  else True
                                                else False
(*                         | tlcase t1 t2 y1 y2 t3 => tfix (abs f Tf
                                                    (abs a Ta
                                                      (abs k (Cont Ta)
                                                        (tlcase t1 
                                                          (app k t2)
                                                          y1 y2
                                                          (trans_M f k t3))))) *)
                        | _ => False
                        end
  | _ => False
  end.



Check subst.

Lemma subst_lemma1 : forall (F t: tm) (f:string), 
  (have_string f F) = false -> subst f t F =b F.
Proof.
  intros.
  unfold have_string in H.
  induction t.
  Admitted.

Lemma subst_lemma2 : forall t1 t1' f s,
  t1 =b t1' -> subst f s t1 =b subst f s t1'.
Proof.
  Admitted.

Search list.

Lemma gen_lemma : forall (x:string) (l:list string),
  List.In x l -> x =? (gen_sym l) = false.
Proof.
  intros. 
  Admitted.

Lemma gen_lemma2 : forall (l:list string),
  (gen_sym l) =? (gen_sym l) = true.
Proof.
  intros.
  Search (_ =? _).
  apply eqb_refl.
  Qed.

(* Lemma need_lemma1 : forall (x:string) (t:tm),
  t =b 
. *)
Definition is_fix_string (F:tm) (f:string) : Prop :=
  match F with
  | tfix (abs f' t) => match (eqb f' f) with
                          | true => True
                          | false => False
                          end
  | _ => False
  end.

Notation multib := (multi beta_equiv).

Check multi_refl.
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
  
Print beta_fixabs.

Theorem multib_comm : forall (t1 t2:tm),
  multib t1 t2 -> multib t2 t1.
Proof.
  intros.
  apply multib_eq_be. apply multib_eq_be in H.
  apply beta_symm. apply H.
  Qed.


Theorem m_k : forall (F k:tm)(n: nat),
  halt k->
  is_recursion F->
  app k (app F n) =b app (app (trans_to_tail_recursion F) n) k.
Proof.
  intros F k0 n HH H.
  unfold is_recursion in H.
  destruct F eqn:E1; intros; try destruct H.
  destruct t eqn:E2; try destruct H.
  destruct t0 eqn:E3; try destruct H.
  destruct (s =? s0) eqn:E7; try destruct H.
  destruct t1 eqn:E4; try destruct H.
  destruct t2_1 eqn:E5; try destruct H.
  destruct (s0 =? s1) eqn:E6; try destruct H.
  destruct (have_string s t2_2) eqn:E8; try destruct H.
  apply eqb_eq in E6.
  subst.
  unfold trans_to_tail_recursion.
  induction n.
  - apply multib_eq_be. eapply multi_step. 
    + apply beta_r. apply beta_l. apply beta_fixabs.
    + eapply multi_step. 
      * simpl. rewrite E7. apply beta_r. apply beta_appabs. Search halt. apply h_natconst.
      * simpl. Search(_ =? _). rewrite eqb_refl. simpl. eapply multi_step.
        ** apply beta_r. apply beta_test0Zro. 
        ** eapply multi_step. 
           *** apply beta_r. apply subst_lemma2. apply subst_lemma1. apply E8.
           *** apply multib_comm. eapply multi_step.
             **** apply beta_l. apply beta_l. apply beta_fixabs.
             **** eapply multi_step.
                ***** simpl. rewrite E7. assert(H2: List.In s (s1::s::nil)). { simpl. right. left. reflexivity. }
                      apply gen_lemma in H2. rewrite H2. apply beta_l. apply beta_appabs. apply h_natconst. 
                ***** simpl. assert(H2: List.In s1 (s1::s::nil)). {simpl. left. reflexivity. } apply gen_lemma in H2. rewrite H2. 
                      rewrite eqb_refl. eapply multi_step.
                      ++ apply beta_appabs. apply HH. 
                      ++ eapply multi_step.
                        +++ apply subst_lemma2. apply beta_test0Zro.
                        +++ simpl. eapply multi_step. 
                          ++++ apply beta_r. apply subst_lemma2. apply subst_lemma2. apply subst_lemma1. apply E8.
                          ++++ rewrite gen_lemma2.   
            

Theorem m_k__k_m : forall (F k M:tm) (f:string),
  is_fix_string F f->
  is_recursion F -> 
  trans_M f k M =b app k M.
Proof.
  unfold is_fix_string.
  destruct F eqn:E1; intros; try destruct H.
  destruct t eqn:E2; intros; try destruct H.
  destruct (s =? f0) eqn:E3; intros; try destruct H.

  unfold is_recursion in H0.
  destruct t1 eqn:E4; try destruct H0.
  destruct t2 eqn:E5; try destruct H0.
  

Lemma be_tttr2 : forall (k M:tm) ,
  M =b trans_to_tail_recursion M
.
Proof. Admitted.
Lemma be_tttr : forall (k M:tm) ,
  trans_M k M =b app k M
.
Proof.
  intros.
  induction M; try apply beta_refl.
  simpl.   
    
  
Admitted.
  


Check fact.

Compute fact.

Compute trans_to_tail_recursion fact.


Example test_mlt_cont_trans1 :
  multistep (app (app (trans_to_tail_recursion fact) 4) (abs "s" Nat "s")) 24.
Proof.
  unfold trans_to_tail_recursion.
  unfold fact.
  unfold trans_M.
  normalize.
  Qed.

Example test_mlt_cont_trans2 :
  multistep (app (app (trans_to_tail_recursion fact2) 4)(abs "s" Nat "s"))  24.
Proof.
  unfold trans_to_tail_recursion.
  unfold fact2.
  unfold trans_M.
  normalize.
  Qed.

Compute trans_to_tail_recursion fact_pls.

Example test_mlt_pls_cont_trans1 :
  multistep (app (app (trans_to_tail_recursion fact_pls) 4) (abs "s" Nat "s")) 88.
Proof.
  unfold trans_to_tail_recursion.
  unfold fact_pls.
  unfold trans_M.
  normalize.
  Qed.
(* Definition sum_list_cont3 := trans_to_tail_recursion sum_list.

Compute trans_to_tail_recursion sum_list.

Example test_sum_list_cont_trans1 :
  multistep (app ( app sum_list_cont3 list_sample) (abs "s" (Cont Nat) (var "s"))) 24.
Proof.
  unfold sum_list_cont3.
  unfold trans_to_tail_recursion.
  unfold trans_M.
  unfold have_string.
  unfold list_sample.
  simpl.
  normalize.
  Qed. *)

Definition double_recursion_fact :=
  tfix
    (abs f (Arrow Nat Nat)
      (abs x Nat
        (test0
           x
           1
           ((x * (app f (x-1))) * (x * (app f (x-1))))))).

Example test_double_fact:
  multistep (app double_recursion_fact 2) 4.
Proof.
  unfold double_recursion_fact.
  normalize.
  Qed.

Definition double_fact_cont :=
  trans_to_tail_recursion double_recursion_fact.

Example test_double_fact_cont:
  multistep (app (app double_fact_cont 3)(abs "s" Nat "s")) 144.
Proof.
  unfold double_fact_cont.
  unfold trans_to_tail_recursion.
  unfold double_recursion_fact.
  normalize.
  Qed.

Definition forth_sum :=
  tfix
    (abs f (Arrow Nat Nat)
      (abs x Nat
        (test0
           x
           1
          (((app f (x - 1)) + (app f (x - 1))) + ((app f (x - 1)) + (app f (x - 1))))
             ))).
Example test_forth_sum:
  multistep (app forth_sum 2) 16.
Proof.
  unfold forth_sum.
  normalize.
  Qed.

Definition forth_sum_cont :=
  trans_to_tail_recursion forth_sum.

Compute forth_sum_cont.

Example test_forth_sum_cont :
  multistep (app (app forth_sum_cont 3) (abs "s" Nat "s")) 64.
Proof.
  unfold forth_sum_cont.
  unfold trans_to_tail_recursion.
  unfold forth_sum.
  normalize.
  Qed.






