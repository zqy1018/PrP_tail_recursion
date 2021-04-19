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
                (app (abs x t) h) =b (subst x h t)
  | beta_abs x t t':
                t =b t' ->
                abs x t =b abs x t'
  | beta_fix1 t1 t1': t1 =b t1' -> tfix t1 =b tfix t1'
  | beta_fixabs f t2: tfix (abs f t2) =b subst f (tfix (abs f t2)) t2 
  | beta_test01: forall t1 t1' t2 t2' t3 t3',
              t1 =b t1' ->
              t2 =b t2' ->
              t3 =b t3' ->
              (test0 t1 t2 t3) =b (test0 t1' t2' t3')
  | beta_let1 : forall x t1 t2 t1' t2',
              t1 =b t1' ->
              t2 =b t2' ->
              (tlet x t1 t2) =b (tlet x t1' t2')
  | beta_letvalue : forall x h1 t2,
              halt h1 ->
              (tlet x h1 t2) =b (subst x h1 t2)
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

Fixpoint l_have_string (l:list string) (k:string) : bool :=
  match l with
  | nil => false
  | cons x l' => if eqb x k
             then true
             else l_have_string l' k
  end.

Fixpoint gen_sym_loop (l:list string) (k:string) (n:nat) (m:nat): string :=
  match m with
  | O => match n with
        | O => k
        | S n' => if(l_have_string l k) 
                  then gen_sym_loop l (k++k) n' O
                  else k
        end
  | S m' => match n with
        | O => k
        | S n' => if(l_have_string l k)
                  then gen_sym_loop l (k++k) n' m
                  else gen_sym_loop l (k++k) n' m'
        end
end.


Definition gen_sym (l:list string) (m:nat): string :=
  gen_sym_loop l "k" ((Datatypes.length l) + m) m.

Fixpoint get_all_string (t:tm) : list string :=
  match t with
  | var y => y::nil
  | app t1 t2 => (get_all_string t1) ++ (get_all_string t2)
  | abs y t1 => y :: (get_all_string t1)
  | nat_const n => nil
  | op_const n => nil
  | test0 t1 t2 t3 => (get_all_string t1) ++ (get_all_string t2) ++(get_all_string t3)
  | tlet y t1 t2 => y::(get_all_string t1)++ (get_all_string t2)
  | tfix t1 => get_all_string t1

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
                          tlet "s1" 
                            (abs "res1"
                              (tlet "s2"
                                (abs "res2" (app k (app "res1" "res2")))
                                (trans_M F "s2" m2)))
                            (trans_M F "s1" m1)
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

(* Fixpoint trans_M (F:string)(k t:tm) (l:list string) :=
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
                          tlet (gen_sym l 1) 
                            (abs (gen_sym l 2)  
                              (tlet (gen_sym l 3)
                                (abs (gen_sym l 4) (app k (app (gen_sym l 2) (gen_sym l 4))))
                                (trans_M F (gen_sym l 3) m2 l)))
                            (trans_M F (gen_sym l 1) m1 l)
                        else
                            (trans_M F (abs (gen_sym l 1) (app k (app (gen_sym l 1) m2))) m1 l)
                  else if have_string F m2
                        then
                            (trans_M F (abs (gen_sym l 1) (app k (app m1 (gen_sym l 1))))  m2 l)
                        else 
                          app k t
            | _ => app k t
            end
  end. *)
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

(* Definition trans_to_tail_recursion (F:tm):=
  match F with
  | tfix (abs f
       (abs a t )) => match t with
                        | test0 t1 t2 t3 => tfix (abs f
                                              (abs a 
                                                (abs (gen_sym (get_all_string F) 0)
                                                  (test0 t1
                                                    (app (gen_sym (get_all_string F) 0) t2)
                                                    (trans_M f (gen_sym (get_all_string F) 0) t3 (get_all_string F))))))
                    
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
  end. *)

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
       (abs a t )) => if eqb f a 
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
(* Lemma gen_lemma : forall (x:string) (l:list string) (n:nat),
  List.In x l -> x =? (gen_sym l n) = false.
Proof.
  intros. 
  Admitted.

Lemma gen_lemma2 : forall (l:list string) (n:nat),
  (gen_sym l n) =? (gen_sym l n) = true.
Proof.
  intros.
  Search (_ =? _).
  apply eqb_refl.
  Qed.

Lemma gen_lemma3 : forall (l:list string) (n m:nat),
  n <> m ->
  (gen_sym l n) =? (gen_sym l m) = false.
Proof.
  intros l.
  Search (_ =? _).
  Admitted. *)

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

Theorem multib_comm : forall (t1 t2:tm),
  multib t1 t2 -> multib t2 t1.
Proof.
  intros.
  apply multib_eq_be. apply multib_eq_be in H.
  apply beta_symm. apply H.
  Qed.

Fixpoint no_name_F (F : string) (M:tm) :Prop :=
  match M with
  | var y => True
  | app t1 t2 => no_name_F F t1 /\ no_name_F F t2
  | abs y t1 => 
          if eqb y F then False else no_name_F F t1
  | nat_const n => True
  | op_const n => True
  | test0 t1 t2 t3 => no_name_F F t1 /\ no_name_F F t2 /\ no_name_F F t3
  | tlet y t1 t2 => if eqb F y 
                      then False
                      else no_name_F F t1 /\ no_name_F F t2
  | tfix t1 => no_name_F F t1
end.

Fixpoint match_subtm (f:string) (M:tm): Prop :=
  match have_string f M with
  | false => no_name_F f M
  | true => match M with
            | app m1 m2 => match m1 with
                          | var a => if eqb f a
                                    then if have_string f m2 
                                      then False
                                      else no_name_F f m2
                                    else False
                          | _ => match_subtm f m1 /\ match_subtm f m2
                          end
            | _ => False
            end
  end
.

Lemma subst_lemma1 : forall (f t: tm) (F:string), 
  (have_string F f) = false -> subst F t f =b f.
Proof.
  intros.
  induction f0.
  - simpl. simpl in H. destruct (F =? s ) eqn:E1. 
    + discriminate.
    + apply beta_refl.
  - simpl. apply multib_eq_be. eapply multi_step. apply beta_l. apply IHf0_1. simpl in H. destruct (have_string F f0_1) eqn:E1. discriminate. reflexivity.
    eapply multi_step. apply beta_r. apply IHf0_2. simpl in H. destruct (have_string F f0_1) eqn:E1. discriminate. apply H.  apply multib_eq_be. apply beta_refl.
  - simpl. simpl in H. destruct (F =? s) eqn:E1. apply beta_refl. apply beta_abs. apply IHf0. apply H.
  - simpl. apply beta_refl.
  - simpl. apply beta_refl.
  - simpl. Print beta_equiv. simpl in H. destruct (have_string F f0_1) eqn:E1; destruct (have_string F f0_2) eqn:E2. apply beta_test01. apply IHf0_1. discriminate. discriminate. discriminate. discriminate. discriminate. apply beta_test01. apply IHf0_1. reflexivity. 
    apply IHf0_2. reflexivity. apply IHf0_3. apply H.
  - simpl. destruct (F =? s) eqn:E1. 
    + apply beta_let1. apply IHf0_1. simpl in H. rewrite E1 in H. apply H. apply beta_refl.
    + simpl in H. rewrite E1 in H. destruct (have_string F f0_1) eqn:E2. discriminate. apply beta_let1.  apply IHf0_1. reflexivity. apply IHf0_2. apply H.  
  - simpl. Print beta_equiv. apply beta_fix1. apply IHf0. simpl in H. apply H.
  Qed.

Lemma subst_lemma2 : forall t1 t1' f s,
  t1 =b t1' -> subst f s t1 =b subst f s t1'.
Proof.
  Admitted.

Lemma subst_lemma3:forall t1 f s1 s1',
  s1 =b s1' -> subst f s1 t1 =b subst f s1' t1.
Proof.
  Admitted.

Lemma beta_rl : forall t1 t1' t2 t2',
  t1 =b t1' ->
  t2 =b t2' ->
  app t1 t2 =b app t1' t2'.
Proof.
  intros.
  apply multib_eq_be.
  eapply multi_step.
  - apply beta_l. apply H.
  - eapply multi_step. apply beta_r. apply H0.
  apply multib_eq_be.
  apply beta_refl.
  Qed.

Lemma subst_lemma4:forall (f1 f2 :string) (t1 t2 t3:tm),
  eqb f1 f2 = false->
  have_string f2 t1 = false->
  (*no_name_F f1 t3 ->*)
  subst f1 t1 (subst f2 t2 t3) =b subst f2 (subst f1 t1 t2) (subst f1 t1 t3).
Proof.
  Admitted.
(*   intros.
  induction t3.
  - simpl. destruct (f2 =? s) eqn:E1; destruct (f1 =? s) eqn:E2.
    + apply eqb_eq in E1. apply eqb_eq in E2. subst. apply eqb_neq in H. destruct H. reflexivity.
    + simpl. rewrite E1. apply beta_refl. 
    + simpl. rewrite E2. apply beta_symm. apply subst_lemma1. apply H0.
    + simpl. rewrite E1. rewrite E2. apply beta_refl.
  - simpl. apply beta_rl.
    + apply IHt3_1. simpl in H1. destruct H1. apply H1.
    + apply IHt3_2. simpl in H1. destruct H1. apply H2. 
  - simpl. destruct (f2 =? s) eqn:E1; destruct (f1 =? s) eqn:E2; simpl; try rewrite E1; try rewrite E2; try apply beta_refl.
    + simpl in H1. apply eqb_eq in E2. rewrite E2 in H1. rewrite eqb_refl in H1. destruct H1.
    + apply beta_abs. apply IHt3. simpl in H1. Search(_=?_). rewrite eqb_sym in E2. rewrite E2 in H1. apply H1. 
  - simpl. apply beta_refl.
  - simpl. apply beta_refl.
  - simpl in H1. destruct H1. destruct H2. simpl. apply beta_test01. apply IHt3_1. apply H1.  apply IHt3_2. apply H2. apply IHt3_3. apply H3.
  - simpl. destruct (f1 =? s) eqn:E2. 
    + apply eqb_eq in E2. subst. simpl in H1. rewrite eqb_refl in H1. destruct H1.  
    + destruct (f2 =? s) eqn:E1; simpl; try rewrite E1; try rewrite E2; try apply beta_refl.
      * apply beta_let1. apply IHt3_1. simpl in H1. rewrite E2 in H1. destruct H1. apply H1. apply beta_refl.
      * apply beta_let1. apply IHt3_1. simpl in H1. rewrite E2 in H1. destruct H1. apply H1. apply IHt3_2. simpl in H1. rewrite E2 in H1. destruct H1. apply H2.  
  - simpl. Print beta_equiv. apply beta_fix1. apply IHt3. simpl in H1. apply H1.
  Qed. *)




Lemma match_subtm__no_name:forall (F:string) (M:tm),
  match_subtm F M -> no_name_F F M.
Proof.
  intros.
  induction M.
  - simpl. reflexivity.
  - simpl. simpl in H. destruct (have_string F M1) eqn:E1; destruct (have_string F M2) eqn:E2; split.
    + apply IHM1. destruct M1 eqn:E3;try destruct H;try apply H.
      * destruct (F=?s). destruct H. destruct H.
    + apply IHM2. destruct M1 eqn:E3;try destruct H;try apply H0.
      * destruct (F=?s). destruct H. destruct H.
    + destruct M1 eqn:E3.
      * simpl. reflexivity.
      * apply IHM1. destruct H. apply H.
      * apply IHM1. destruct H. apply H.
      * apply IHM1. destruct H. apply H.
      * apply IHM1. destruct H. apply H.
      * apply IHM1. destruct H. apply H.
      * apply IHM1. destruct H. apply H.
      * apply IHM1. destruct H. apply H.
    + destruct M1 eqn:E3.
      * destruct (F=?s). apply H. destruct H.
      * destruct H. apply IHM2. apply H0.
      * destruct H. apply IHM2. apply H0.
      * destruct H. apply IHM2. apply H0.
      * destruct H. apply IHM2. apply H0.
      * destruct H. apply IHM2. apply H0.
      * destruct H. apply IHM2. apply H0.
      * destruct H. apply IHM2. apply H0.
    + apply IHM1. destruct M1 eqn:E3;try destruct H;try apply H.
      * destruct (F=?s). destruct H. destruct H.
    + apply IHM2. destruct M1 eqn:E3;try destruct H;try apply H0.
      * destruct (F=?s). destruct H. destruct H.
    + destruct H. apply H.
    + destruct H. apply H0.
  - simpl in H. destruct (F=?s) eqn:E1. 
    + rewrite eqb_sym in H. rewrite E1 in H. destruct H.
    + simpl. rewrite eqb_sym. rewrite E1. destruct (have_string F M). destruct H. rewrite eqb_sym in H. rewrite  E1 in H. apply H.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. simpl in H. 
    destruct (have_string F M1). destruct H.
    destruct (have_string F M2). destruct H.
    destruct (have_string F M3). destruct H.
    apply H.
  - simpl. simpl in H. destruct (F=?s).
    + destruct (have_string F M1). destruct H.
      destruct (have_string F M2). destruct H.
      destruct H.
    + destruct (have_string F M1). destruct H.
      destruct (have_string F M2). destruct H.
      apply H.
  - simpl. simpl in H. destruct (have_string F M). destruct H. apply H.
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
Theorem m_k_2 : forall (f f' M k m:tm)(F:string),
  have_string F k = false ->
  match_subtm F M ->
  eqb F "f" = true ->
  (forall k' m',
  app k' (app f m') =b app (app f' m') k') ->
  have_string "s1" f' = false->
  have_string "s2" f' = false->
  have_string "s1" M = false->
  have_string "s2" M = false ->
  have_string "s2" f = false->
  have_string "res1" f' = false->
  have_string "res2" f' = false->
  have_string "s1" f = false->
  have_string "res1" f = false->
  have_string "res2" f = false->
  have_string "s" k = false->
  have_string "s" f = false->
  have_string "s" M = false->
  have_string "s" f' = false->
  have_string "res1" k = false->
  have_string "res2" k = false->
  have_string "res1" M = false->
  have_string "res2" M = false->
  subst F f' (trans_M F k M ) =b app k (subst F f M).

Proof.
  intros. 
  apply multib_eq_be.
  generalize dependent k0.
  induction M;  intros.
  - simpl. destruct (F =? s) eqn:E1.
    + unfold match_subtm in H0. simpl in H0. rewrite E1 in H0. destruct H0. 
    + simpl. rewrite E1. apply (subst_lemma1 k0 f' F) in H. eapply multi_step.
      * apply beta_l. apply H.
      * apply multib_eq_be. apply beta_refl.
  -  destruct (have_string F M1) eqn:E1; destruct (have_string F M2) eqn:E2.
    + destruct M1 as [] eqn:E4.
      * destruct (s =? F) eqn:E3.
        ** apply eqb_eq in E3. subst. simpl in H0. rewrite eqb_refl in H0. rewrite E2 in H0. destruct H0.
        ** simpl. Search(_ =? _). simpl in E1. rewrite eqb_sym in E1. rewrite E3 in E1. discriminate.
      * rewrite <- E4. apply eqb_eq in H1. eapply multi_step. rewrite <- E4 in E1.
        ** apply subst_lemma2. simpl. rewrite E1. rewrite E4. rewrite E2. apply beta_letvalue. apply h_abs.
        ** eapply multi_step.
          *** apply subst_lemma2. apply subst_lemma3. apply beta_abs. apply beta_letvalue. apply h_abs.
          *** eapply multi_step.
            **** apply subst_lemma4. rewrite H1. simpl. reflexivity. apply H3. 
            **** rewrite H1. simpl. eapply multi_step. 
              ***** apply subst_lemma3. apply beta_abs. apply subst_lemma4. simpl. reflexivity. apply H4. 
              ***** simpl. assert(HH1: (subst "f" f' (trans_M "f" "s2" M2)) =b (app "s2" (subst "f" f0 M2))).
                   {apply multib_eq_be. rewrite H1 in IHM2. apply IHM2. - rewrite <- E4 in H0.  simpl in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E4 in H0. destruct H0. rewrite H1 in H21. apply H21. - rewrite <- E4 in H5. simpl in H5. destruct (have_string "s1" M1) eqn:EE1. discriminate H5. apply H5. 
                  - rewrite <- E4 in H6. simpl in H6. destruct (have_string "s2" M1). discriminate. apply H6. 
                  - rewrite <- E4 in H15. simpl in H15. destruct (have_string "s" M2) eqn:EE1. destruct (have_string "s" M1). discriminate H15. discriminate H15. reflexivity. 
                  - rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. apply H19.
                  - rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. apply H20.
                  - simpl. reflexivity. -simpl. reflexivity. - simpl. reflexivity. - simpl. reflexivity. } 
                  eapply multi_step.
                  ++ apply subst_lemma3. apply beta_abs. apply subst_lemma2. apply HH1. 
                  ++ simpl. eapply multi_step.
                    +++ apply subst_lemma3. apply beta_abs. apply beta_r. apply subst_lemma1. apply subst_lemma5. simpl. reflexivity. apply H7. rewrite <- E4 in H6. simpl in H6. destruct (have_string "s2" M1) eqn:EE1. discriminate. apply H6.
                    +++ eapply multi_step.
                      ++++ apply subst_lemma3. apply beta_abs. apply beta_appabs.
                      ++++ simpl. eapply multi_step.
                        +++++ apply subst_lemma3. apply beta_abs. apply beta_l. apply subst_lemma1. apply subst_lemma5. simpl. reflexivity. apply H9. apply H18.
                        +++++ assert(HH2: (subst "f" f' (trans_M "f" "s1" M1)) =b (app "s1" (subst "f" f0 M1))).
                            { apply multib_eq_be. rewrite H1 in IHM1. rewrite <- E4 in IHM1. apply IHM1. 
                              - rewrite <- E4 in H0.  simpl in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E4 in H0. destruct H0. rewrite <-E4 in H0. rewrite H1 in H0. apply H0. - rewrite <- E4 in H5. simpl in H5. destruct (have_string "s1" M1) eqn:EE1. discriminate H5. reflexivity. - rewrite <- E4 in H6. simpl in H6. destruct (have_string "s2" M1). discriminate H6. reflexivity.  - rewrite <-E4 in H15. simpl in H15. destruct (have_string "s" M1). discriminate. reflexivity. 
                              - rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. reflexivity. 
                              - rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. reflexivity.
                              - simpl. reflexivity. - simpl. reflexivity. - simpl. reflexivity. - simpl. reflexivity. }  
                            eapply multi_step.
                          ++++++ apply subst_lemma2. apply HH2. 
                          ++++++ simpl.  eapply multi_step.
                            -- apply beta_appabs.
                            -- simpl. eapply multi_step. apply beta_l. apply subst_lemma1. apply subst_lemma5. simpl. reflexivity. apply H8. apply H17.
                               eapply multi_step. apply beta_r. apply beta_r. apply subst_lemma1. apply subst_lemma5. 
                               simpl. reflexivity. apply H11. 
                               rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. apply H19.
                               eapply multi_step. apply beta_r. apply beta_l. apply subst_lemma1. apply subst_lemma5. simpl. reflexivity. apply H10.
                               rewrite <- E4 in H5. simpl in H5. destruct (have_string "s1" M1) eqn:EE1. discriminate. reflexivity.
                               eapply multi_step. apply beta_l. apply subst_lemma1. rewrite <- H1. apply H. apply multib_eq_be. apply beta_refl.
      * rewrite <- E4 in H0; simpl in H0.  rewrite E2 in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E4 in H0. rewrite <- E4 in H0. 
          destruct H0. rewrite E4 in H0. simpl in H0. 
          rewrite E4 in E1. simpl in E1. rewrite E1 in H0. destruct H0.
      * simpl in E1. discriminate E1.
      * simpl in E1. discriminate E1.
      * rewrite <- E4 in H0; simpl in H0.  rewrite E2 in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E4 in H0. rewrite <- E4 in H0. 
          destruct H0. rewrite E4 in H0. simpl in H0. rewrite E4 in E1. simpl in E1. rewrite E1 in H0. destruct H0.
      * rewrite <- E4 in H0; simpl in H0.  rewrite E2 in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E4 in H0. rewrite <- E4 in H0. 
          destruct H0. rewrite E4 in H0. simpl in H0. rewrite E4 in E1. simpl in E1. rewrite E1 in H0. destruct H0.
      * rewrite <- E4 in H0; simpl in H0.  rewrite E2 in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E4 in H0. rewrite <- E4 in H0. 
          destruct H0. rewrite E4 in H0. simpl in H0. rewrite E4 in E1. simpl in E1. rewrite E1 in H0. destruct H0. 
    + destruct M1 as [] eqn:E4.
      * destruct (F =? s) eqn:E5. 
        ** simpl. rewrite E5. Search(_ =? _). rewrite eqb_sym. rewrite E5. simpl. rewrite eqb_refl. eapply multi_step.
          apply beta_l. apply beta_r. apply subst_lemma1. apply E2. eapply multi_step.
          apply beta_r. apply subst_lemma1. apply H. apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step.
          apply beta_r. apply beta_r. apply subst_lemma1. apply E2. apply multib_eq_be. apply H2.
        ** simpl in E1. rewrite E5 in E1. discriminate E1.
      * rewrite <- E4. rewrite <-E4 in E1. simpl. rewrite E1. rewrite E2. rewrite E4. eapply multi_step. apply multib_eq_be. apply IHM1. 
        rewrite <-E4 in H0. simpl in H0. rewrite E1 in H0. rewrite E4 in H0. destruct H0. apply H0. rewrite <- E4 in H5. simpl in H5. 
        ** destruct (have_string "s1" M1) eqn: EE1. 
          *** discriminate.
          *** rewrite <-E4. apply EE1.
        ** destruct (have_string "s2" M1) eqn: EE2.
          *** rewrite <- E4 in H6. simpl in H6. rewrite EE2 in H6. discriminate.
          *** rewrite <- E4. apply EE2.
        ** rewrite <- E4. rewrite <- E4 in H15. simpl in H15. destruct (have_string "s" M1) eqn:EE1. discriminate. reflexivity.
        ** rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. rewrite <- E4. apply EE1. 
        ** rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. rewrite <- E4. apply EE1. 
        ** simpl. apply eqb_eq in H1. rewrite H1. simpl. rewrite <- H1. rewrite H. rewrite E2. reflexivity.  
        ** simpl. reflexivity.
        ** simpl. rewrite H17. rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. apply H19.
        ** simpl. rewrite H18. rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. apply H20.
        ** rewrite <- E4. eapply multi_step.
           apply beta_appabs. simpl. eapply multi_step.
           apply beta_l. apply subst_lemma1. apply H13. eapply multi_step.
           apply beta_r. apply beta_r. apply subst_lemma1. rewrite <- E4 in H15. simpl in H15. destruct (have_string "s" M1) eqn:EE1. discriminate. apply H15. apply multib_eq_be.
           apply beta_symm. apply multib_eq_be. eapply multi_step.
           apply beta_r. apply beta_r. apply subst_lemma1. apply E2. apply multib_eq_be. apply beta_refl.
      * rewrite <- E4 in H0; simpl in H0.  rewrite E2 in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E4 in H0. rewrite <- E4 in H0. 
          destruct H0. rewrite E4 in H0. simpl in H0. rewrite E4 in E1. simpl in E1. rewrite E1 in H0. destruct H0.
      * simpl in E1. discriminate.
      * simpl in E1. discriminate.
      * rewrite <- E4 in H0; simpl in H0.  rewrite E2 in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E4 in H0. rewrite <- E4 in H0. 
          destruct H0. rewrite E4 in H0. simpl in H0. rewrite E4 in E1. simpl in E1. rewrite E1 in H0. destruct H0.
      * rewrite <- E4 in H0; simpl in H0.  rewrite E2 in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E4 in H0. rewrite <- E4 in H0. 
          destruct H0. rewrite E4 in H0. simpl in H0. rewrite E4 in E1. simpl in E1. rewrite E1 in H0. destruct H0. 
      * rewrite <- E4 in H0; simpl in H0.  rewrite E2 in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E4 in H0. rewrite <- E4 in H0. 
          destruct H0. rewrite E4 in H0. simpl in H0. rewrite E4 in E1. simpl in E1. rewrite E1 in H0. destruct H0. 
    + simpl. rewrite E1. rewrite E2.
      destruct M1 as [] eqn:E4.
      * simpl in E1. destruct (F =? s) eqn:E5.
        ** discriminate.
        ** simpl in H0. rewrite E5 in H0. rewrite E2 in H0. destruct H0.
      * eapply multi_step. apply multib_eq_be. apply IHM2. 
        ** rewrite <-E4 in H0. simpl in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E2 in H0. rewrite E4 in H0. destruct H0. apply H21.
        ** rewrite <- E4 in H5. simpl in H5. destruct (have_string "s1" M1) eqn:EE1. discriminate. apply H5.
        ** rewrite <- E4 in H6. simpl in H6. destruct (have_string "s2" M1) eqn:EE1. discriminate. apply H6.
        ** rewrite <- E4 in H15. simpl in H15. destruct (have_string "s" M1) eqn:EE1. discriminate. apply H15.
        ** rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. apply H19. 
        ** rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. apply H20.
        ** simpl. apply eqb_eq in H1. rewrite H1. simpl. rewrite <- H1. rewrite H. simpl in E1. rewrite E1. reflexivity.
        ** simpl. reflexivity.
        ** rewrite <- E4. simpl. rewrite H17. rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. simpl. rewrite H18. rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. eapply multi_step. apply beta_appabs. eapply multi_step. simpl. apply beta_l. apply subst_lemma1. apply H13. eapply multi_step.
           apply beta_r. apply beta_l. apply subst_lemma1. rewrite <-E4 in H15. simpl in H15. destruct (have_string "s" M1). discriminate. reflexivity.
           apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step. apply beta_r. apply beta_l. apply subst_lemma1. rewrite E4. apply E1.
           apply multib_eq_be. apply beta_refl.
      * eapply multi_step. apply multib_eq_be. apply IHM2. 
        ** rewrite <- E4 in H0. simpl in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E2 in H0. rewrite E4 in H0. destruct H0. apply H21.
        ** rewrite <- E4 in H5. simpl in H5. destruct (have_string "s1" M1) eqn:EE1. discriminate. apply H5.
        ** rewrite <- E4 in H6. simpl in H6. destruct (have_string "s2" M1) eqn:EE1. discriminate. apply H6.
        ** rewrite <- E4 in H15. simpl in H15. destruct (have_string "s" M1) eqn:EE1. discriminate. apply H15.
        ** rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. apply H19. 
        ** rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. apply H20.
        ** rewrite <- E4 in E1. rewrite <- E4. simpl. apply eqb_eq in H1. rewrite H1. simpl. rewrite <- H1. rewrite H.  simpl in E1. rewrite E1. reflexivity.
        ** simpl. reflexivity.
        ** rewrite <- E4. simpl. rewrite H17. rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. simpl. rewrite H18. rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. eapply multi_step. apply beta_appabs. eapply multi_step. simpl. apply beta_l. apply subst_lemma1. apply H13. eapply multi_step.
           apply beta_r. apply beta_l. apply subst_lemma1. rewrite <-E4 in H15. simpl in H15. destruct (have_string "s" M1). discriminate. reflexivity.
           apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step. apply beta_r. apply beta_l. apply subst_lemma1. rewrite E4. apply E1.
           apply multib_eq_be. apply beta_refl.
      * eapply multi_step. apply multib_eq_be. apply IHM2. 
        ** rewrite <- E4 in H0. simpl in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E2 in H0. rewrite E4 in H0. destruct H0. apply H21.
        ** rewrite <- E4 in H5. simpl in H5. destruct (have_string "s1" M1) eqn:EE1. discriminate. apply H5.
        ** rewrite <- E4 in H6. simpl in H6. destruct (have_string "s2" M1) eqn:EE1. discriminate. apply H6.
        ** rewrite <- E4 in H15. simpl in H15. destruct (have_string "s" M1) eqn:EE1. discriminate. apply H15.
        ** rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. apply H19. 
        ** rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. apply H20.
        ** rewrite <- E4 in E1. rewrite <- E4. simpl. apply eqb_eq in H1. rewrite H1. simpl. rewrite <- H1. rewrite H.  simpl in E1. rewrite E1. reflexivity.
        ** simpl. reflexivity.
        ** rewrite <- E4. simpl. rewrite H17. rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. simpl. rewrite H18. rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. eapply multi_step. apply beta_appabs. eapply multi_step. simpl. apply beta_l. apply subst_lemma1. apply H13. eapply multi_step.
           apply beta_r. apply beta_l. apply subst_lemma1. rewrite <-E4 in H15. simpl in H15. destruct (have_string "s" M1). discriminate. reflexivity.
           apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step. apply beta_r. apply beta_l. apply subst_lemma1. rewrite E4. apply E1.
           apply multib_eq_be. apply beta_refl.
     * eapply multi_step. apply multib_eq_be. apply IHM2. 
        ** rewrite <- E4 in H0. simpl in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E2 in H0. rewrite E4 in H0. destruct H0. apply H21.
        ** rewrite <- E4 in H5. simpl in H5. destruct (have_string "s1" M1) eqn:EE1. discriminate. apply H5.
        ** rewrite <- E4 in H6. simpl in H6. destruct (have_string "s2" M1) eqn:EE1. discriminate. apply H6.
        ** rewrite <- E4 in H15. simpl in H15. destruct (have_string "s" M1) eqn:EE1. discriminate. apply H15.
        ** rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. apply H19. 
        ** rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. apply H20.
        ** rewrite <- E4 in E1. rewrite <- E4. simpl. apply eqb_eq in H1. rewrite H1. simpl. rewrite <- H1. rewrite H.  simpl in E1. rewrite E1. reflexivity.
        ** simpl. reflexivity.
        ** rewrite <- E4. simpl. rewrite H17. rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. simpl. rewrite H18. rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. eapply multi_step. apply beta_appabs. eapply multi_step. simpl. apply beta_l. apply subst_lemma1. apply H13. eapply multi_step.
           apply beta_r. apply beta_l. apply subst_lemma1. rewrite <-E4 in H15. simpl in H15. destruct (have_string "s" M1). discriminate. reflexivity.
           apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step. apply beta_r. apply beta_l. apply subst_lemma1. rewrite E4. apply E1.
           apply multib_eq_be. apply beta_refl.
     * eapply multi_step. apply multib_eq_be. apply IHM2. 
        ** rewrite <- E4 in H0. simpl in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E2 in H0. rewrite E4 in H0. destruct H0. apply H21.
        ** rewrite <- E4 in H5. simpl in H5. destruct (have_string "s1" M1) eqn:EE1. discriminate. apply H5.
        ** rewrite <- E4 in H6. simpl in H6. destruct (have_string "s2" M1) eqn:EE1. discriminate. apply H6.
        ** rewrite <- E4 in H15. simpl in H15. destruct (have_string "s" M1) eqn:EE1. discriminate. apply H15.
        ** rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. apply H19. 
        ** rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. apply H20.
        ** rewrite <- E4 in E1. rewrite <- E4. simpl. apply eqb_eq in H1. rewrite H1. simpl. rewrite <- H1. rewrite H.  simpl in E1. rewrite E1. reflexivity.
        ** simpl. reflexivity.
        ** rewrite <- E4. simpl. rewrite H17. rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. simpl. rewrite H18. rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. eapply multi_step. apply beta_appabs. eapply multi_step. simpl. apply beta_l. apply subst_lemma1. apply H13. eapply multi_step.
           apply beta_r. apply beta_l. apply subst_lemma1. rewrite <-E4 in H15. simpl in H15. destruct (have_string "s" M1). discriminate. reflexivity.
           apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step. apply beta_r. apply beta_l. apply subst_lemma1. rewrite E4. apply E1.
           apply multib_eq_be. apply beta_refl.
      * eapply multi_step. apply multib_eq_be. apply IHM2. 
        ** rewrite <- E4 in H0. simpl in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E2 in H0. rewrite E4 in H0. destruct H0. apply H21.
        ** rewrite <- E4 in H5. simpl in H5. destruct (have_string "s1" M1) eqn:EE1. discriminate. apply H5.
        ** rewrite <- E4 in H6. simpl in H6. destruct (have_string "s2" M1) eqn:EE1. discriminate. apply H6.
        ** rewrite <- E4 in H15. simpl in H15. destruct (have_string "s" M1) eqn:EE1. discriminate. apply H15.
        ** rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. apply H19. 
        ** rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. apply H20.
        ** rewrite <- E4 in E1. rewrite <- E4. simpl. apply eqb_eq in H1. rewrite H1. simpl. rewrite <- H1. rewrite H.  simpl in E1. rewrite E1. reflexivity.
        ** simpl. reflexivity.
        ** rewrite <- E4. simpl. rewrite H17. rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. simpl. rewrite H18. rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. eapply multi_step. apply beta_appabs. eapply multi_step. simpl. apply beta_l. apply subst_lemma1. apply H13. eapply multi_step.
           apply beta_r. apply beta_l. apply subst_lemma1. rewrite <-E4 in H15. simpl in H15. destruct (have_string "s" M1). discriminate. reflexivity.
           apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step. apply beta_r. apply beta_l. apply subst_lemma1. rewrite E4. apply E1.
           apply multib_eq_be. apply beta_refl.
     * eapply multi_step. apply multib_eq_be. apply IHM2. 
        ** rewrite <- E4 in H0. simpl in H0. rewrite <- E4 in E1. rewrite E1 in H0. rewrite E2 in H0. rewrite E4 in H0. destruct H0. apply H21.
        ** rewrite <- E4 in H5. simpl in H5. destruct (have_string "s1" M1) eqn:EE1. discriminate. apply H5.
        ** rewrite <- E4 in H6. simpl in H6. destruct (have_string "s2" M1) eqn:EE1. discriminate. apply H6.
        ** rewrite <- E4 in H15. simpl in H15. destruct (have_string "s" M1) eqn:EE1. discriminate. apply H15.
        ** rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. apply H19. 
        ** rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. apply H20.
        ** rewrite <- E4 in E1. rewrite <- E4. simpl. apply eqb_eq in H1. rewrite H1. simpl. rewrite <- H1. rewrite H.  simpl in E1. rewrite E1. reflexivity.
        ** simpl. reflexivity.
        ** rewrite <- E4. simpl. rewrite H17. rewrite <- E4 in H19. simpl in H19. destruct (have_string "res1" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. simpl. rewrite H18. rewrite <- E4 in H20. simpl in H20. destruct (have_string "res2" M1) eqn:EE1. discriminate. reflexivity. 
        ** rewrite <- E4. eapply multi_step. apply beta_appabs. eapply multi_step. simpl. apply beta_l. apply subst_lemma1. apply H13. eapply multi_step.
           apply beta_r. apply beta_l. apply subst_lemma1. rewrite <-E4 in H15. simpl in H15. destruct (have_string "s" M1). discriminate. reflexivity.
           apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step. apply beta_r. apply beta_l. apply subst_lemma1. rewrite E4. apply E1.
           apply multib_eq_be. apply beta_refl.
    + eapply multi_step. simpl. rewrite E1. rewrite E2. apply subst_lemma1. simpl. rewrite H. rewrite E1. rewrite E2. reflexivity.
       apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step. apply beta_r. apply subst_lemma1. simpl. rewrite E1. apply E2. apply multib_eq_be. apply beta_refl.
  - simpl in H0. destruct (F =? s) eqn:E1.
    + simpl. rewrite E1. eapply multi_step. apply subst_lemma1. simpl. rewrite H. rewrite E1. reflexivity. apply multib_eq_be. apply beta_refl.
    + simpl. rewrite E1. destruct (have_string F M) eqn:E2. destruct H0. eapply multi_step. apply subst_lemma1. simpl. rewrite H. rewrite E1. apply E2. apply multib_eq_be. apply beta_symm. apply multib_eq_be.
      eapply multi_step. apply beta_r. apply beta_abs. apply subst_lemma1. apply E2. apply multib_eq_be. apply beta_refl.
  - simpl. eapply multi_step. apply beta_l. apply subst_lemma1. apply H. apply multib_eq_be. apply beta_refl.
  - simpl. eapply multi_step. apply beta_l. apply subst_lemma1. apply H. apply multib_eq_be. apply beta_refl.
  - simpl in H0. destruct (have_string F M1) eqn:E1. destruct H0. destruct (have_string F M2) eqn:E2. destruct H0. destruct (have_string F M3) eqn:E3. destruct H0.
    apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step. apply beta_r. apply subst_lemma1. simpl. rewrite E1. rewrite E2. rewrite E3. reflexivity.
    simpl. rewrite E1. rewrite E2. rewrite E3. apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step. apply subst_lemma1.  simpl. rewrite E1. rewrite E2. rewrite E3. rewrite H. reflexivity.
    apply multib_eq_be. apply beta_refl.
  - simpl in H0. destruct(F =? s) eqn:E0; destruct(have_string F M1) eqn:E1. destruct H0. 
    + simpl. rewrite E0. rewrite E1. eapply multi_step. apply subst_lemma1. simpl. rewrite H. rewrite E0. apply E1. apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step.
      apply beta_r. apply beta_let1. apply subst_lemma1. apply E1. apply beta_refl. apply multib_eq_be. apply beta_refl.
    + destruct H0. 
    + destruct(have_string F M2) eqn:E2. destruct H0. eapply multi_step. simpl. apply subst_lemma1. simpl. rewrite E0. rewrite E1. rewrite E2. simpl. rewrite H. rewrite E0. rewrite E1. rewrite E2. reflexivity.
      rewrite E0. rewrite E1. rewrite E2. 
      apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step. apply beta_r. apply subst_lemma1. simpl. rewrite E0. rewrite E1. rewrite E2. reflexivity.
      apply multib_eq_be. apply beta_refl.
  - simpl in H0. destruct(have_string F M) eqn:E1. destruct H0. eapply multi_step. simpl. rewrite E1. apply subst_lemma1. simpl. rewrite H. apply E1.
    apply multib_eq_be. apply beta_symm. apply multib_eq_be. eapply multi_step. apply beta_r. apply subst_lemma1. simpl. apply E1.
    apply multib_eq_be. apply beta_refl.
  Qed.

(* Theorem m_k : forall (F k:tm)(n: nat),
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
             *)

(*  Theorem m_k__k_m : forall (F k M:tm) (f:string),
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
  destruct t2 eqn:E5; try destruct H0. *)
  

  


Check fact.

Compute fact.

Compute trans_to_tail_recursion fact.


Example test_mlt_cont_trans1 :
  multistep (app (app (trans_to_tail_recursion fact) 4) (abs "s" "s")) 24.
Proof.
  unfold trans_to_tail_recursion.
  unfold fact.
  unfold trans_M.
  normalize.
  Qed.

Example test_mlt_cont_trans2 :
  multistep (app (app (trans_to_tail_recursion fact2) 4)(abs "s" "s"))  24.
Proof.
  unfold trans_to_tail_recursion.
  unfold fact2.
  unfold trans_M.
  normalize.
  Qed.

Compute trans_to_tail_recursion fact_pls.

Example test_mlt_pls_cont_trans1 :
  multistep (app (app (trans_to_tail_recursion fact_pls) 4) (abs "s" "s")) 88.
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
    (abs f 
      (abs x 
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
  multistep (app (app double_fact_cont 3)(abs "s" "s")) 144.
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






