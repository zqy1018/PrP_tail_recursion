Set Warnings "-notation-overridden,-parsing".
From TRO Require Import Smallstep.
From Coq Require Import Strings.String.

Inductive ty : Type :=
  | Nat : ty
  | Arrow : ty -> ty -> ty
  | List : ty -> ty
  | Cont : ty -> ty
.

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  
  | const : nat -> tm
  | min : tm -> tm -> tm
  | pls : tm -> tm -> tm
  | mlt : tm -> tm -> tm
  | test0 : tm -> tm -> tm -> tm 
  
  | tlet : string -> tm -> tm -> tm
  
  | tfix : tm -> tm
  | tnil : ty -> tm
  | tcons : tm -> tm -> tm
  | tlcase : tm -> tm -> string -> string -> tm -> tm
.

Coercion var: string >-> tm.
Coercion const: nat >-> tm.

Fixpoint subst (x : string) (s: tm) (t:tm) :tm :=
  match t with
  | var y =>   
          if eqb x y then s else t
  | app t1 t2 =>
          app (subst x s t1) (subst x s t2)
  | abs y T t1 => 
          if eqb x y then (abs y T t1) else (abs y T (subst x s t1))
  | const n =>
          const n
  | min t1 t2 => min (subst x s t1) (subst x s t2)
  | mlt t1 t2 =>
          mlt (subst x s t1) (subst x s t2)
  | pls t1 t2 =>
          pls (subst x s t1) (subst x s t2)
  | test0 t1 t2 t3 =>
          test0 (subst x s t1) (subst x s t2) (subst x s t3)
  | tlet y t1 t2 => 
          tlet y (subst x s t1) (if eqb x y then t2 else (subst x s t2))      
  | tfix t1 =>
          tfix (subst x s t1)
  | tnil T =>
          tnil T
  | tcons t1 t2 =>
          tcons (subst x s t1) (subst x s t2)
  | tlcase t1 t2 y1 y2 t3 =>
          tlcase (subst x s t1) (subst x s t2) y1 y2 (if eqb y1 x then t3 else if eqb y2 x then t3 else (subst x s t3))  
end.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_const : forall n,
      value (const n)
  | v_lnil : forall T, 
      value (tnil T)
  | v_lcons : forall v1 vl,
      value v1 ->
      value vl ->
      value (tcons v1 vl)
.
Hint Constructors value.

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t v,
                value v ->
                step (app (abs x T t) v) (subst x v t)
  | ST_App1 : forall t1 t1' t2,
              step t1 t1' ->
              step (app t1 t2) (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
              value v1 ->
              step t2 t2' ->
              step (app v1 t2) (app v1 t2')
  | ST_Min1 : forall t1 t1' t2,
              step t1 t1' ->
              step (min t1 t2) (min t1' t2)
  | ST_Min2 : forall v1 t2 t2',
              value v1 ->
              step t2 t2' ->
              step (min v1 t2) (min v1 t2')
  | ST_Minconsts : forall n1 n2,
              step (min (const n1) (const n2)) (const (n1 - n2))
  | ST_Plus1 : forall t1 t1' t2,
              step t1 t1' ->
              step (pls t1 t2) (pls t1' t2)
  | ST_Plus2 : forall v1 t2 t2',
              value v1 ->
              step t2 t2' ->
              step (pls v1 t2) (pls v1 t2')
  | ST_Plusconsts : forall n1 n2,
              step (pls (const n1) (const n2)) (const (plus n1 n2))
  | ST_Mult1 : forall t1 t1' t2,
              step t1 t1' -> 
              step (mlt t1 t2) (mlt t1' t2)
  | ST_Mult2 : forall v t2 t2',
              value v ->
              step t2 t2' ->
              step (mlt v t2) (mlt v t2')
  | ST_Multconsts: forall n1 n2,  
              step (mlt (const n1) (const n2)) (const (mult n1 n2))
  | ST_Test01: forall t1 t1' t2 t3,
              step t1 t1' ->
              step (test0 t1 t2 t3) (test0 t1' t2 t3)
  | ST_Test0Zro : forall t2 t3,
              step (test0 (const 0) t2 t3) t2
  | ST_Test0NotZro: forall n t2 t3,
              step (test0 (const (S n)) t2 t3) t3
  | ST_Let1 : forall x t1 t2 t1',
              step t1 t1' ->
              step (tlet x t1 t2) (tlet x t1' t2)
  | ST_LetValue : forall x v1 t2,
              value v1 ->
              step (tlet x v1 t2) (subst x v1 t2)
  | ST_Fix1 : forall t1 t1',
              step t1 t1' ->
              step (tfix t1) (tfix t1')
  | ST_FixAbs: forall xf T1 t2,
              step (tfix (abs xf T1 t2)) (subst xf (tfix (abs xf T1 t2)) t2)
  | ST_Cons1 : forall t1 t1' t2,
              step t1 t1' ->
              step (tcons t1 t2) (tcons t1' t2)
  | ST_Cons2 : forall v1 t2 t2',
              value v1 -> 
              step t2 t2' ->
              step (tcons v1 t2) (tcons v1 t2')
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
              step t1 t1' ->
              step (tlcase t1 t2 x1 x2 t3) (tlcase t1' t2 x1 x2 t3)
  | ST_LcaseNil : forall T t2 x1 x2 t3,
              step (tlcase (tnil T) t2 x1 x2 t3) t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
              value v1 ->
              value vl ->
              step (tlcase (tcons v1 vl) t2 x1 x2 t3) (subst x2 vl (subst x1 v1 t3))
.
Hint Constructors step.
Notation multistep := (multi step).
Notation "t1 '+' t2" := (pls t1 t2).
Notation "t1 '*' t2" := (mlt t1 t2).
Notation "t1 '-' t2" := (min t1 t2).




Definition test :=
  test0
    (min
      (pls
        (
          (2 * 0) - 1) 1) 1)
    (const 5)
    (const 6).

Example cal:
 multistep test (const 5).
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
  (abs x Nat (var x)).


Notation idBB :=
  (abs x (Arrow Nat Nat) (var x)).

Example reduces1 :
  multistep (app idB (const 4)) (const 4).
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
    (abs "f" (Arrow Nat Nat)
      (abs "a" Nat
        (test0
           (var "a")
           (const 1)
           (mlt
              (var "a")
              (app (var "f") ((var "a") - 1)))))).



Example reduces2 :
  multistep (app fact (const 4)) (const 24).
Proof.
  unfold fact.
  normalize.
  Qed.

Definition fact2 :=
  tfix
    (abs "f" (Arrow Nat Nat)
      (abs "a" Nat
        (test0
           (var "a")
           (const 1)
           (mlt
              (app (var "f") ((var "a") - 1))
              (var "a"))))).

Definition fact_pls :=
  tfix
    (abs "f" (Arrow Nat Nat)
      (abs "a" Nat
        (test0
           (var "a")
           (const 1)
           ("a" + "a" * (app "f" ("a" - 1)))))).

Definition mlt_pls_cont := 
  tfix 
    (abs f (Arrow Nat (Cont Nat))
      (abs x Nat
        (abs c (Cont Nat)
          (test0
            (var x)
            (app c 1)
            (app 
              (app f (x - 1))
              (abs "s" (Cont Nat) 
                (app c 
                  (x + x * "s")))))))).

(** 0 -> 1, 1 -> 2, 2 -> 6, 3 -> 21 , 4 -> 88**)
Example reduces3 :
  multistep (app fact_pls (const 4)) (const 88).
Proof.
  unfold fact_pls.
  normalize.
  Qed.

Example reduces4:
  multistep (app (app mlt_pls_cont 4) (abs "s" Nat "s")) (const 88).
Proof.
  unfold mlt_pls_cont.
  normalize.
  Qed.


Definition mlt_cont := 
  tfix 
    (abs f (Arrow Nat (Cont Nat))
      (abs x Nat
        (abs c (Cont Nat)
          (test0
            (var x)
            (app (var c) 1)
            (app 
              (app (var f) (x - 1))
              (abs "s" (Cont Nat) 
                (app (var c) 
                  (mlt (var "s") (var x))))))))).



Example test_mlt_cont :
  multistep (app (app mlt_cont 4) (abs "s" Nat (var "s"))) 24.
Proof.
  unfold mlt_cont.
  normalize.
  Qed.

Definition l := "l".
Definition hd := "hd".
Definition tail := "tail".

Definition test_list :=
  tlet l
    (tcons (const 5) (tcons (const 6) (tnil Nat)))
    (tlcase (var l)
       (const 0)
       x y (mlt (var x) (var x))).

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
          hd tail (pls (var hd) 
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
              (abs "s" (Cont Nat) (app (var c) (pls (var hd) (var "s"))))))))).

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
  Qed.
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
  | abs y T t1 => 
          if eqb x y then false else have_string x t1
  | const n => false
  | min t1 t2 => if (have_string x t1) 
                  then true 
                  else have_string x t2
  | mlt t1 t2 => if (have_string x t1) 
                  then true 
                  else have_string x t2
  | pls t1 t2 => if (have_string x t1) 
                  then true 
                  else have_string x t2
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

  | tnil T => false
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
                                        else have_string x t3  
end.

Fixpoint trans_M (f : string) (k t3:tm) :=
  match t3 with 
  | app f t4 => app (app f t4)k
  | m1 * m2 => if have_string f m1 
                  then if have_string f m2
                        then
                          tlet "fs1"
                            (abs "s1" (Cont Nat) 
                              (tlet "fs2" 
                                (abs "s2" (Cont Nat) (app k ("s1" * "s2")))
                                (trans_M f "fs2" m2)))
                            (trans_M f "fs1" m1)
                        else
                          tlet "fs" 
                            (abs "s" (Cont Nat) (app k ("s" * m2))) 
                            (trans_M f "fs" m1)
                  else if have_string f m2
                        then
                          tlet "fs" 
                            (abs "s" (Cont Nat) (app k (m1 * "s"))) 
                            (trans_M f "fs" m2)
                        else 
                          app t3 k
  | m1 + m2 => if have_string f m1 
                  then if have_string f m2
                        then
                          tlet "fs1"
                            (abs "s1" (Cont Nat) 
                              (tlet "fs2" 
                                (abs "s2" (Cont Nat) (app k ("s1" + "s2")))
                                (trans_M f "fs2" m2)))
                            (trans_M f "fs1" m1)
                        else
                          tlet "fs" 
                            (abs "s" (Cont Nat) (app k ("s" + m2))) 
                            (trans_M f "fs" m1)
                  else if have_string f m2
                        then
                          tlet "fs" 
                            (abs "s" (Cont Nat) (app k (m1 + "s"))) 
                            (trans_M f "fs" m2)
                        else 
                          app t3 k
  | m1 - m2 => if have_string f m1 
                  then if have_string f m2
                        then
                          tlet "fs1"
                            (abs "s1" (Cont Nat) 
                              (tlet "fs2" 
                                (abs "s2" (Cont Nat) (app k ("s1" - "s2")))
                                (trans_M f "fs2" m2)))
                            (trans_M f "fs1" m1)
                        else
                          tlet "fs" 
                            (abs "s" (Cont Nat) (app k ("s" - m2))) 
                            (trans_M f "fs" m1)
                  else if have_string f m2
                        then
                          tlet "fs" 
                            (abs "s" (Cont Nat) (app k (m1 - "s"))) 
                            (trans_M f "fs" m2)
                        else 
                          app t3 k
  | _ => app t3 k
  end.

Compute (trans_M "f" "k" (1 + (1 + (app (var "f") (var "l'"))))).

Definition trans_to_tail_recursion (F:tm):=
  match F with
  | tfix (abs f Tf 
       (abs a Ta t )) => match t with
                        | test0 t1 t2 t3 => tfix (abs f Tf
                                              (abs a Ta 
                                                (abs c (Cont Ta)
                                                  (test0 t1
                                                    (app c t2)
                                                    (trans_M f c t3)))))
                        | tlcase t1 t2 y1 y2 t3 => tfix (abs f Tf
                                                    (abs a Ta
                                                      (abs c (Cont Ta)
                                                        (tlcase t1 
                                                          (app c t2)
                                                          y1 y2
                                                          (trans_M f c t3)))))
                        | _ => F
                        end
  | _ => F
  end.

Check fact.

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
  multistep (app (app (trans_to_tail_recursion fact2) 4) (abs "s" Nat "s")) 24.
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
Definition sum_list_cont3 := trans_to_tail_recursion sum_list.

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
  Qed.

Definition double_recursion_fact :=
  tfix
    (abs f (Arrow Nat Nat)
      (abs x Nat
        (test0
           x
           1
           ((x * (app f (x-1))) * (x * (app f (x-1))))))).

Example test_double_fact:
  multistep (app double_recursion_fact 3) 144.
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
  multistep (app forth_sum 3) 64.
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




