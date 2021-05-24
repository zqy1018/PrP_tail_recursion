From STLC Require Export Definitions.
From STLC Require Export Argument.
From Coq Require Import Logic.FunctionalExtensionality.
(*From Coq Require Import List.
Import ListNotations.*)

Print tm.
Print depth.
Print CPS.

Inductive stlc_expr (func_name : string) : tm -> Prop :=
  | E_Var : forall x1,
        eqb func_name x1 = false ->
        stlc_expr func_name (var x1)
  | E_Abs : forall x1 t1 t2,
       eqb func_name x1 = false ->
       stlc_expr func_name t1 ->
       stlc_expr func_name t2 ->
       stlc_expr func_name (app (abs x1 t1) t2)
  | E_AppF : forall t1,
       stlc_expr func_name t1 ->
       stlc_expr func_name (app (var func_name) t1)
  | E_App : forall t1 t2,
       stlc_expr func_name t1 ->
       stlc_expr func_name t2 ->
       stlc_expr func_name (app t1 t2)
  
  | E_Const : forall n,
       stlc_expr func_name (tconst n)
  | E_Plus : forall t1 t2,
       stlc_expr func_name t1 ->
       stlc_expr func_name t2 ->
       stlc_expr func_name (tplus t1 t2)
  | E_Minus : forall t1 t2,
       stlc_expr func_name t1 ->
       stlc_expr func_name t2 ->
       stlc_expr func_name (tminus t1 t2)
  | E_Mult : forall t1 t2,
       stlc_expr func_name t1 ->
       stlc_expr func_name t2 ->
       stlc_expr func_name (tmult t1 t2)
  | E_If0 : forall t1 t2 t3,
       stlc_expr func_name t1 ->
       stlc_expr func_name t2 ->
       stlc_expr func_name t3 ->
       stlc_expr func_name (tif0 t1 t2 t3)
  
  | E_Nil :
       stlc_expr func_name tnil
  | E_Cons : forall t1 t2,
       stlc_expr func_name t1 ->
       stlc_expr func_name t2 ->
       stlc_expr func_name (tcons t1 t2)
  | E_LCase : forall t1 t2 x1 x2 t3,
       eqb func_name x1 = false ->
       eqb func_name x2 = false ->
       stlc_expr func_name t1 ->
       stlc_expr func_name t2 ->
       stlc_expr func_name t3 ->
       stlc_expr func_name (tlcase t1 t2 x1 x2 t3)

  | E_Let : forall x1 t1 t2,
       eqb func_name x1 = false ->
       stlc_expr func_name t1 ->
       stlc_expr func_name t2 ->
       stlc_expr func_name (tlet x1 t1 t2).

Reserved Notation "t1 '=s' t2" (at level 50).

Inductive stlc_eqb : tm -> tm -> Prop :=
  | S_Refl : forall x1,
       x1 =s x1
  | S_Symm : forall x1 x2,
       x1 =s x2 ->
       x2 =s x1
  | S_Trans : forall x1 x2 x3,
       x1 =s x2 ->
       x2 =s x3 ->
       x1 =s x3
  
  | S_App : forall t1 t1' t2 t2',
       t1 =s t1' ->
       t2 =s t2' ->
       app t1 t2 =s app t1' t2'
  | S_AppAbs : forall x y t,
       app (abs x t) y =s subst x y t
  | S_Abs : forall x t t',
       t =s t' ->
       abs x t =s abs x t'
  | S_AbsName : forall x y t,
       (List.In y (list_name t) -> False) ->
       abs x t =s abs y (subst x y t)
  
  | S_Plus : forall t1 t1' t2 t2',
       t1 =s t1' ->
       t2 =s t2' ->
       tplus t1 t2 =s tplus t1' t2'
  | S_Minus : forall t1 t1' t2 t2',
       t1 =s t1' ->
       t2 =s t2' ->
       tminus t1 t2 =s tminus t1' t2'
  | S_Mult : forall t1 t1' t2 t2',
       t1 =s t1' ->
       t2 =s t2' ->
       tmult t1 t2 =s tmult t1' t2'
  | S_If0 : forall t1 t1' t2 t2' t3 t3',
       t1 =s t1' ->
       t2 =s t2' ->
       t3 =s t3' ->
       tif0 t1 t2 t3 =s tif0 t1' t2' t3'
  | S_If0AppLeft : forall k t1 t2 t3,
       app k (tif0 t1 t2 t3) =s tif0 t1 (app k t2) (app k t3)
  | S_If0AppRight : forall k t1 t2 t3,
       app (tif0 t1 t2 t3) k =s tif0 t1 (app t2 k) (app t3 k)
  
  | S_Cons : forall t1 t1' t2 t2',
       t1 =s t1' ->
       t2 =s t2' ->
       tcons t1 t2 =s tcons t1' t2'
  | S_LCase : forall t1 t1' t2 t2' x1 x2 t3 t3',
       t1 =s t1' ->
       t2 =s t2' ->
       t3 =s t3' ->
       tlcase t1 t2 x1 x2 t3 =s tlcase t1' t2' x1 x2 t3'
  | S_LCaseAppLeft : forall k t1 t2 x1 x2 t3,
       app k (tlcase t1 t2 x1 x2 t3) =s tlcase t1 (app k t2) x1 x2 (app k t3)
  | S_LCaseAppRight : forall k t1 t2 x1 x2 t3,
       app (tlcase t1 t2 x1 x2 t3) k =s tlcase t1 (app t2 k) x1 x2 (app t3 k)
  
  | S_Let : forall x t1 t1' t2 t2',
       t1 =s t1' ->
       t2 =s t2' ->
       tlet x t1 t2 =s tlet x t1' t2'
  | S_LetSubst : forall x t1 t2,
       tlet x t1 t2 =s subst x t1 t2
  
  | S_Fix : forall t1 t1',
       t1 =s t1' ->
       tfix t1 =s tfix t1'
  | S_FixAbs : forall f t,
       tfix (abs f t) =s subst f (tfix (abs f t)) t

  where "t1 '=s' t2" := (stlc_eqb t1 t2).

Lemma depth_helper1 :
  forall m, exists n, S m = S n.
Proof.
  intros m. exists m. reflexivity.
Qed.

Lemma depth_gt_1 :
  forall F M, exists n, depth F M = S n.
Proof.
  intros. destruct M; simpl; try (apply depth_helper1); try (destruct (find_func F M1), (find_func F M2); apply depth_helper1).
  - destruct ((find_func F M1 =? 1) && (find_func F M2 =? 0) && is_recu F M1)%bool. apply depth_helper1.
  destruct (find_func F M1), (find_func F M2); apply depth_helper1.
Qed.

Lemma depth_helper2 :
  forall n m, exists k, n + k = Init.Nat.max n m.
Proof.
  Search "<=". intros. induction (Nat.le_max_l n m).
  - exists 0. apply Nat.add_comm.
  - destruct IHl. exists (S x). rewrite Nat.add_comm. simpl. f_equal. rewrite Nat.add_comm. apply H.
Qed.

Axiom stlc_functional_extensionality : forall (A : Type) (f g : A -> tm),
  (forall x : A, f x =s g x) -> f = g.

Theorem fuel_enough :
  forall k F M continuation naming n,
  CPS k F M continuation naming (depth F M) =s CPS k F M continuation naming (depth F M + n).
Proof.
  intros. generalize dependent naming. generalize dependent continuation. generalize dependent n. induction M.
  - intros n H naming. destruct (depth_gt_1 F <{ s }>). rewrite H0. simpl. apply S_Refl.
  - admit.
  - intros n H naming. destruct (depth_gt_1 F <{ \ s, M }>). simpl in H0. injection H0 as H0. simpl. apply S_Abs. apply IHM.
  - intros. simpl. apply S_Refl.
  - intros n H naming. destruct (depth_gt_1 F <{ M1 + M2 }>). rewrite H0. simpl in H0. simpl. destruct (find_func F M1), (find_func F M2); injection H0 as H0; try (rewrite <- H0).
    apply S_Refl. apply IHM2. apply IHM1. destruct (depth_helper2 (depth F M1) (depth F M2)). rewrite <- H1. eapply S_Trans. apply S_Symm. apply IHM1. rewrite Plus.plus_assoc_reverse.
    assert ((fun res1 : tm => CPS k F M2 (fun res2 : tm => H <{ res1 + res2 }>) (naming + S n0) (depth F M1 + x0)) = (fun res1 : tm => CPS k F M2 (fun res2 : tm => H <{ res1 + res2 }>) (naming + S n0) (depth F M1 + (x0 + n)))). {
    apply stlc_functional_extensionality. intros. rewrite <- Plus.plus_assoc_reverse. rewrite H1. destruct (depth_helper2 (depth F M2) (depth F M1)). rewrite Nat.max_comm in H2. rewrite <- H2. eapply S_Trans. apply S_Symm.
    apply (IHM2 x2 (fun res2 : tm => H <{ x1 + res2 }>) (naming + S n0)). rewrite Plus.plus_assoc_reverse. apply IHM2. } rewrite H2. apply IHM1.
  - intros n H naming. destruct (depth_gt_1 F <{ M1 - M2 }>). rewrite H0. simpl in H0. simpl. destruct (find_func F M1), (find_func F M2); injection H0 as H0; try (rewrite <- H0).
    apply S_Refl. apply IHM2. apply IHM1. destruct (depth_helper2 (depth F M1) (depth F M2)). rewrite <- H1. eapply S_Trans. apply S_Symm. apply IHM1. rewrite Plus.plus_assoc_reverse.
    assert ((fun res1 : tm => CPS k F M2 (fun res2 : tm => H <{ res1 - res2 }>) (naming + S n0) (depth F M1 + x0)) = (fun res1 : tm => CPS k F M2 (fun res2 : tm => H <{ res1 - res2 }>) (naming + S n0) (depth F M1 + (x0 + n)))). {
    apply stlc_functional_extensionality. intros. rewrite <- Plus.plus_assoc_reverse. rewrite H1. destruct (depth_helper2 (depth F M2) (depth F M1)). rewrite Nat.max_comm in H2. rewrite <- H2. eapply S_Trans. apply S_Symm.
    apply (IHM2 x2 (fun res2 : tm => H <{ x1 - res2 }>) (naming + S n0)). rewrite Plus.plus_assoc_reverse. apply IHM2. } rewrite H2. apply IHM1.
  - intros n H naming. destruct (depth_gt_1 F <{ M1 * M2 }>). rewrite H0. simpl in H0. simpl. destruct (find_func F M1), (find_func F M2); injection H0 as H0; try (rewrite <- H0).
    apply S_Refl. apply IHM2. apply IHM1. destruct (depth_helper2 (depth F M1) (depth F M2)). rewrite <- H1. eapply S_Trans. apply S_Symm. apply IHM1. rewrite Plus.plus_assoc_reverse.
    assert ((fun res1 : tm => CPS k F M2 (fun res2 : tm => H <{ res1 * res2 }>) (naming + S n0) (depth F M1 + x0)) = (fun res1 : tm => CPS k F M2 (fun res2 : tm => H <{ res1 * res2 }>) (naming + S n0) (depth F M1 + (x0 + n)))). {
    apply stlc_functional_extensionality. intros. rewrite <- Plus.plus_assoc_reverse. rewrite H1. destruct (depth_helper2 (depth F M2) (depth F M1)). rewrite Nat.max_comm in H2. rewrite <- H2. eapply S_Trans. apply S_Symm.
    apply (IHM2 x2 (fun res2 : tm => H <{ x1 * res2 }>) (naming + S n0)). rewrite Plus.plus_assoc_reverse. apply IHM2. } rewrite H2. apply IHM1.
  - intros n H naming. destruct (depth_gt_1 F <{ if0 M1 then M2 else M3 }>). rewrite H0. simpl in H0. simpl. destruct (find_func F M1). injection H0 as H0. apply S_If0. apply S_Refl. rewrite <- H0.
    destruct (depth_helper2 (depth F M2) (depth F M3)). rewrite <- H1. eapply S_Trans. apply S_Symm. apply IHM2. rewrite Plus.plus_assoc_reverse. apply IHM2. destruct (depth_helper2 (depth F M3) (depth F M2)). rewrite Nat.max_comm in H1.
    rewrite <- H0. rewrite <- H1. eapply S_Trans. apply S_Symm. apply IHM3. rewrite Plus.plus_assoc_reverse. apply IHM3. injection H0 as H0. rewrite <- H0. apply IHM1.
  - intros n H naming. simpl. apply S_Refl.
  - intros n H naming. destruct (depth_gt_1 F <{ M1 :: M2 }>). rewrite H0. simpl in H0. simpl. destruct (find_func F M1), (find_func F M2); injection H0 as H0; try (rewrite <- H0).
    apply S_Refl. apply IHM2. apply IHM1. destruct (depth_helper2 (depth F M1) (depth F M2)). rewrite <- H1. eapply S_Trans. apply S_Symm. apply IHM1. rewrite Plus.plus_assoc_reverse.
    assert ((fun res1 : tm => CPS k F M2 (fun res2 : tm => H <{ res1 :: res2 }>) (naming + S n0) (depth F M1 + x0)) = (fun res1 : tm => CPS k F M2 (fun res2 : tm => H <{ res1 :: res2 }>) (naming + S n0) (depth F M1 + (x0 + n)))). {
    apply stlc_functional_extensionality. intros. rewrite <- Plus.plus_assoc_reverse. rewrite H1. destruct (depth_helper2 (depth F M2) (depth F M1)). rewrite Nat.max_comm in H2. rewrite <- H2. eapply S_Trans. apply S_Symm.
    apply (IHM2 x2 (fun res2 : tm => H <{ x1 :: res2 }>) (naming + S n0)). rewrite Plus.plus_assoc_reverse. apply IHM2. } rewrite H2. apply IHM1.
  - intros n H naming. destruct (depth_gt_1 F <{ case M1 of | nil => M2 | s :: s0 => M3 }>). rewrite H0. simpl in H0. simpl. destruct (find_func F M1). injection H0 as H0. apply S_LCase. apply S_Refl. rewrite <- H0.
    destruct (depth_helper2 (depth F M2) (depth F M3)). rewrite <- H1. eapply S_Trans. apply S_Symm. apply IHM2. rewrite Plus.plus_assoc_reverse. apply IHM2. destruct (depth_helper2 (depth F M3) (depth F M2)). rewrite Nat.max_comm in H1.
    rewrite <- H0. rewrite <- H1. eapply S_Trans. apply S_Symm. apply IHM3. rewrite Plus.plus_assoc_reverse. apply IHM3. injection H0 as H0. rewrite <- H0. apply IHM1.
  - intros n H naming. simpl. apply S_Let. destruct (depth_helper2 (depth F M1) (depth F M2)). rewrite <- H0. eapply S_Trans. apply S_Symm. apply IHM1. rewrite Plus.plus_assoc_reverse. apply IHM1.
    destruct (depth_helper2 (depth F M2) (depth F M1)). rewrite Nat.max_comm in H0. rewrite <- H0. eapply S_Trans. apply S_Symm. apply IHM2. rewrite Plus.plus_assoc_reverse. apply IHM2.
  - intros n H naming. simpl. apply S_Fix. apply IHM.
  Admitted.

Theorem naming_arbitrarility :
  forall k F M continuation n,
  CPS k F M continuation 1 (depth F M) =s CPS k F M continuation (1 + n) (depth F M).

Theorem CPS_conversion_correct : forall F f f' k M,
  subst F f k =s k ->
  subst F f' k =s k ->
  stlc_expr F M ->
  subst F f' (CPS k F M (fun res => res) 1 (depth F M)) =s app k (subst F f M).
Proof.
  intros. rename H into Hkf. rename H0 into Hkf'. rename H1 into H. remember M as HM. induction M; rewrite HeqHM in *; simpl.
  - inversion H. rewrite (eqb_sym s F). rewrite H1. simpl. rewrite H1. apply S_App. apply Hkf'. apply S_Refl.
  - admit.
  - inversion H.
  - apply S_App. apply Hkf'. apply S_Refl.
  - Admitted.

(*
  The definition of [stlc_eqb] :

                    -----------------------------                       (S_Refl)
                               x1 =s x1

                               x1 =s x2
                    -----------------------------                       (S_Symm)
                               x2 =s x1

                               x1 =s x2
                               x2 =s x3
                    -----------------------------                       (S_Trans)
                               x1 =s x3

                              t1 =s t1'
                              t2 =s t2'
                    -------------------------------                     (S_App)
                        app t1 t2 =s app t1' t2'

                    --------------------------------                    (S_AppAbs)
                     app (abs x t) y =s subst x y t

                               t =s t'
                    --------------------------------                    (S_Abs)
                          abs x t =s abs x t'

                        In y (list_name t) = false
                    --------------------------------                    (S_AbsName)
                          abs x t =s abs x t'

                              t1 =s t1'
                              t2 =s t2'
                    ---------------------------------                   (S_Plus)
                      tplus t1 t2 =s tplus t1' t2'

                              t1 =s t1'
                              t2 =s t2'
                    ---------------------------------                   (S_Minus)
                      tminus t1 t2 =s tminus t1' t2'

                              t1 =s t1'
                              t2 =s t2'
                    ---------------------------------                   (S_Mult)
                      tmult t1 t2 =s tmult t1' t2'

                              t1 =s t1'
                              t2 =s t2'
                              t3 =s t3'
                    ---------------------------------                   (S_If0)
                      tif0 t1 t2 t3 =s t1' t2' t3'

            -----------------------------------------------------       (S_If0AppLeft)
            app k (tif0 t1 t2 t3) =s tif0 t1 (app k t2) (app k t3)

            -----------------------------------------------------       (S_If0AppRight)
            app (tif0 t1 t2 t3) k =s tif0 t1 (app t2 k) (app t3 k)

                              t1 =s t1'
                              t2 =s t2'
                    ---------------------------------                   (S_Cons)
                      tcons t1 t2 =s tcons t1' t2'

                              t1 =s t1'
                              t2 =s t2'
                              t3 =s t3'
                    ---------------------------------                   (S_LCase)
                      tlcase t1 t2 x1 x2 t3 =s tlcase t1' t2' x1 x2 t3'

            -----------------------------------------------------       (S_LCaseAppLeft)
      app k (tlcase t1 t2 x1 x2 t3) =s tlcase t1 (app k t2) x1 x2 (app k t3)

            -----------------------------------------------------       (S_LCaseAppRight)
      app (tlcase t1 t2 x1 x2 t3) k =s tlcase t1 (app t2 k) x1 x2 (app t3 k)

                              t1 =s t1'
                    ---------------------------------                   (S_Fix)
                         tfix t1 =s tfix t1'

                    ---------------------------------                   (S_FixAbs)
                 tfix (abs f t) =s subst f (tfix (abs f t)) t

  The meanings of symbols:
    F is the identifier of the recursive function.
    f is the syntax tree before the CPS conversion.
    f' is the syntax tree after the CPS conversion.
    M is the recursive stlc expression consist in f, that is to say M is the remain part of f after removing those outer [abs]s.
    k is the continuation.
    Here, we suppose that there is no duplication of variable name.

  A property of f and f':
    forall k, app k (app f ...) = app (app f' ...) k,
    where ... are the parameters of f.

  Properties of M:
    1. M is not of the form [abs _ _],
    2. M does not contain [tfix],
    3. Those variables bound in M do not contain F (resursive function name).

  Properties of k:
    k does not contain recursive call because we do not consider free variables.
    Consequently we can get two lemmas:
    1. subst F f k =s k
    2. subst F f' k =s k

  Our conversion function:
    CPS (k : tm) (func_name : string) (func_body : tm) (continuation : tm -> tm) (naming fuel : nat),
    where the initial values of [continuation], [naming] and [fuel] are respectively [fun res => res] 1 and [depth M].

  The theorem to be informally proved:
    subst F f' (CPS k F M (fun res => res) 1 (depth F M)) =s app k (subst F f M)

  Proof:

  By induction on M.

  1. When M = var x1.
     F is not equal to x1,
          subst F f (var x1) = var x1
          subst F f' (var x1) = var x1
     We know that,
          CPS k F (var x1) (fun res => res) 1 (depth F (var x1))
       =s CPS k F (var x1) (fun res => res) 1 1
       =s app k (var x1)
     Finally,
          subst F f' (CPS k F (var x1) (fun res => res) 1 (depth F (var x1)))
       =s subst F f' (app k (var x1))
       =s app (subst F f' k) (subst F f' (var x1))
       =s app k (var x1)
       =s app k (subst F f (var x1))

  2. When M = app t1 t2.
  
  3. When M = tconst n.
     We know that,
          CPS k F (tconst n) (fun res => res) 1 (depth F (tconst n))
       =s CPS k F (tconst n) (fun res => res) 1 1
       =s app k (tconst n)
     Finally,
          subst F f' (CPS k F (tconst n) (fun res => res) 1 (depth F (tconst n)))
       =s subst F f' (app k (tconst n))
       =s app (subst F f' k) (subst F f' (tconst n))
       =s app k (tconst n)
       =s app k (subst F f (tconst n))

  4. When M = tplus t1 t2.
     The induction hypothesis:
          subst F f' (CPS k F t1 (fun res => res) 1 (depth F t1)) =s app k (subst F f t1)
          subst F f' (CPS k F t2 (fun res => res) 1 (depth F t2)) =s app k (subst F f t2)
       ▲ If both t1 and t2 are not resursive,
       We know that,
            CPS k F (tplus t1 t2) (fun res => res) 1 (depth F (tplus t1 t2))
         =s CPS k F (tplus t1 t2) (fun res => res) 1 1
         =s app k (tplus t1 t2)
       Finally,
            subst F f' (CPS k F (tplus t1 t2) (fun res => res) 1 (depth F (tplus t1 t2)))
         =s subst F f' (app k (tplus t1 t2))
         =s app (subst F f' k) (tplus (subst F f' t1) (subst F f' t2))
         =s app k (tplus t1 t2)
         =s app k (tplus (subst F f t1) (subst F f t2))
         =s app k (subst F f (tplus t1 t2))
       ▲ If t1 is recursive and t2 not recursive,
       We know that,
            CPS k F (tplus t1 t2) (fun res => res) 1 (depth F (tplus t1 t2))
         =s CPS k F (tplus t1 t2) (fun res => res) 1 (1 + depth F t1)
         =s CPS k F t1 (fun res : tm => tplus res t2) 1 (depth F t1)
         =s (?)
       Finally,
            subst F f' (CPS k F (tplus t1 t2) (fun res => res) 1 (depth F (tplus t1 t2)))
         =s subst F f' (CPS k F t1 (fun res : tm => tplus res t2) 1 (depth F t1))
         =s 
         =s app k (tplus (subst F f t1) t2)
         =s app k (subst F f (tplus t1 t2))
         
         
         
         
*)

Compute 1.

Compute (CPS k F 
<{ F a (F b c) }>
 (fun res => res) 1 (depth F <{ F a (F b c) }>)).

Compute (CPS k F 
<{ F a (F b c) }>
 (fun res => tplus res n2) 1 (depth F <{ F a (F b c) }>)).

Compute (CPS k F 
<{ F a (F b c) + n2 }>
 (fun res => res) 1 (depth F <{ F a (F b c) + n2 }>)).

Compute (tplus (CPS k F <{ F a (F b c) }> (fun res => res) 1 (depth F <{ F a (F b c) }>)) n2).

Compute (CPS k F 
<{ F a (F b c) }>
 (fun res => res) 1 (depth F <{ F a (F b c) }>)).





