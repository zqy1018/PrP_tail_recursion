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

Inductive no_duplicate (s : string) : tm -> Prop :=
  | D_Var : forall x1,
       no_duplicate s (var x1)
  | D_Abs : forall x1 t1,
       s <> x1 ->
       no_duplicate s t1 ->
       no_duplicate s (abs x1 t1)
  | D_App : forall t1 t2,
       no_duplicate s t1 ->
       no_duplicate s t2 ->
       no_duplicate s (app t1 t2)
  | D_Const : forall n,
       no_duplicate s (tconst n)
  | D_Plus : forall t1 t2,
       no_duplicate s t1 ->
       no_duplicate s t2 ->
       no_duplicate s (tplus t1 t2)
  | D_Minus : forall t1 t2,
       no_duplicate s t1 ->
       no_duplicate s t2 ->
       no_duplicate s (tminus t1 t2)
  | D_Mult : forall t1 t2,
       no_duplicate s t1 ->
       no_duplicate s t2 ->
       no_duplicate s (tmult t1 t2)
  | D_If0 : forall t1 t2 t3,
       no_duplicate s t1 ->
       no_duplicate s t2 ->
       no_duplicate s t3 ->
       no_duplicate s (tif0 t1 t2 t3)
  | D_Nil :
       no_duplicate s tnil
  | D_Cons : forall t1 t2,
       no_duplicate s t1 ->
       no_duplicate s t2 ->
       no_duplicate s (tcons t1 t2)
  | D_LCase : forall t1 t2 x1 x2 t3,
       s <> x1 ->
       s <> x2 ->
       no_duplicate s t1 ->
       no_duplicate s t2 ->
       no_duplicate s t3 ->
       no_duplicate s (tlcase t1 t2 x1 x2 t3)
  | D_Let : forall x1 t1 t2,
       s <> x1 ->
       no_duplicate s t1 ->
       no_duplicate s t2 ->
       no_duplicate s (tlet x1 t1 t2)
  | D_Fix : forall t1,
       no_duplicate s t1 ->
       no_duplicate s (tfix t1).

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
  forall n m, exists k, n + k = Nat.max n m.
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
  - assert (Heq : forall n m, (S n =? S m) = (n =? m)). { intros n1 m1. simpl. reflexivity. }
    intros n H naming. destruct (depth_gt_1 F <{ M1 M2 }>). rewrite H0. simpl in H0. destruct ((find_func F M1 =? 1) && (find_func F M2 =? 0) && is_recu F M1)%bool eqn:HE.
    injection H0 as H0. rewrite <- H0. simpl. rewrite HE. apply S_Refl. simpl. destruct (find_func F M1), (find_func F M2); simpl. apply S_Refl. injection H0 as H0. destruct (is_app_F F M1). rewrite <- H0.
    apply IHM2. rewrite <- H0. apply IHM2. apply Bool.andb_false_iff in HE. destruct HE. apply Bool.andb_false_iff in H1. destruct H1.
    rewrite Heq in H1. rewrite H1. simpl. destruct (is_app_F F M1). destruct n0. discriminate H1. simpl. injection H0 as H0. rewrite <- H0. apply IHM1. injection H0 as H0. rewrite <- H0. apply IHM1. discriminate H1. rewrite H1.
    rewrite Bool.andb_comm. simpl. destruct (is_app_F F M1). destruct n0. simpl. apply S_Refl. simpl. injection H0 as H0. rewrite <- H0. apply IHM1. injection H0 as H0. rewrite <- H0. apply IHM1. rewrite (Bool.andb_comm (n0 =? 0)). simpl.
    destruct (is_app_F F M1). destruct n0. simpl. injection H0 as H0. apply eq_sym in H0. destruct (depth_helper2 (depth F M2) (S (depth F M1))). rewrite H0. rewrite <- H1. eapply S_Trans. apply S_Symm. apply IHM2.
    rewrite Plus.plus_assoc_reverse. apply IHM2. simpl. assert ((fun res1 : tm => CPS k F M2 (fun res2 : tm => H <{ res1 res2 }>) (naming + S n0) x) = (fun res1 : tm => CPS k F M2 (fun res2 : tm => H <{ res1 res2 }>) (naming + S n0) (x + n))). {
    apply stlc_functional_extensionality. intros. injection H0 as H0. rewrite <- H0. destruct (depth_helper2 (depth F M2) (S (depth F M1))). rewrite <- H1. eapply S_Trans. apply S_Symm. apply IHM2. rewrite Plus.plus_assoc_reverse. apply IHM2. }
    rewrite H1. injection H0 as H0. rewrite <- H0. destruct (depth_helper2 (S (depth F M1)) (depth F M2)). rewrite Nat.max_comm in H2. rewrite <- H2. eapply S_Trans. apply S_Symm. Search (S _ + _). rewrite Nat.add_succ_comm. apply IHM1. assert (S (depth F M1) + x0 + n = depth F M1 + S (x0 + n)). {
    rewrite Plus.plus_assoc_reverse. apply Nat.add_succ_comm. } rewrite H3. assert (depth F M1 + S x0 + n = depth F M1 + S (x0 + n)). { rewrite Plus.plus_assoc_reverse. simpl. reflexivity. } rewrite H4. apply IHM1.
    assert ((fun res1 : tm => CPS k F M2 (fun _ : tm => H <{ res1 M2 }>) (naming + S n0) x) = (fun res1 : tm => CPS k F M2 (fun _ : tm => H <{ res1 M2 }>) (naming + S n0) (x + n))). { apply stlc_functional_extensionality. intros. injection H0 as H0. rewrite <- H0. destruct (depth_helper2 (depth F M2) (S (depth F M1))).
    rewrite <- H1. eapply S_Trans. apply S_Symm. apply IHM2. rewrite Plus.plus_assoc_reverse. apply IHM2. } rewrite H1. injection H0 as H0. rewrite <- H0. destruct (depth_helper2 (S (depth F M1)) (depth F M2)). rewrite Nat.max_comm in H2. rewrite <- H2. eapply S_Trans. Search (S _ + _). rewrite Nat.add_succ_comm. apply S_Symm. apply IHM1.
    rewrite Plus.plus_assoc_reverse. rewrite (Nat.add_succ_comm (depth F M1)). rewrite Plus.plus_assoc_reverse. apply IHM1.
  - intros. simpl. apply S_Abs. apply IHM.
  - intros. simpl. destruct (find_func F (continuation n)). apply S_Refl. apply S_Refl.
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
Qed.

Theorem naming_arbitrarility :
  forall k F M continuation fuel n,
  CPS k F M continuation 1 fuel =s CPS k F M continuation (1 + n) fuel.
Proof.
  intros. generalize dependent n. generalize dependent continuation. generalize dependent fuel. induction M; intros.
  - destruct fuel. simpl. apply S_Refl. simpl. destruct (find_func F (continuation s)). apply S_Refl. apply S_Refl.
  - destruct fuel. simpl. apply S_Refl. simpl. admit.
  - destruct fuel. simpl. apply S_Refl. simpl. apply S_Abs. apply IHM.
  - destruct fuel. simpl. apply S_Refl. simpl. destruct (find_func F (continuation n)). apply S_Refl. apply S_Refl.
  - destruct fuel. simpl. apply S_Refl. simpl. destruct (find_func F M1), (find_func F M2). apply S_Refl. apply IHM2. apply IHM1.
    assert (HF : (fun res1 : tm => CPS k F M2 (fun res2 : tm => continuation <{ res1 + res2 }>) (S (S n0)) fuel) = (fun res1 : tm => CPS k F M2 (fun res2 : tm => continuation <{ res1 + res2 }>) (S (n + S n0)) fuel)). {
    apply stlc_functional_extensionality. intros. eapply S_Trans. apply S_Symm. apply IHM2. apply IHM2. } rewrite HF. apply IHM1.
  - destruct fuel. simpl. apply S_Refl. simpl. destruct (find_func F M1), (find_func F M2). apply S_Refl. apply IHM2. apply IHM1.
    assert (HF : (fun res1 : tm => CPS k F M2 (fun res2 : tm => continuation <{ res1 - res2 }>) (S (S n0)) fuel) = (fun res1 : tm => CPS k F M2 (fun res2 : tm => continuation <{ res1 - res2 }>) (S (n + S n0)) fuel)). {
    apply stlc_functional_extensionality. intros. eapply S_Trans. apply S_Symm. apply IHM2. apply IHM2. } rewrite HF. apply IHM1.
  - destruct fuel. simpl. apply S_Refl. simpl. destruct (find_func F M1), (find_func F M2). apply S_Refl. apply IHM2. apply IHM1.
    assert (HF : (fun res1 : tm => CPS k F M2 (fun res2 : tm => continuation <{ res1 * res2 }>) (S (S n0)) fuel) = (fun res1 : tm => CPS k F M2 (fun res2 : tm => continuation <{ res1 * res2 }>) (S (n + S n0)) fuel)). {
    apply stlc_functional_extensionality. intros. eapply S_Trans. apply S_Symm. apply IHM2. apply IHM2. } rewrite HF. apply IHM1.
  - destruct fuel. simpl. apply S_Refl. simpl. destruct (find_func F M1), (find_func F M2). apply S_If0. apply S_Refl. apply IHM2. apply IHM3. apply S_If0. apply S_Refl. apply IHM2. apply IHM3.
    apply IHM1. apply IHM1.
  - destruct fuel. simpl. apply S_Refl. simpl. destruct (find_func F (continuation <{ nil }>)). apply S_Refl. apply S_Refl.
  - destruct fuel. simpl. apply S_Refl. simpl. destruct (find_func F M1), (find_func F M2). apply S_Refl. apply IHM2. apply IHM1.
    assert (HF : (fun res1 : tm => CPS k F M2 (fun res2 : tm => continuation <{ res1 :: res2 }>) (S (S n0)) fuel) = (fun res1 : tm => CPS k F M2 (fun res2 : tm => continuation <{ res1 :: res2 }>) (S (n + S n0)) fuel)). {
    apply stlc_functional_extensionality. intros. eapply S_Trans. apply S_Symm. apply IHM2. apply IHM2. } rewrite HF. apply IHM1.
  - destruct fuel. simpl. apply S_Refl. simpl. destruct (find_func F M1), (find_func F M2). apply S_LCase. apply S_Refl. apply IHM2. apply IHM3. apply S_LCase. apply S_Refl. apply IHM2. apply IHM3.
    apply IHM1. apply IHM1.
  - destruct fuel. simpl. apply S_Refl. simpl. apply S_Let. apply IHM1. apply IHM2.
  - destruct fuel. simpl. apply S_Refl. simpl. apply S_Fix. apply IHM.
Admitted.

Lemma eqbP : forall n m, Bool.reflect (n = m) (n =? m)%string.
Proof.
  intros n m. apply Bool.iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Lemma in_distributive_by_app :
  forall (F : string) (l1 l2 : list string), List.In F (l1 ++ l2) <-> (List.In F l1 \/ List.In F l2).
Proof.
  intros. split.
  - intros H. induction l1; simpl in *.
    + right. apply H.
    + destruct H. left. left. apply H. destruct (IHl1 H). left. right. apply H0. right. apply H0.
  - intros [H1 | H2].
    + induction l1; simpl in *. exfalso. apply H1. destruct H1. left. apply H. right. apply (IHl1 H).
    + induction l2; simpl in *. exfalso. apply H2. apply List.in_or_app. right. simpl. apply H2.
Qed.

Theorem substution_invariance :
  forall F M f, (List.In F (list_name M) -> False) -> (subst F f M =s M).
Proof.
  intros. induction M; simpl in *.
  - rewrite eqb_sym. destruct (eqbP s F). exfalso. apply H.
    left. apply e. apply S_Refl.
  - rewrite in_distributive_by_app in H. apply Decidable.not_or_iff in H. destruct H as [H1 H2].
    apply S_App. apply IHM1. apply H1. apply IHM2. apply H2.
  - rewrite eqb_sym. destruct (eqbP s F). apply S_Refl. apply S_Abs. apply Decidable.not_or_iff in H.
    destruct H as [H1 H2]. apply (IHM H2).
  - apply S_Refl.
  - rewrite in_distributive_by_app in H. apply Decidable.not_or_iff in H. destruct H as [H1 H2].
    apply S_Plus. apply IHM1. apply H1. apply IHM2. apply H2.
  - rewrite in_distributive_by_app in H. apply Decidable.not_or_iff in H. destruct H as [H1 H2].
    apply S_Minus. apply IHM1. apply H1. apply IHM2. apply H2.
  - rewrite in_distributive_by_app in H. apply Decidable.not_or_iff in H. destruct H as [H1 H2].
    apply S_Mult. apply IHM1. apply H1. apply IHM2. apply H2.
  - rewrite in_distributive_by_app in H. rewrite in_distributive_by_app in H. apply Decidable.not_or_iff in H.
    destruct H as [H1 H23]. apply Decidable.not_or_iff in H23. destruct H23 as [H2 H3]. apply S_If0. apply (IHM1 H1).
    apply (IHM2 H2). apply (IHM3 H3).
  - apply S_Refl.
  - rewrite in_distributive_by_app in H. apply Decidable.not_or_iff in H. destruct H as [H1 H2].
    apply S_Cons. apply IHM1. apply H1. apply IHM2. apply H2.
  - rewrite in_distributive_by_app in H. rewrite in_distributive_by_app in H. apply Decidable.not_or_iff in H.
    destruct H as [H1 H23]. apply Decidable.not_or_iff in H23. destruct H23 as [H2 H3]. apply S_LCase. apply (IHM1 H1).
    apply (IHM2 H2). simpl in H3. rewrite eqb_sym. destruct (eqbP s F). apply S_Refl. rewrite eqb_sym. destruct (eqbP s0 F). apply S_Refl.
    apply IHM3. apply Decidable.not_or_iff in H3. destruct H3. apply Decidable.not_or_iff in H0. destruct H0. apply H3.
  - rewrite eqb_sym. rewrite in_distributive_by_app in H. apply Decidable.not_or_iff in H. destruct H as [H H12].
    apply Decidable.not_or_iff in H12. destruct H12 as [H1 H2]. destruct (eqbP s F). apply S_Let. apply (IHM1 H1). apply S_Refl.
    apply S_Let. apply (IHM1 H1). apply (IHM2 H2).
  - apply S_Fix. apply IHM. apply H.
Qed.

Lemma str_reflect : forall s1 s2, s1 <> s2 -> (eqb s1 s2)%string = false.
Proof.
  intros. destruct (eqbP s1 s2). apply H in e. destruct e. reflexivity.
Qed.

Theorem subst_distribution :
  forall F G f t1 t2, F <> G -> no_duplicate F t1 -> no_duplicate F t2 -> no_duplicate G t2 ->
  subst F f (subst G t1 t2) =s subst G (subst F f t1) (subst F f t2).
Proof.
  intros F G f t1 t2. induction t2; intros HNeq HF1 HF2 HG2.
  - simpl. destruct (eqbP F s), (eqbP G s). rewrite e in HNeq. rewrite e0 in HNeq. exfalso. apply HNeq. reflexivity.
    simpl. rewrite e. rewrite eqb_refl. admit. simpl. rewrite e. rewrite eqb_refl. apply S_Refl. simpl.
    rewrite (str_reflect F s n). rewrite (str_reflect G s n0). apply S_Refl. 
  - simpl. apply S_App. apply IHt2_1. apply HNeq. apply HF1. inversion HF2. apply H1. inversion HG2. apply H1.
    apply IHt2_2. apply HNeq. apply HF1. inversion HF2. apply H2. inversion HG2. apply H2.
  - simpl. inversion HF2. inversion HG2. rewrite (str_reflect F s H1). rewrite (str_reflect G s H5). simpl.
    rewrite (str_reflect F s H1). rewrite (str_reflect G s H5). apply S_Abs. apply IHt2. assumption. assumption.
    assumption. assumption.
  - simpl. apply S_Refl.
  - simpl. apply S_Plus. apply IHt2_1. apply HNeq. apply HF1. inversion HF2. apply H1. inversion HG2. apply H1.
    apply IHt2_2. apply HNeq. apply HF1. inversion HF2. apply H2. inversion HG2. apply H2.
  - simpl. apply S_Minus. apply IHt2_1. apply HNeq. apply HF1. inversion HF2. apply H1. inversion HG2. apply H1.
    apply IHt2_2. apply HNeq. apply HF1. inversion HF2. apply H2. inversion HG2. apply H2.
  - simpl. apply S_Mult. apply IHt2_1. apply HNeq. apply HF1. inversion HF2. apply H1. inversion HG2. apply H1.
    apply IHt2_2. apply HNeq. apply HF1. inversion HF2. apply H2. inversion HG2. apply H2.
  - simpl. apply S_If0. apply IHt2_1. apply HNeq. apply HF1. inversion HF2. apply H2. inversion HG2. apply H2.
    apply IHt2_2. apply HNeq. apply HF1. inversion HF2. apply H3. inversion HG2. apply H3. apply IHt2_3.
    apply HNeq. apply HF1. inversion HF2. apply H4. inversion HG2. apply H4.
  - simpl. apply S_Refl.
  - simpl. apply S_Cons. apply IHt2_1. apply HNeq. apply HF1. inversion HF2. apply H1. inversion HG2. apply H1.
    apply IHt2_2. apply HNeq. apply HF1. inversion HF2. apply H2. inversion HG2. apply H2.
  - simpl. inversion HF2. inversion HG2. rewrite (str_reflect F s H4). rewrite (str_reflect G s H14). rewrite (str_reflect F s0 H5). rewrite (str_reflect G s0 H15).
    apply S_LCase. apply IHt2_1. assumption. assumption. assumption. assumption. apply IHt2_2. assumption. assumption. assumption.
    assumption. apply IHt2_3. assumption. assumption. assumption. assumption.
  - simpl. inversion HF2. inversion HG2. rewrite (str_reflect F s H2). rewrite (str_reflect G s H8). apply S_Let. apply IHt2_1.
    assumption. assumption. assumption. assumption. apply IHt2_2. assumption. assumption. assumption. assumption.
  - simpl. apply S_Fix. apply IHt2. assumption. assumption. inversion HF2. assumption. inversion HG2. assumption.
Admitted.
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
                     abs x t =s abs y (subst x y t)

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
                              t2 =s t2'
                    ---------------------------------                   (S_Let)
                     tlet x t1 t2 =s tlet x t1' t2'

                    ---------------------------------                   (S_LetSubst)
                     tlet x t1 t2 =s subst x t1 t2

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
    ▲ If k contains recursive call (as a intermediate state of the process), the conversion function will not apply it with [k].

  Our conversion function:
    CPS (k : tm) (func_name : string) (func_body : tm) (continuation : tm -> tm) (naming fuel : nat),
    where the initial values of [continuation], [naming] and [fuel] are respectively [fun res => res] 1 and [depth M].

  The theorem to be informally proved:
    subst F f' (CPS k F M (fun res => res) 1 (depth F M)) =s app k (subst F f M)

  Proof:

  First, if we say a stlc term [t] is recursive, we mean that [find_func F t > 0].
  Here we note [find_func F t1 = S n1] and [find_func F t2 = S n2] if [t1] or [t2] is recursive.

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

  2. When M = app t1 t2. (TODO)

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
            forall k, subst F f' (CPS k F t1 (fun res => res) 1 (depth F t1)) =s app k (subst F f t1)
            forall k, subst F f' (CPS k F t2 (fun res => res) 1 (depth F t2)) =s app k (subst F f t2)
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
         =s CPS k F t1 (fun res => tplus res t2) 1 (depth F t1)
       According to the induction hypothesis,
            forall k, subst F f' (CPS k F t1 (fun res => res) 1 (depth F t1)) =s app k (subst F f t1)
       We have,
            subst F f' (CPS k F t1 (fun res => tplus res t2) 1 (depth F t1)) =s app k (tplus (subst F f t1) t2)
       Finally,
            subst F f' (CPS k F (tplus t1 t2) (fun res => res) 1 (depth F (tplus t1 t2)))
         =s subst F f' (CPS k F t1 (fun res => tplus res t2) 1 (depth F t1))
         =s app k (tplus (subst F f t1) t2)
         =s app k (subst F f (tplus t1 t2))

     ▲ If t2 is recursive and t1 not recursive,
       We know that,
            CPS k F (tplus t1 t2) (fun res => res) 1 (depth F (tplus t1 t2))
         =s CPS k F (tplus t1 t2) (fun res => res) 1 (1 + depth F t2)
         =s CPS k F t2 (fun res => tplus t1 res) 1 (depth F t2)
       According to the induction hypothesis,
            forall k, subst F f' (CPS k F t2 (fun res => res) 1 (depth F t2)) =s app k (subst F f t2)
       We have,
            subst F f' (CPS k F t2 (fun res => tplus t1 res) 1 (depth F t2)) =s app k (tplus t1 (subst F f t2))
       Finally,
            subst F f' (CPS k F (tplus t1 t2) (fun res => res) 1 (depth F (tplus t1 t2)))
         =s subst F f' CPS k F t2 (fun res => tplus t1 res) 1 (depth F t2)
         =s app k (tplus t1 (subst F f t2))
         =s app k (subst F f (tplus t1 t2))

     ▲ If both t1 and t2 are recursive,
       We know that,
            CPS k F (tplus t1 t2) (fun res => res) 1 (depth F (tplus t1 t2))
         =s CPS k F (tplus t1 t2) (fun res => res) 1 (1 + max (depth F t1) (depth F t2))
         =s CPS k F t1 (fun res1 => CPS k F t2 (fun res2 => tplus res1 res2)
            (1 + (S n1)) (max (depth F t1) (depth F t2))) 1 (max (depth F t1) (depth F t2))
       According to the induction hypothesis,
            forall k, subst F f' (CPS k F t1 (fun res => res) 1 (depth F t1)) =s app k (subst F f t1)
            forall k, subst F f' (CPS k F t2 (fun res => res) (1 + (S n1)) (depth F t2))
         =s subst F f' (CPS k F t2 (fun res => res) 1 (depth F t2)) =s app k (subst F f t2)
       We have,
            subst F f' (CPS k F t1 (fun res1 => CPS k F t2 (fun res2 => tplus res1 res2)
            (1 + (S n1)) (max (depth F t1) (depth F t2))) 1 (max (depth F t1) (depth F t2)))
         =s subst F f' (CPS k F t1 (fun res1 => CPS k F t2 (fun res2 => tplus res1 res2)
            (1 + (S n1)) (max (depth F t1) (depth F t2))) 1 (depth F t1))
         =s subst F f' (CPS k F t2 (fun res2 => tplus t1 res2) (1 + (S n1)) (max (depth F t1) (depth F t2)))
         =s subst F f' (CPS k F t2 (fun res2 => tplus t1 res2) (1 + (S n1)) (depth F t2))
         =s app k (tplus (subst F f t1) (subst F f t2))
      Finally,
            subst F f' (CPS k F (tplus t1 t2) (fun res => res) 1 (depth F (tplus t1 t2)))
         =s app k (tplus (subst F f t1) (subst F f t2))
         =s app k (subst F f (tplus t1 t2))

  Cases where M = tminus t1 t2, tmult t1 t2 and tcons t1 t2 are similar.

  5. When M = tif0 t1 t2 t3.
     The induction hypothesis:
          forall k, subst F f' (CPS k F t1 (fun res => res) 1 (depth F t1)) =s app k (subst F f t1)
          forall k, subst F f' (CPS k F t2 (fun res => res) 1 (depth F t2)) =s app k (subst F f t2)
          forall k, subst F f' (CPS k F t3 (fun res => res) 1 (depth F t3)) =s app k (subst F f t3)
     ▲ If t1 is not recursive,
       We know that,
            CPS k F (tif0 t1 t2 t3) (fun res => res) 1 (depth F (tif0 t1 t2 t3))
         =s CPS k F (tif0 t1 t2 t3) (fun res => res) 1 (1 + max (depth F t2) (depth F t3))
         =s tif0 t1 (CPS k F t2 (fun res => res) 1 (max (depth F t2) (depth F t3)))
            (CPS k F t3 (fun res => res) 1 (max (depth F t2) (depth F t3)))
         =s tif0 t1 (CPS k F t2 (fun res => res) 1 (depth F t2))
            (CPS k F t3 (fun res => res) 1 (depth F t3))
       Finally,
            subst F f' (CPS k F (tif0 t1 t2 t3) (fun res => res) 1 (depth F (tif0 t1 t2 t3)))
         =s subst F f' (tif0 t1 (CPS k F t2 (fun res => res) 1 (depth F t2))
            (CPS k F t3 (fun res => res) 1 (depth F t3)))
         =s tif0 (subst F f' t1) (subst F f' (CPS k F t2 (fun res => res) 1 (depth F t2)))
            (subst F f' (CPS k F t3 (fun res => res) 1 (depth F t3)))
         =s tif0 t1 (app k (subst F f t2)) (app k (subst F f t3))
         =s app k (tif0 t1 (subst F f t2) (subst F f t3))
         =s app k (tif0 (subst F f t1) (subst F f t2) (subst F f t3))
         =s app k (subst F f (tif0 t1 t2 t3))
       
     ▲ If t1 is recursive,
       We know that,
            CPS k F (tif0 t1 t2 t3) (fun res => res) 1 (depth F (tif0 t1 t2 t3))
         =s CPS k F (tif0 t1 t2 t3) (fun res => res) 1 (1 + max (depth F t1) (max (depth F t2) (depth F t3)))
         =s CPS k F t1 (fun res => tif0 res
            (CPS k F t2 (fun res => res) (1 + (S n1)) (max (depth F t1) (max (depth F t2) (depth F t3))))
            (CPS k F t3 (fun res => res) (1 + (S n1)) (max (depth F t1) (max (depth F t2) (depth F t3))))) 1 (max (depth F t1) (max (depth F t2) (depth F t3)))
       According to the induction hypothesis,
            forall k, subst F f' (CPS k F t1 (fun res => res) 1 (depth F t1)) =s app k (subst F f t1)
            forall k, subst F f' (CPS k F t2 (fun res => res) 1 (depth F t2)) =s app k (subst F f t2)
            forall k, subst F f' (CPS k F t3 (fun res => res) 1 (depth F t3)) =s app k (subst F f t3)
       We have,
            subst F f' (CPS k F t2 (fun res => res) (1 + (S n1)) (max (depth F t1) (max (depth F t2) (depth F t3))))
         =s subst F f' (CPS k F t2 (fun res => res) (1 + (S n1)) (depth F t2))
         =s subst F f' (CPS k F t2 (fun res => res) 1 (depth F t2))
         =s app k (subst F f t2)
            subst F f' (CPS k F t3 (fun res => res) (1 + (S n1)) (max (depth F t1) (max (depth F t2) (depth F t3))))
         =s subst F f' (CPS k F t3 (fun res => res) (1 + (S n1)) (depth F t3))
         =s subst F f' (CPS k F t3 (fun res => res) 1 (depth F t3))
         =s app k (subst F f t3)
            subst F f' (CPS k F t1 (fun res => tif0 res
            (CPS k F t2 (fun res => res) (1 + (S n1)) (max (depth F t1) (max (depth F t2) (depth F t3))))
            (CPS k F t3 (fun res => res) (1 + (S n1)) (max (depth F t1) (max (depth F t2) (depth F t3))))) 1 (max (depth F t1) (max (depth F t2) (depth F t3))))
         =s subst F f' (CPS k F t1 (fun res => tif0 res
            (CPS k F t2 (fun res => res) (1 + (S n1)) (max (depth F t1) (max (depth F t2) (depth F t3))))
            (CPS k F t3 (fun res => res) (1 + (S n1)) (max (depth F t1) (max (depth F t2) (depth F t3))))) 1 (depth F t1))
         =s tif0 (subst F f t1) (subst F f' (CPS k F t2 (fun res => res) (1 + (S n1)) (max (depth F t1) (max (depth F t2) (depth F t3)))))
            (subst F f' (CPS k F t3 (fun res => res) (1 + (S n1)) (max (depth F t1) (max (depth F t2) (depth F t3)))))
         =s tif0 (subst F f t1) (subst F f' (CPS k F t2 (fun res => res) (1 + (S n1)) (depth F t2)))
            (subst F f' (CPS k F t3 (fun res => res) (1 + (S n1)) (depth F t3)))
         =s tif0 (subst F f t1) (app k (subst F f t2)) (app k (subst F f t3))
        
       Finally,
            subst F f' (CPS k F (tif0 t1 t2 t3) (fun res => res) 1 (depth F (tif0 t1 t2 t3)))
         =s tif0 (subst F f t1) (app k (subst F f t2)) (app k (subst F f t3))
         =s app k (tif0 (subst F f t1) (subst F f t2) (subst F f t3))
         =s app k (subst F f (tif0 t1 t2 t3))

  The case where M = tlcase t1 t2 x1 x2 t3 is similar.

  6. When M = tnil.
     We know that,
          CPS k F tnil (fun res => res) 1 (depth F tnil)
       =s CPS k F nil (fun res => res) 1 1
       =s app k nil
     Finally,
          subst F f' (CPS k F tnil (fun res => res) 1 (depth F tnil))
       =s subst F f' (app k nil)
       =s app k nil
       =s app k (subst F f nil)
   
  7. When M = tlet x1 t1 t2.
     The induction hypothesis:
            forall k, subst F f' (CPS k F t1 (fun res => res) 1 (depth F t1)) =s app k (subst F f t1)
            forall k, subst F f' (CPS k F t2 (fun res => res) 1 (depth F t2)) =s app k (subst F f t2)
     ▲ If both t1 and t2 are not resursive,
       We know that,
            CPS k F (tlet x1 t1 t2) (fun res => res) 1 (depth F (tlet x1 t1 t2))
         =s CPS k F (tlet x1 t1 t2) (fun res => res) 1 1
         =s app k (tlet x1 t1 t2)
       Finally,
            subst F f' (CPS k F (tlet x1 t1 t2) (fun res => res) 1 (depth F (tlet x1 t1 t2)))
         =s subst F f' (app k (tlet x1 t1 t2))
         =s app (subst F f' k) (tlet x1 (subst F f' t1) (subst F f' t2))
         =s app k (tlet x1 t1 t2)
         =s app k (tlet x1 (subst F f t1) (subst F f t2))
         =s app k (subst F f (tlet x1 t1 t2))
     ▲ If t1 is recursive and t2 not recursive,
       We know that,
            CPS k F (tlet x1 t1 t2) (fun res => res) 1 (depth F (tlet x1 t1 t2))
         =s CPS k F (tlet x1 t1 t2) (fun res => res) 1 (1 + depth F t1)
         =s CPS (abs res res) F t1 (fun res : tm => tlet x1 res (app k t2)) 1 (depth F t1)
       According to the induction hypothesis,
            forall k, subst F f' (CPS k F t1 (fun res => res) 1 (depth F t1)) =s app k (subst F f t1)
       We have,
            subst F f' (CPS (abs res res) F t1 (fun res : tm => tlet x1 res (app k t2)) 1 (depth F t1))
         =s app k (tlet x1 (subst F f t1) (app k t2))
       Finally,
            subst F f' (CPS k F (tlet x1 t1 t2) (fun res => res) 1 (depth F (tlet x1 t1 t2)))
         =s app (abs res res) (tlet x1 (subst F f t1) (app k t2))
         =s tlet x1 (subst F f t1) (app k t2)
         =s subst x1 (subst F f t1) (app k t2)
         =s app (subst x1 (subst F f t1) k) (subst x1 (subst F f t1) t2)
         =s app k (subst x1 (subst F f t1) t2)
         =s app k (subst x1 (subst F f t1) (subst F f t2))
         =s app k (subst F f (subst x1 t1 t2))
         =s app k (subst F f (tlet x1 t1 t2))

     ▲ If t2 is recursive and t1 not recursive,
       We know that,
            CPS k F (tlet x1 t1 t2) (fun res => res) 1 (depth F (tlet x1 t1 t2))
         =s CPS k F (tlet x1 t1 t2) (fun res => res) 1 (1 + depth F t2)
         =s CPS k F t2 (fun res : tm => tlet x1 t1 res) 1 (depth F t2)
       According to the induction hypothesis,
            forall k, subst F f' (CPS k F t2 (fun res => res) 1 (depth F t2)) =s app k (subst F f t2)
       We have,
            subst F f' (CPS k F t2 (fun res : tm => tlet x1 t1 res) 1 (depth F t2))
         =s app k (tlet x1 t1 (subst F f t2))
       Finally,
            subst F f' (CPS k F (tlet x1 t1 t2) (fun res => res) 1 (depth F (tlet x1 t1 t2)))
         =s app k (tlet x1 t1 (subst F f t2))
         =s app k (tlet x1 (subst F f t1) (subst F f t2))
         =s app k (subst F f (tlet x1 t1 t2))

     ▲ If both t1 and t2 are recursive,
       We know that,
            CPS k F (tlet x1 t1 t2) (fun res => res) 1 (depth F (tlet x1 t1 t2))
         =s CPS k F (tlet x1 t1 t2) (fun res => res) 1 (1 + max (depth F t1) (depth F t2))
         =s CPS (abs res res) F t1 (fun res1 => CPS k F t2 (fun res2 => tlet x1 res1 res2)
            (1 + (S n1)) (max (depth F t1) (depth F t2))) 1 (max (depth F t1) (depth F t2))
       According to the induction hypothesis,
            forall k, subst F f' (CPS k F t1 (fun res => res) 1 (depth F t1)) =s app k (subst F f t1)
            forall k, subst F f' (CPS k F t2 (fun res => res) (1 + (S n1)) (depth F t2))
            =s subst F f' (CPS k F t2 (fun res => res) 1 (depth F t2)) =s app k (subst F f t2)
       We have,
            subst F f' (CPS (abs res res) F t1 (fun res1 => CPS k F t2 (fun res2 => tlet x1 res1 res2)
            (1 + (S n1)) (max (depth F t1) (depth F t2))) 1 (max (depth F t1) (depth F t2)))
         =s subst F f' (CPS (abs res res) F t1 (fun res1 => CPS k F t2 (fun res2 => tlet x1 res1 res2)
            (1 + (S n1)) (max (depth F t1) (depth F t2))) 1 (depth F t1))
         =s subst F f' (CPS k F t2 (fun res2 => tlet x1 t1 res2) (1 + (S n1)) (max (depth F t1) (depth F t2)))
         =s subst F f' (CPS k F t2 (fun res2 => tlet x1 t1 res2) (1 + (S n1)) (depth F t2))
         =s app k (tlet x1 (subst F f t1) (subst F f t2))
       Finally,
            CPS k F (tlet x1 t1 t2) (fun res => res) 1 (depth F (tlet x1 t1 t2))
         =s app k (tlet x1 (subst F f t1) (subst F f t2))
         =s app k (subst x1 (subst F f t1) (subst F f t2))
         =s app k (subst F f (subst x1 t1 t2))
         =s app k (subst F f (tlet x1 t1 t2))
*)
