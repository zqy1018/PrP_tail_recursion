From STLC Require Export Definitions.
From STLC Require Export Argument.
From Coq Require Import Logic.FunctionalExtensionality.
(*From Coq Require Import List.
Import ListNotations.*)

Print tm.
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

Lemma eqbP : forall n m, Bool.reflect (n = m) (n =? m)%string.
Proof.
  intros n m. apply Bool.iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Lemma in_distributive_for_app :
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
  - rewrite in_distributive_for_app in H. apply Decidable.not_or_iff in H. destruct H as [H1 H2].
    apply S_App. apply IHM1. apply H1. apply IHM2. apply H2.
  - rewrite eqb_sym. destruct (eqbP s F). apply S_Refl. apply S_Abs. apply Decidable.not_or_iff in H.
    destruct H as [H1 H2]. apply (IHM H2).
  - apply S_Refl.
  - rewrite in_distributive_for_app in H. apply Decidable.not_or_iff in H. destruct H as [H1 H2].
    apply S_Plus. apply IHM1. apply H1. apply IHM2. apply H2.
  - rewrite in_distributive_for_app in H. apply Decidable.not_or_iff in H. destruct H as [H1 H2].
    apply S_Minus. apply IHM1. apply H1. apply IHM2. apply H2.
  - rewrite in_distributive_for_app in H. apply Decidable.not_or_iff in H. destruct H as [H1 H2].
    apply S_Mult. apply IHM1. apply H1. apply IHM2. apply H2.
  - rewrite in_distributive_for_app in H. rewrite in_distributive_for_app in H. apply Decidable.not_or_iff in H.
    destruct H as [H1 H23]. apply Decidable.not_or_iff in H23. destruct H23 as [H2 H3]. apply S_If0. apply (IHM1 H1).
    apply (IHM2 H2). apply (IHM3 H3).
  - apply S_Refl.
  - rewrite in_distributive_for_app in H. apply Decidable.not_or_iff in H. destruct H as [H1 H2].
    apply S_Cons. apply IHM1. apply H1. apply IHM2. apply H2.
  - rewrite in_distributive_for_app in H. rewrite in_distributive_for_app in H. apply Decidable.not_or_iff in H.
    destruct H as [H1 H23]. apply Decidable.not_or_iff in H23. destruct H23 as [H2 H3]. apply S_LCase. apply (IHM1 H1).
    apply (IHM2 H2). simpl in H3. rewrite eqb_sym. destruct (eqbP s F). apply S_Refl. rewrite eqb_sym. destruct (eqbP s0 F). apply S_Refl.
    apply IHM3. apply Decidable.not_or_iff in H3. destruct H3. apply Decidable.not_or_iff in H0. destruct H0. apply H3.
  - rewrite eqb_sym. rewrite in_distributive_for_app in H. apply Decidable.not_or_iff in H. destruct H as [H H12].
    apply Decidable.not_or_iff in H12. destruct H12 as [H1 H2]. destruct (eqbP s F). apply S_Let. apply (IHM1 H1). apply S_Refl.
    apply S_Let. apply (IHM1 H1). apply (IHM2 H2).
  - apply S_Fix. apply IHM. apply H.
Qed.

Lemma str_reflect : forall s1 s2, s1 <> s2 -> (eqb s1 s2)%string = false.
Proof.
  intros. destruct (eqbP s1 s2). apply H in e. destruct e. reflexivity.
Qed.

Theorem CPS_correct : forall (k : tm) (F : string) (M f f' : tm),
  stlc_expr F M ->
  (List.In F (list_name k) -> False) ->
  subst F f' (CPS k F M (fun res => res) 1) =s app k (subst F f M).
Proof.
  intros k F M f f' HM HK.
  assert (HKf : subst F f k =s k). { apply substution_invariance. apply HK. }
  assert (HKf' : subst F f' k =s k). { apply substution_invariance. apply HK. }
  induction HM.
  - simpl. rewrite H. simpl. rewrite H. apply S_App. apply HKf'. apply S_Refl.
  - simpl. rewrite H. Admitted.


(*
  The definition of [stlc_eqb], whose notation is [ _ =s _ ] :

                    ----------------------------                        (S_Refl)
                              x1 =s x1

                              x1 =s x2
                    ----------------------------                        (S_Symm)
                              x2 =s x1

                              x1 =s x2
                              x2 =s x3
                    ----------------------------                        (S_Trans)
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
                    --------------------------------                    (S_Plus)
                      tplus t1 t2 =s tplus t1' t2'

                              t1 =s t1'
                              t2 =s t2'
                    --------------------------------                    (S_Minus)
                      tminus t1 t2 =s tminus t1' t2'

                              t1 =s t1'
                              t2 =s t2'
                    --------------------------------                    (S_Mult)
                      tmult t1 t2 =s tmult t1' t2'

                              t1 =s t1'
                              t2 =s t2'
                              t3 =s t3'
                    --------------------------------                    (S_If0)
                      tif0 t1 t2 t3 =s t1' t2' t3'

            -----------------------------------------------------       (S_If0AppLeft)
            app k (tif0 t1 t2 t3) =s tif0 t1 (app k t2) (app k t3)

            -----------------------------------------------------       (S_If0AppRight)
            app (tif0 t1 t2 t3) k =s tif0 t1 (app t2 k) (app t3 k)

                              t1 =s t1'
                              t2 =s t2'
                    --------------------------------                    (S_Cons)
                      tcons t1 t2 =s tcons t1' t2'

                              t1 =s t1'
                              t2 =s t2'
                              t3 =s t3'
              -------------------------------------------------         (S_LCase)
              tlcase t1 t2 x1 x2 t3 =s tlcase t1' t2' x1 x2 t3'

      ----------------------------------------------------------------- (S_LCaseAppLeft)
      app k (tlcase t1 t2 x1 x2 t3) =s tlcase t1 (app k t2) x1 x2 (app k t3)

      ----------------------------------------------------------------- (S_LCaseAppRight)
      app (tlcase t1 t2 x1 x2 t3) k =s tlcase t1 (app t2 k) x1 x2 (app t3 k)

                              t1 =s t1'
                              t2 =s t2'
                    -------------------------------                     (S_Let)
                     tlet x t1 t2 =s tlet x t1' t2'

                    -------------------------------                     (S_LetSubst)
                     tlet x t1 t2 =s subst x t1 t2

                              t1 =s t1'
                    -----------------------------                       (S_Fix)
                         tfix t1 =s tfix t1'

                 --------------------------------------------           (S_FixAbs)
                 tfix (abs f t) =s subst f (tfix (abs f t)) t

  The meanings of symbols:
    F is the identifier of the recursive function.
    f is the syntax tree before the CPS conversion.
    f' is the syntax tree after the CPS conversion.
    M is the recursive stlc expression consist in f, that is to say M is the remain part of f after removing those outer [abs]s.
    tm_no_F is any stlc term which does not contain recursive call, that is used in order to formally describe a proposition of a function typed [tm -> tm].
    [find_func F (continuation tm_no_F) = 0] means there is no recursive call in the function body, which is typed [tm].
    Here, we suppose that there is no duplication of variable name.

  A property of f and f':
    forall k, app k (app f ...) = app (app f' ...) k,
    where ... are the arguments of f.

  Properties of M:
    1. M is not of the form [abs _ _].
    2. M does not contain [tfix].
    3. Those variables bound in M do not contain F (the resursive function).
    Formally, M satisfies the property [stlc_expr F M], which is defined above.

  Properties of k:
    k does not contain recursive call because we do not consider free variables.
    Consequently we can get two lemmas [subst F f k =s k] and [subst F f' k =s k].

  Our conversion function:
    [CPS (k : tm) (func_name : string) (func_body : tm) (continuation : tm -> tm) (naming : nat)].
  When we need to convert a function, initially we let [k] be plein [var k], [continuation] be [fun res : tm => res] and [naming] be [1].

  A property of the argument naming in function CPS:
    Since naming will be used only to give names in the [abs _ _]s, according to the rule [S_AbsName: (List.In y (list_name t) -> False) -> abs x t =s abs y (subst x y t)], if we do not
    employ the strings which may become an output of the function nat2string, we need not worry about the specific value of naming.
    Formally, that is to say:
        forall n, (In (nat2string n) (list_name M) -> False) -> (CPS k F M continuation naming =s CPS k F M continuation (S naming)).

  Firstly we prove another theorem which is a branch of the main theorem: When [is_app_F F M = true], 
    subst F f' (CPS_app_F k F M continuation continuation2 naming (find_func F M)) =s (subst F f continuation2) (app k (subst F f (continuation M))) (when [find_func F (continuation tm_no_F) = 0] and [find_func F (continuation2 tm_no_F) = 0])
                                                                                   =s (subst F f continuation2) (app k ((subst F f' continuation) (subst F f M))) (when [find_func F (continuation tm_no_F) = S _] and [find_func F (continuation2 tm_no_F) = 0])
                                                                                   =s (subst F f' continuation2) (app k (subst F f (continuation M))) (when [find_func F (continuation tm_no_F) = 0] and [find_func F (continuation2 tm_no_F) = S _])
                                                                                   =s (subst F f' continuation2) (app k ((subst F f' continuation) (subst F f M))) (when [find_func F (continuation tm_no_F) = S _] and [find_func F (continuation2 tm_no_F) = S _])

    Actually there we have misused the function [subst] in [subst F f continuation] due to the type of [continuation] is [tm -> tm] instead of [tm], what we mean is to substitute those recursive calls in the
    body of the fonction [continuation] by [f], which can be expressed formally: [subst tm_no_F (subst F f M) (subst F f' (continuation tm_no F))].

  By induction on [find_func F M - 1].
  1. find_func F M - 1 = 0.
        CPS_app_F k F M continuation continuation2 naming (find_func F M)
     =s CPS_app_F k F M continuation continuation2 naming 1
     =s continuation2 (app M (abs continuation_name (app k (continuation continuation_name))))
     where [continuation_name = append "res" (nat2string naming)].
     We know that [is_app_F F M = true] and [find_func F M = 1], that is to say M ressemble [F M1 M2 ... Mn] where no recursive call is in the parameters,
     consequently [subst F f M = f M1 M2 ... Mn] and [subst F f' M = f' M1 M2 ... Mn].

     When [find_func F (continuation tm_no_F) = 0],
     Consequently we know that [subst F f (continuation tm_no_F) = continuation tm_no_F] and [subst F f' (continuation tm_no_F) = continuation tm_no_F].

       When [find_func F (continuation2 tm_no_F) = 0],
       Consequently we know that [subst F f (continuation2 tm_no_F) = continuation2 tm_no_F] and [subst F f' (continuation2 tm_no_F) = continuation2 tm_no_F].

          subst F f' (CPS_app_F k F M continuation continuation2 naming (find_func F M))
       =s subst F f' (continuation2 (app M (abs continuation_name (app k (continuation continuation_name)))))
       We know that [F <> continuation_name].
       =s (subst F f' continuation2) (app (subst F f' M) (abs continuation_name (app (subst F f' k) ((subst F f' continuation) (subst F f' continuation_name)))))
       =s continuation2 (app (subst F f' M) (abs continuation_name (app k (continuation continuation_name))))
       =s continuation2 (app (abs continuation_name (app k (continuation continuation_name))) (subst F f M))
       =s continuation2 (app k (continuation (subst F f M)))
       =s (subst F f continuation2) (app k ((subst F f continuation) (subst F f M)))
       =s (subst F f continuation2) (app k (subst F f (continuation M)))

       When [find_func F (continuation2 tm_no_F) = S _],
          subst F f' (CPS_app_F k F M continuation continuation2 naming (find_func F M))
       =s subst F f' (continuation2 (app M (abs continuation_name (app k (continuation continuation_name)))))
       We know that [F <> continuation_name].
       =s (subst F f' continuation2) (app (subst F f' M) (abs continuation_name (app (subst F f' k) ((subst F f' continuation) (subst F f' continuation_name)))))
       =s (subst F f' continuation2) (app (subst F f' M) (abs continuation_name (app k (continuation continuation_name))))
       =s (subst F f' continuation2) (app (abs continuation_name (app k (continuation continuation_name))) (subst F f M))
       =s (subst F f' continuation2) (app k (continuation (subst F f M)))
       =s (subst F f' continuation2) (app k ((subst F f continuation) (subst F f M)))
       =s (subst F f' continuation2) (app k (subst F f (continuation M)))

     When [find_func F (continuation tm_no_F) = S _],
       When [find_func F (continuation2 tm_no_F) = 0],
       Consequently we know that [subst F f (continuation2 tm_no_F) = continuation2 tm_no_F] and [subst F f' (continuation2 tm_no_F) = continuation2 tm_no_F].

          subst F f' (CPS_app_F k F M continuation continuation2 naming (find_func F M))
       =s subst F f' (continuation2 (app M (abs continuation_name (app k (continuation continuation_name)))))
       We know that [F <> continuation_name].
       =s (subst F f' continuation2) (app (subst F f' M) (abs continuation_name (app (subst F f' k) ((subst F f' continuation) (subst F f' continuation_name)))))
       =s continuation2 (app (subst F f' M) (abs continuation_name (app (subst F f' k) ((subst F f' continuation) (subst F f' continuation_name)))))
       =s continuation2 (app (subst F f' M) (abs continuation_name (app k ((subst F f' continuation) continuation_name))))
       =s continuation2 (app (abs continuation_name (app k ((subst F f' continuation) continuation_name))) (subst F f M))
       =s continuation2 (app k ((subst F f' continuation) (subst F f M)))
       =s (subst F f continuation2) (app k ((subst F f' continuation) (subst F f M)))

       When [find_func F (continuation2 tm_no_F) = S _],
          subst F f' (CPS_app_F k F M continuation continuation2 naming (find_func F M))
       =s subst F f' (continuation2 (app M (abs continuation_name (app k (continuation continuation_name)))))
       We know that [F <> continuation_name].
       =s (subst F f' continuation2) (app (subst F f' M) (abs continuation_name (app (subst F f' k) ((subst F f' continuation) (subst F f' continuation_name)))))
       =s (subst F f' continuation2) (app (subst F f' M) (abs continuation_name (app k ((subst F f' continuation) continuation_name))))
       =s (subst F f' continuation2) (app (abs continuation_name (app k ((subst F f' continuation) continuation_name))) (subst F f M))
       =s (subst F f' continuation2) (app k ((subst F f' continuation) (subst F f M)))

  2. find_func F M - 1 = S n.
     By the induction hypothesis, for all M which satisfy [find_func F M = n], we have
     subst F f' (CPS_app_F k F M continuation continuation2 naming (find_func F M)) =s (subst F f continuation2) (app k (subst F f (continuation M))) (when [find_func F (continuation tm_no_F) = 0] and [find_func F (continuation2 tm_no_F) = 0])
                                                                                    =s (subst F f continuation2) (app k ((subst F f' continuation) (subst F f M))) (when [find_func F (continuation tm_no_F) = S _] and [find_func F (continuation2 tm_no_F) = 0])
                                                                                    =s (subst F f' continuation2) (app k (subst F f (continuation M))) (when [find_func F (continuation tm_no_F) = 0] and [find_func F (continuation2 tm_no_F) = S _])
                                                                                    =s (subst F f' continuation2) (app k ((subst F f' continuation) (subst F f M))) (when [find_func F (continuation tm_no_F) = S _] and [find_func F (continuation2 tm_no_F) = S _])

        CPS_app_F k F M continuation continuation2 naming (find_func F M)
     =s CPS_app_F k F M continuation continuation2 naming (S n)
     =s CPS_app_F k F new_body continuation (fun res => continuation2 (app arg (abs continuation_name res))) (naming + 1) n
     where [continuation_name = append "res" (nat2string naming)] and [(arg, new_body) = extract_and_subst_arg F M naming].

        subst F f' (CPS_app_F k F M continuation continuation2 naming (find_func F M))
     =s subst F f' (CPS_app_F k F new_body continuation (fun res => continuation2 (app arg (abs continuation_name res))) (naming + 1) n)

     We know that [find_func F M = find_func F new_body + 1], consequently [find_func F new_body = n].
     We also know that [is_recu F arg = true], that is to say arg ressemble [F M1 M2 ... Mn] where no recursive call is in the parameters,
     consequently [subst F f arg = f M1 M2 ... Mn] and [subst F f' arg = f' M1 M2 ... Mn].

     When [find_func F (continuation tm_no_F) = 0],
     Consequently we know that [subst F f (continuation tm_no_F) = continuation tm_no_F] and [subst F f' (continuation tm_no_F) = continuation tm_no_F].

       When [find_func F (continuation2 tm_no_F) = 0],
       Consequently we know that [subst F f (continuation2 tm_no_F) = continuation2 tm_no_F] and [subst F f' (continuation2 tm_no_F) = continuation2 tm_no_F].

          subst F f' (CPS_app_F k F M continuation continuation2 naming (find_func F M))
       =s subst F f' (CPS_app_F k F new_body continuation (fun res => continuation2 (app arg (abs continuation_name res))) (naming + 1) n)
       =s (subst F f' (fun res => continuation2 (app arg (abs continuation_name res)))) (app k (subst F f (continuation new_body))) [induction hypothesis]
       We know that [F <> continuation_name] and that [F <> res].
       =s (fun res => (subst F f' continuation2) (app (subst F f' arg) (abs (subst F f' continuation_name) (subst F f' res)))) (app k (subst F f (continuation new_body)))
       =s (fun res => continuation2 (app (subst F f' arg) (abs continuation_name res))) (app k (subst F f (continuation new_body)))
       =s continuation2 (app (subst F f' arg) (abs continuation_name (app k (subst F f (continuation new_body)))))
       =s continuation2 (app (abs continuation_name (app k (subst F f (continuation new_body)))) (subst F f arg))
       We know that [subst continuation_name arg new_body = M]
       =s continuation2 (app k (subst F f (continuation M)))
       =s (subst F f continuation2) (app k (subst F f (continuation M)))

       When [find_func F (continuation2 tm_no_F) = S _],
          subst F f' (CPS_app_F k F M continuation continuation2 naming (find_func F M))
       =s subst F f' (CPS_app_F k F new_body continuation (fun res => continuation2 (app arg (abs continuation_name res))) (naming + 1) n)
       =s (subst F f' (fun res => continuation2 (app arg (abs continuation_name res)))) (app k (subst F f (continuation new_body))) [induction hypothesis]
       We know that [F <> continuation_name] and that [F <> res].
       =s (fun res => (subst F f' continuation2) (app (subst F f' arg) (abs (subst F f' continuation_name) (subst F f' res)))) (app k (subst F f (continuation new_body)))
       =s (fun res => (subst F f' continuation2) (app (subst F f' arg) (abs continuation_name res))) (app k (subst F f (continuation new_body)))
       =s (subst F f' continuation2) (app (subst F f' arg) (abs continuation_name (app k (subst F f (continuation new_body)))))
       =s (subst F f' continuation2) (app (abs continuation_name (app k (subst F f (continuation new_body)))) (subst F f arg))
       We know that [subst continuation_name arg new_body = M]
       =s (subst F f' continuation2) (app k (subst F f (continuation M)))

     When [find_func F (continuation tm_no_F) = S _],
       When [find_func F (continuation2 tm_no_F) = 0],
       Consequently we know that [subst F f (continuation2 tm_no_F) = continuation2 tm_no_F] and [subst F f' (continuation2 tm_no_F) = continuation2 tm_no_F].

          subst F f' (CPS_app_F k F M continuation continuation2 naming (find_func F M))
       =s subst F f' (CPS_app_F k F new_body continuation (fun res => continuation2 (app arg (abs continuation_name res))) (naming + 1) n)
       =s (subst F f' (fun res => continuation2 (app arg (abs continuation_name res)))) (app k (subst F f' continuation) (subst F f new_body)) [induction hypothesis]
       We know that [F <> continuation_name] and that [F <> res].
       =s (fun res => (subst F f' continuation2) (app (subst F f' arg) (abs (subst F f' continuation_name) (subst F f' res)))) (app k (subst F f' continuation) (subst F f new_body))
       =s (fun res => continuation2 (app (subst F f' arg) (abs continuation_name res))) (app k (subst F f' continuation) (subst F f new_body))
       =s continuation2 (app (subst F f' arg) (abs continuation_name (app k (subst F f' continuation) (subst F f new_body))))
       =s continuation2 (app (abs continuation_name (app k (subst F f' continuation) (subst F f new_body))) (subst F f arg))
       We know that [subst continuation_name arg new_body = M]
       =s continuation2 (app k ((subst F f' continuation) (subst F f M)))
       =s (subst F f continuation2) (app k ((subst F f' continuation) (subst F f M)))

       When [find_func F (continuation2 tm_no_F) = S _],
          subst F f' (CPS_app_F k F M continuation continuation2 naming (find_func F M))
       =s subst F f' (CPS_app_F k F new_body continuation (fun res => continuation2 (app arg (abs continuation_name res))) (naming + 1) n)
       =s (subst F f' (fun res => continuation2 (app arg (abs continuation_name res)))) (app k (subst F f' continuation) (subst F f new_body)) [induction hypothesis]
       We know that [F <> continuation_name] and that [F <> res].
       =s (fun res => (subst F f' continuation2) (app (subst F f' arg) (abs (subst F f' continuation_name) (subst F f' res)))) (app k (subst F f' continuation) (subst F f new_body))
       =s (fun res => (subst F f' continuation2) (app (subst F f' arg) (abs continuation_name res))) (app k (subst F f' continuation) (subst F f new_body))
       =s (subst F f' continuation2) (app (subst F f' arg) (abs continuation_name (app k (subst F f' continuation) (subst F f new_body))))
       =s (subst F f' continuation2) (app (abs continuation_name (app k (subst F f' continuation) (subst F f new_body)))) (subst F f arg))
       We know that [subst continuation_name arg new_body = M]
       =s (subst F f' continuation2) (app k ((subst F f' continuation) (subst F f M)))

  The theorem is proved.

  The main theorem to be proved:
    subst F f' (CPS k F M continuation naming) =s app k (subst F f (continuation M)) (when [find_func F (continuation tm_no_F) = 0])
                                                  app k ((subst F f' continuation) (subst F f M)) (when [find_func F (continuation tm_no_F) = S _])
    obviously, [find_func F tm_no_F = 0].

  Proof:

  We prove: for a particular M, F, f and f', for all k, continuation and naming, the conclusion holds.
  By induction on M.

  1. M = var x1.
     We know that [eqb F x1 = false], so we have [subst F f M = M] and [subst F f' M = M].
        CPS k F M continuation naming
     =s CPS k F (var x1) continuation naming

     When [find_func F (continuation tm_no_F) = 0],
     Consequently we know that [subst F f (continuation tm_no_F) = continuation tm_no_F] and [subst F f' (continuation tm_no_F) = continuation tm_no_F].
        CPS k F M continuation naming
     =s app k (continuation (var x1))

        subst F f' (CPS k F M continuation naming)
     =s subst F f' (app k (continuation (var x1)))
     =s app (subst F f' k) (subst F f' (continuation (var x1)))
     =s app k (continuation (var x1))
     =s app (subst F f k) (subst F f (continuation (var x1)))
     =s subst F f (app k (continuation M))

     When [find_func F (continuation tm_no_F) = S _],
        CPS k F M continuation naming
     =s app k (continuation (var x1))

        subst F f' (CPS k F M continuation naming)
     =s subst F f' (app k (continuation (var x1)))
     =s app (subst F f' k) (subst F f' (continuation (var x1)))
     =s app k ((subst F f' continuation) (subst F f' (var x1)))
     =s app k ((subst F f' continuation) M)
     =s app k ((subst F f' continuation) (subst F f M))

     those cases where [M = tconst n] and [M = tnil] are similar.

  2. M = app t1 t2. (This case almost cover the case M = app (abs x1 t1) t2 and M = app (var F) t1, so we need not repeat)
     There we prove only the first case
     By the induction hypothesis, we have
     [subst F f' (CPS k F t1 continuation naming) =s app k (subst F f (continuation t1))] (when [find_func F (continuation tm_no_F) = 0])
                                                     app k ((subst F f' continuation) (subst F f t1))] (when [find_func F (continuation tm_no_F) = S n]) and
     [subst F f' (CPS k F t2 continuation naming) =s app k (subst F f (continuation t2))] (when [find_func F (continuation tm_no_F) = 0])
                                                     app k ((subst F f' continuation) (subst F f t2))] (when [find_func F (continuation tm_no_F) = S n]).

     When [is_app_F F M = false].
       When [find_func F (continuation tm_no_F) = 0],
        ①. When both t1 and t2 are not recursive, that is to say [find_func F t1 = 0] and [find_finc F t2 = 0],
           consequently [subst F f t1 = t1], [subst F f t2 = t2], [subst F f' t1 = t1] and [subst F f' t2 = t2].
              CPS k F M continuation naming
           =s app k (continuation (app t1 t2))

              subst F f' (CPS k F M continuation naming)
           =s subst F f' (app k (continuation (app t1 t2)))
           =s app (subst F f' k) (subst F f' (continuation (app t1 t2)))
           =s app k (continuation (app t1 t2))
           =s app (subst F f k) (subst F f (continuation M))
           =s app k (subst F f (continuation M))

        ②. When t1 is recursive and t2 not, that is to say [find_func F t1 = S n1] and [find_finc F t2 = 0],
           consequently [subst F f t2 = t2] and [subst F f' t2 = t2].
              CPS k F M continuation naming
           =s CPS k F t1 (fun res => continuation (app res t2)) naming

              subst F f' (CPS k F M continuation naming)
           =s subst F f' (CPS k F t1 (fun res => continuation (app res t2)) naming)
           =s app k (subst F f ((fun res => continuation (app res t2)) t1)) [induction hypothesis]
           =s app k (subst F f (continuation (app t1 t2)))
           =s app k (subst F f (continuation M))

        ③. When t2 is recursive and t1 not, that is to say [find_func F t1 = 0] and [find_finc F t2 = S n2],
           consequently [subst F f t1 = t1] and [subst F f' t1 = t1].
              CPS k F M continuation naming
           =s CPS k F t2 (fun res => continuation (app t1 res)) naming

              subst F f' (CPS k F M continuation naming)
           =s subst F f' (CPS k F t2 (fun res => continuation (app t1 res)) naming)
           =s app k (subst F f ((fun res => continuation (app t1 res)) t2)) [induction hypothesis]
           =s app k (subst F f (continuation (app t1 t2)))
           =s app k (subst F f (continuation M))

        ④. When both t1 and t2 are recursive, that is to say [find_func F t1 = S n1] and [find_finc F t2 = S n2].
              CPS k F M continuation naming
           =s CPS (abs res res) F t1 (fun res1 => CPS k F t2 (fun res2 => continuation (app res1 res2)) (naming + (S n1))) naming

              subst F f' (CPS k F M continuation naming)
           =s subst F f' (CPS (abs res res) F t1 (fun res1 => CPS k F t2 (fun res2 => continuation (app res1 res2)) (naming + (S n1))) naming)
           =s app (abs res res) ((subst F f' (fun res1 => CPS k F t2 (fun res2 => continuation (app res1 res2)) (naming + (S n1)))) (subst F f t1)) [induction hypothesis]
           =s (subst F f' (fun res1 => CPS k F t2 (fun res2 => continuation (app res1 res2)) (naming + (S n1)))) (subst F f t1)
           =s (fun res1 => subst F f' (CPS k F t2 (fun res2 => continuation (app res1 res2)) (naming + (S n1)))) (subst F f t1)
           =s (fun res1 => app k (subst F f ((fun res2 => continuation (app res1 res2)) t2))) (subst F f t1) [induction hypothesis]
           =s (fun res1 => app k (subst F f (continuation (app res1 t2)))) (subst F f t1)
           =s (fun res1 => app k ((subst F f continuation) (subst F f (app res1 t2)))) (subst F f t1)
           =s (fun res1 => app k (continuation (app res1 (subst F f t2)))) (subst F f t1)
           =s app k (continuation (app (subst F f t1) (subst F f t2)))
           =s app k ((subst F f continuation) (subst F f (app t1 t2)))
           =s app k (subst F f (continuation (app t1 t2)))
           =s app k (subst F f (continuation M))

       When [find_func F (continuation tm_no_F) = S _],
        ①. When both t1 and t2 are not recursive, that is to say [find_func F t1 = 0] and [find_finc F t2 = 0],
           consequently [subst F f t1 = t1], [subst F f t2 = t2], [subst F f' t1 = t1] and [subst F f' t2 = t2].
              CPS k F M continuation naming
           =s app k (continuation (app t1 t2))

              subst F f' (CPS k F M continuation naming)
           =s subst F f' (app k (continuation (app t1 t2)))
           =s app (subst F f' k) ((subst F f' continuation) (subst F f' (app t1 t2)))
           =s app k ((subst F f' continuation) (subst F f (app t1 t2)))
           =s app k ((subst F f' continuation) (subst F f M))

        ②. When t1 is recursive and t2 not, that is to say [find_func F t1 = S n1] and [find_finc F t2 = 0],
           consequently [subst F f t2 = t2] and [subst F f' t2 = t2].
              CPS k F M continuation naming
           =s CPS k F t1 (fun res => continuation (app res t2)) naming

              subst F f' (CPS k F M continuation naming)
           =s subst F f' (CPS k F t1 (fun res => continuation (app res t2)) naming)
           =s app k ((subst F f' (fun res => continuation (app res t2))) (subst F f t1)) [induction hypothesis]
           =s app k ((fun res => (subst F f' continuation) (subst F f' (app res t2))) (subst F f t1))
           =s app k ((subst F f' continuation) (app (subst F f t1) t2))
           =s app k ((subst F f' continuation) (app (subst F f t1) (subst F f t2)))
           =s app k ((subst F f' continuation) (subst F f (app t1 t2)))
           =s app k ((subst F f' continuation) (subst F f M))

        ③. When t2 is recursive and t1 not, that is to say [find_func F t1 = 0] and [find_finc F t2 = S n2],
           consequently [subst F f t1 = t1] and [subst F f' t1 = t1].
              CPS k F M continuation naming
           =s CPS k F t2 (fun res => continuation (app t1 res)) naming

              subst F f' (CPS k F M continuation naming)
           =s subst F f' (CPS k F t2 (fun res => continuation (app t1 res)) naming)
           =s app k ((subst F f' (fun res => continuation (app t1 res))) (subst F f t2)) [induction hypothesis]
           =s app k ((fun res => (subst F f' continuation) (subst F f' (app t1 res))) (subst F f t2))
           =s app k ((subst F f' continuation) (app t1 (subst F f t2)))
           =s app k ((subst F f' continuation) (app (subst F f t1) (subst F f t2)))
           =s app k ((subst F f' continuation) (subst F f (app t1 t2)))
           =s app k ((subst F f' continuation) (subst F f M))

        ④. When both t1 and t2 are recursive, that is to say [find_func F t1 = S n1] and [find_finc F t2 = S n2].
              CPS k F M continuation naming
           =s CPS (abs res res) F t1 (fun res1 => CPS k F t2 (fun res2 => continuation (app res1 res2)) (naming + (S n1))) naming

              subst F f' (CPS k F M continuation naming)
           =s subst F f' (CPS (abs res res) F t1 (fun res1 => CPS k F t2 (fun res2 => continuation (app res1 res2)) (naming + (S n1))) naming)
           =s app (abs res res) ((subst F f' (fun res1 => CPS k F t2 (fun res2 => continuation (app res1 res2)) (naming + (S n1)))) (subst F f t1)) [induction hypothesis]
           =s (subst F f' (fun res1 => CPS k F t2 (fun res2 => continuation (app res1 res2)) (naming + (S n1)))) (subst F f t1)
           =s (fun res1 => subst F f' (CPS k F t2 (fun res2 => continuation (app res1 res2)) (naming + (S n1)))) (subst F f t1)
           =s (fun res1 => app k ((subst F f' (fun res2 => continuation (app res1 res2))) (subst F f t2))) (subst F f t1) [induction hypothesis]
           =s (fun res1 => app k (((fun res2 => (subst F f' continuation) (subst F f' (app res1 res2)))) (subst F f t2))) (subst F f t1)
           =s (fun res1 => app k (((fun res2 => (subst F f' continuation) (app res1 res2))) (subst F f t2))) (subst F f t1)
           =s (fun res1 => app k ((subst F f' continuation) (app res1 (subst F f t2)))) (subst F f t1)
           =s app k ((subst F f' continuation) (app (subst F f t1) (subst F f t2)))
           =s app k ((subst F f' continuation) (subst F f (app t1 t2)))
           =s app k ((subst F f' continuation) (subst F f M))

     those cases where [M = tplus t1 t2], [M = tminus t1 t2], [M = tmult t1 t2] and [M = tcons t1 t2] are similar.

     When [is_app_F F M = true], which is exactly the theorem proved before.

       When [find_func F (continuation tm_no_F) = 0],
          subst F f' (CPS k F M continuation naming)
       =s subst F f' (CPS_app_F k F M continuation (fun res => res) naming (find_func F M))
       =s (subst F f (fun res => res)) (app k (subst F f (continuation M)))
       =s (fun res => res) (app k (subst F f (continuation M)))
       =s app k (subst F f (continuation M))

       When [find_func F (continuation tm_no_F) = S _],
          subst F f' (CPS k F M continuation naming)
       =s subst F f' (CPS_app_F k F M continuation (fun res => res) naming (find_func F M))
       =s (subst F f (fun res => res)) (app k ((subst F f' continuation) (subst F f M)))
       =s (fun res => res) (app k ((subst F f' continuation) (subst F f M)))
       =s app k ((subst F f' continuation) (subst F f M))

  3. M = tif0 t1 t2 t3.
     By the induction hypothesis, we have
     [subst F f' (CPS k F t1 continuation naming) =s app k (subst F f (continuation t1))] (when [find_func F (continuation tm_no_F) = 0])
                                                     app k ((subst F f' continuation) (subst F f t1))] (when [find_func F (continuation tm_no_F) = S n]) and
     [subst F f' (CPS k F t2 continuation naming) =s app k (subst F f (continuation t2))] (when [find_func F (continuation tm_no_F) = 0])
                                                     app k ((subst F f' continuation) (subst F f t2))] (when [find_func F (continuation tm_no_F) = S n]) and
     [subst F f' (CPS k F t3 continuation naming) =s app k (subst F f (continuation t3))] (when [find_func F (continuation tm_no_F) = 0])
                                                     app k ((subst F f' continuation) (subst F f t3))] (when [find_func F (continuation tm_no_F) = S n])

     When [find_func F (continuation tm_no_F) = 0],
      ①. When t1 is not recursive, that is to say [find_func F t1 = 0] ,
         consequently [subst F f t1 = t1] and [subst F f' t1 = t1].
            CPS k F M continuation naming
         =s tif0 t1 (CPS k func_name t2 continuation naming) (CPS k func_name t3 continuation naming)

            subst F f' (CPS k F M continuation naming)
         =s subst F f' (tif0 t1 (CPS k func_name t2 continuation naming) (CPS k func_name t3 continuation naming))
         =s tif0 (subst F f' t1) (subst F f' (CPS k func_name t2 continuation naming)) (subst F f' (CPS k func_name t3 continuation naming))
         =s tif0 t1 (app k (subst F f (continuation t2))) (app k (subst F f (continuation t3))) [induction hypothesis]
         =s app k (tif0 (subst F f t1) (subst F f (continuation t2)) (subst F f (continuation t3)))
         =s app k (subst F f (tif0 t1 (continuation t2) (continuation t3)))
         =s app k (subst F f (continuation (tif0 t1 t2 t3)))
         =s app k (subst F f (continuation M))

      ②. When t1 is recursive, that is to say [find_func F t1 = S n1].
            CPS k F M continuation naming
         =s CPS (abs res res) F t1 (fun res => tif0 res (CPS k F t2 continuation (naming + (S n1))) (CPS k F t3 continuation (naming + (S n1)))) naming

            subst F f' (CPS k F M continuation naming)
         =s subst F f' (CPS (abs res res) F t1 (fun res => tif0 res (CPS k F t2 continuation (naming + (S n1))) (CPS k F t3 continuation (naming + (S n1)))) naming)

         To use the induction hypothesis, we need to make it clear whether t2 or t3 is recursive. If not recursive, the CPS fonction can be simplified directly.
         If recursive, [subst F f'] will be applied to [fun res => tif0 res (CPS k F t2 continuation (naming + (S n1))) (CPS k F t3 continuation (naming + (S n1)))],
         thus makes the induction hypothesis available.

     When [find_func F (continuation tm_no_F) = S _],
      ①. When t1 is not recursive, that is to say [find_func F t1 = 0] ,
         consequently [subst F f t1 = t1] and [subst F f' t1 = t1].
            CPS k F M continuation naming
         =s tif0 t1 (CPS k func_name t2 continuation naming) (CPS k func_name t3 continuation naming)

            subst F f' (CPS k F M continuation naming)
         =s subst F f' (tif0 t1 (CPS k func_name t2 continuation naming) (CPS k func_name t3 continuation naming))
         =s tif0 (subst F f' t1) (subst F f' (CPS k func_name t2 continuation naming)) (subst F f' (CPS k func_name t3 continuation naming))
         =s tif0 t1 (app k ((subst F f' continuation) (subst F f t2))) (app k ((subst F f' continuation) (subst F f t3)))
         =s app k (tif0 t1 ((subst F f' continuation) (subst F f t2)) ((subst F f' continuation) (subst F f t3)))
         =s app k ((subst F f' continuation) (tif0 (subst F f t1) (subst F f t2) (subst F f t3)))
         =s app k ((subst F f' continuation) (subst F f (tif0 t1 t2 t3)))
         =s app k ((subst F f' continuation) (subst F f M))

      ②. When t1 is recursive, that is to say [find_func F t1 = S n1].
            CPS k F M continuation naming
         =s CPS (abs res res) F t1 (fun res => tif0 res (CPS k F t2 continuation (naming + (S n1))) (CPS k F t3 continuation (naming + (S n1)))) naming

            subst F f' (CPS k F M continuation naming)
         =s subst F f' (CPS (abs res res) F t1 (fun res => tif0 res (CPS k F t2 continuation (naming + (S n1))) (CPS k F t3 continuation (naming + (S n1)))) naming)

         (There we need not discuss whether t2 or t3 is recursive because continuation is already recursive)

         =s app (abs res res) ((subst F f' (fun res => tif0 res (CPS k F t2 continuation (naming + (S n1))) (CPS k F t3 continuation (naming + (S n1))))) (subst F f t1)) [induction hypothesis]
         =s (subst F f' (fun res => tif0 res (CPS k F t2 continuation (naming + (S n1))) (CPS k F t3 continuation (naming + (S n1))))) (subst F f t1) 
         =s (fun res => subst F f' (tif0 res (CPS k F t2 continuation (naming + (S n1))) (CPS k F t3 continuation (naming + (S n1))))) (subst F f t1)
         =s (fun res => tif0 res (subst F f' (CPS k F t2 continuation (naming + (S n1)))) (subst F f' (CPS k F t3 continuation (naming + (S n1))))) (subst F f t1)
         =s (fun res => tif0 res (app k ((subst F f' continuation) (subst F f t2))) (app k ((subst F f' continuation) (subst F f t3)))) (subst F f t1) [induction hypothesis]
         =s (fun res => app k ((subst F f' continuation) (tif0 res (subst F f t2) (subst F f t3)))) (subst F f t1)
         =s app k ((subst F f' continuation) (tif0 (subst F f t1) (subst F f t2) (subst F f t3)))
         =s app k ((subst F f' continuation) (subst F f (tif0 t1 t2 t3)))
         =s app k ((subst F f' continuation) (subst F f M))

  4. M = tlet x1 t1 t2.
     By the induction hypothesis, we have
     [subst F f' (CPS k F t1 continuation naming) =s app k (subst F f (continuation t1))] (when [find_func F (continuation tm_no_F) = 0])
                                                     app k ((subst F f' continuation) (subst F f t1))] (when [find_func F (continuation tm_no_F) = S n]) and
     [subst F f' (CPS k F t2 continuation naming) =s app k (subst F f (continuation t2))] (when [find_func F (continuation tm_no_F) = 0])
                                                     app k ((subst F f' continuation) (subst F f t2))] (when [find_func F (continuation tm_no_F) = S n]) and
     [subst F f' (CPS k F t3 continuation naming) =s app k (subst F f (continuation t3))] (when [find_func F (continuation tm_no_F) = 0])
                                                     app k ((subst F f' continuation) (subst F f t3))] (when [find_func F (continuation tm_no_F) = S n]).

     When [find_func F (continuation tm_no_F) = 0],
      ①. When both t1 and t2 are not recursive, that is to say [find_func F t1 = 0] and [find_finc F t2 = 0],
         consequently [subst F f t1 = t1], [subst F f t2 = t2], [subst F f' t1 = t1] and [subst F f' t2 = t2].
            CPS k F M continuation naming
         =s app k (continuation (tlet x1 t1 t2))

            subst F f' (CPS k F M continuation naming)
         =s subst F f' (app k (continuation (tlet x1 t1 t2)))
         =s app (subst F f' k) (subst F f' (continuation (tlet x1 t1 t2)))
         =s app k (continuation M)
         =s app k (subst F f (continuation M))

      ②. When t1 is recursive and t2 not, that is to say [find_func F t1 = S n1] and [find_finc F t2 = 0],
         consequently [subst F f t2 = t2] and [subst F f' t2 = t2].
            CPS k F M continuation naming
         =s CPS (abs res res) F t1 (fun res => app k (continuation (tlet x1 res t2))) naming

            subst F f' (CPS k F M continuation naming)
         =s subst F f' (CPS (abs res res) F t1 (fun res => app k (continuation (tlet x1 res t2))) naming)
         =s app (abs res res) (subst F f ((fun res => app k (continuation (tlet x1 res t2))) t1)) [induction hypothesis]
         =s subst F f ((fun res => app k (continuation (tlet x1 res t2))) t1)
         =s (fun res => subst F f (app k (continuation (tlet x1 res t2)))) (subst F f t1)
         =s (fun res => app (subst F f k) (subst F f (continuation (tlet x1 res t2)))) (subst F f t1)
         =s (fun res => app k ((subst F f continuation) (tlet x1 res (subst F f t2)))) (subst F f t1)
         =s app k ((subst F f continuation) (tlet x1 (subst F f t1) (subst F f t2)))
         =s app k (subst F f (continuation (tlet x1 t1 t2)))
         =s app k (subst F f (continuation M))

      ③. When t2 is recursive and t1 not, that is to say [find_func F t1 = 0] and [find_finc F t2 = S n2],
         consequently [subst F f t1 = t1] and [subst F f' t1 = t1].
            CPS k F M continuation naming
         =s CPS k F t2 (fun res => continuation (tlet x1 t1 res)) naming

            subst F f' (CPS k F M continuation naming)
         =s subst F f' (CPS k F t2 (fun res => continuation (tlet x1 t1 res)) naming) [induction hypothesis]
         =s app k (subst F f ((fun res => continuation (tlet x1 t1 res)) t2))
         =s app k ((fun res => subst F f (continuation (tlet x1 t1 res))) (subst F f t2))
         =s app k ((fun res => (subst F f continuation) (tlet x1 (subst F f t1) res)) (subst F f t2))
         =s app k ((subst F f continuation) (tlet x1 (subst F f t1) (subst F f t2)))
         =s app k (subst F f (continuation (tlet x1 t1 t2)))
         =s app k (subst F f (continuation M))

      ④. When both t1 and t2 are recursive, that is to say [find_func F t1 = S n1] and [find_finc F t2 = S n2].
            CPS k F M continuation naming
         =s CPS (abs res res) F t1 (fun res1 => CPS k F t2 (fun res2 => continuation (tlet x1 res1 res2)) (naming + (S n1))) naming

            subst F f' (CPS k F M continuation naming)
         =s subst F f' (CPS (abs res res) F t1 (fun res1 => CPS k F t2 (fun res2 => continuation (tlet x1 res1 res2)) (naming + (S n1))) naming)
         =s app (abs res res) ((subst F f' (fun res1 => CPS k F t2 (fun res2 => continuation (tlet x1 res1 res2)) (naming + (S n1)))) (subst F f t1)) [induction hypothesis]
         =s (subst F f' (fun res1 => CPS k F t2 (fun res2 => continuation (tlet x1 res1 res2)) (naming + (S n1)))) (subst F f t1)
         =s (fun res1 => subst F f' (CPS k F t2 (fun res2 => continuation (tlet x1 res1 res2)) (naming + (S n1)))) (subst F f t1)
         =s (fun res1 => app k (subst F f ((fun res2 => continuation (tlet x1 res1 res2)) t2))) (subst F f t1) [induction hypothesis]
         =s (fun res1 => app k ((fun res2 => (subst F f continuation) (subst F f (tlet x1 res1 res2))) (subst F f t2))) (subst F f t1)
         =s (fun res1 => app k ((fun res2 => (subst F f continuation) (tlet x1 res1 res2)) (subst F f t2))) (subst F f t1)
         =s (fun res1 => app k ((subst F f continuation) (tlet x1 res1 (subst F f t2)))) (subst F f t1)
         =s app k ((subst F f continuation) (tlet x1 (subst F f t1) (subst F f t2)))
         =s app k (subst F f (continuation (tlet x1 t1 t2)))
         =s app k (subst F f (continuation M))

     When [find_func F (continuation tm_no_F) = S _],
      ①. When both t1 and t2 are not recursive, that is to say [find_func F t1 = 0] and [find_finc F t2 = 0],
         consequently [subst F f t1 = t1], [subst F f t2 = t2], [subst F f' t1 = t1] and [subst F f' t2 = t2].
            CPS k F M continuation naming
         =s app k (continuation (tlet x1 t1 t2))

            subst F f' (CPS k F M continuation naming)
         =s subst F f' (app k (continuation (tlet x1 t1 t2)))
         =s app (subst F f' k) (subst F f' (continuation (tlet x1 t1 t2)))
         =s app k ((subst F f' continuation) (subst F f' (tlet x1 t1 t2)))
         =s app k ((subst F f' continuation) (tlet x1 t1 t2))
         =s app k ((subst F f' continuation) (subst F f (tlet x1 t1 t2)))
         =s app k ((subst F f' continuation) (subst F f M))

      ②. When t1 is recursive and t2 not, that is to say [find_func F t1 = S n1] and [find_finc F t2 = 0],
         consequently [subst F f t2 = t2] and [subst F f' t2 = t2].
            CPS k F M continuation naming
         =s CPS (abs res res) F t1 (fun res => app k (continuation (tlet x1 res t2))) naming

            subst F f' (CPS k F M continuation naming)
         =s subst F f' (CPS (abs res res) F t1 (fun res => app k (continuation (tlet x1 res t2))) naming)
         =s app (abs res res) ((subst F f' (fun res => app k (continuation (tlet x1 res t2)))) (subst F f t1)) [induction hypothesis]
         =s (subst F f' (fun res => app k (continuation (tlet x1 res t2)))) (subst F f t1)
         =s (fun res => subst F f' (app k (continuation (tlet x1 res t2)))) (subst F f t1)
         =s (fun res => app (subst F f' k) ((subst F f' continuation) (subst F f' (tlet x1 res t2)))) (subst F f t1)
         =s (fun res => app k ((subst F f' continuation) (tlet x1 res t2))) (subst F f t1)
         =s app k ((subst F f' continuation) (tlet x1 (subst F f t1) (subst F f t2)))
         =s app k ((subst F f' continuation) (subst F f (tlet x1 t1 t2)))
         =s app k ((subst F f' continuation) (subst F f M))

      ③. When t2 is recursive and t1 not, that is to say [find_func F t1 = 0] and [find_finc F t2 = S n2],
         consequently [subst F f t1 = t1] and [subst F f' t1 = t1].
            CPS k F M continuation naming
         =s CPS k F t2 (fun res => continuation (tlet x1 t1 res)) naming

            subst F f' (CPS k F M continuation naming)
         =s subst F f' (CPS k F t2 (fun res => continuation (tlet x1 t1 res)) naming)
         =s app k ((subst F f' (fun res => continuation (tlet x1 t1 res))) (subst F f t2)) [induction hypothesis]
         =s app k ((fun res => (subst F f' continuation) (subst F f' (tlet x1 t1 res))) (subst F f t2))
         =s app k ((fun res => (subst F f' continuation) (tlet x1 t1 res)) (subst F f t2))
         =s app k ((subst F f' continuation) (tlet x1 (subst F f t1) (subst F f t2)))
         =s app k ((subst F f' continuation) (subst F f (tlet x1 t1 t2)))
         =s app k ((subst F f' continuation) (subst F f M))

      ④. When both t1 and t2 are recursive, that is to say [find_func F t1 = S n1] and [find_finc F t2 = S n2].
            CPS k F M continuation naming
         =s CPS (abs res res) F t1 (fun res1 => CPS k F t2 (fun res2 => continuation (tlet x1 res1 res2)) (naming + (S n1))) naming

            subst F f' (CPS k F M continuation naming)
         =s subst F f' (CPS (abs res res) F t1 (fun res1 => CPS k F t2 (fun res2 => continuation (tlet x1 res1 res2)) (naming + (S n1))) naming)
         =s app (abs res res) ((subst F f' (fun res1 => CPS k F t2 (fun res2 => continuation (tlet x1 res1 res2)) (naming + (S n1)))) (subst F f t1)) [induction hypothesis]
         =s (subst F f' (fun res1 => CPS k F t2 (fun res2 => continuation (tlet x1 res1 res2)) (naming + (S n1)))) (subst F f t1)
         =s (fun res1 => subst F f' (CPS k F t2 (fun res2 => continuation (tlet x1 res1 res2)) (naming + (S n1)))) (subst F f t1)
         =s (fun res1 => app k ((subst F f' (fun res2 => continuation (tlet x1 res1 res2))) (subst F f t2))) (subst F f t1) [induction hypothesis]
         =s (fun res1 => app k ((fun res2 => subst F f' (continuation (tlet x1 res1 res2))) (subst F f t2))) (subst F f t1)
         =s (fun res1 => app k ((fun res2 => (subst F f' continuation) (subst F f' (tlet x1 res1 res2))) (subst F f t2))) (subst F f t1)
         =s (fun res1 => app k ((fun res2 => (subst F f' continuation) (tlet x1 res1 res2)) (subst F f t2))) (subst F f t1)
         =s (fun res1 => app k ((subst F f' continuation) (tlet x1 res1 (subst F f t2)))) (subst F f t1)
         =s app k ((subst F f' continuation) (tlet x1 (subst F f t1) (subst F f t2)))
         =s app k ((subst F f' continuation) (subst F f (tlet x1 t1 t2)))
         =s app k ((subst F f' continuation) (subst F f M))

  The theorem is proved.
*)