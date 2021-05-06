Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Frap Require Import Maps.
From Frap Require Import Smallstep.

(* a simple mystlc that only has nat types and supports list, fix and add operation*)

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z
  | multi_mstep : forall (x y z : X),
                    multi R x y ->
                    multi R y z ->
                    multi R x z    
  | multi_1mstep : forall (x y z : X),
                    R x y ->
                    R y z ->
                    multi R x z   
  | multi_1 : forall (x y : X),
                    R x y ->
                    multi R x y                 
                    .


Inductive tm : Type :=
  (* pure mystlc *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> tm -> tm
.

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

(* Notation "'List" :=
  (Ty_List T) (in custom mystlc at level 4). *)

Require Export Ensembles.
Require Export Constructive_sets.
Require Export Classical.

Print Singleton.

Fixpoint FV (x : tm) : Ensemble string :=
  match x with
  | tm_var y =>
      (Singleton string) y
  | tm_abs y t1 =>
      (Subtract string) (FV t1) y
  | <{t1 t2}> =>
      (Union string) (FV t1) (FV t2)
  end.


Inductive value : tm -> Prop :=
| v_abs : forall x t1,
    value (tm_abs x t1)
.

Hint Constructors value : core.



Reserved Notation "'[' x ':=' s ']' t" (in custom mystlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if eqb_string x y then s else t
  | tm_abs y t1 =>
      if eqb_string x y then t else tm_abs y (subst x s t1)
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>

  (* numbers *)
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
  | ST_AppAb : forall x M1 M2,
         M1 --> M2 -> tm_abs x M1 --> tm_abs x M2
  (* numbers *)

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


(*Reserved Notation "x '=b' y" (in custom mystlc at level 20, x constr).
*)
Inductive beta_eq: tm -> tm -> Prop :=
  | M_id : forall M,
      beta_eq M M
  | M_rapply : forall M M1 M2,
      beta_eq M1 M2 -> beta_eq (tm_app M1 M) (tm_app M2 M)
  | M_lapply : forall M M1 M2,
      beta_eq M1 M2 -> beta_eq (tm_app M M1) (tm_app M M2)




  | M_subs : forall x e e1,
      beta_eq <{ {tm_abs x e} e1 }> <{ [ x := e1 ] e }>
  | M_lam : forall M,
      beta_eq <{\x,M}> <{\y,[x:=y]M}>

  
 

  | M_comm : forall M1 M2,
      beta_eq M1 M2 -> beta_eq M2 M1
  | M_trans : forall M1 M2 M3,
      beta_eq M1 M2 -> beta_eq M2 M3 -> beta_eq M1 M3

  .
  
  (*where "x '=b' y'" := (beta_eq x y).*)
Hint Constructors beta_eq : core.

Require Export FrapWithoutSets.

Module Export SN := SetNotations(FrapWithoutSets).
(*
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


Qed. 

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


*)


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






Reserved Notation "t 'l-->' t'" (at level 40).

Inductive lstep : tm -> tm -> Prop :=
  | lST_S : forall x, x l--> x
  | lST_AppAbs : forall x M1 M2,
      M1 l--> M2 -> tm_abs x M1 l--> tm_abs x M2
  | lST_App1 : forall t1 t1' t2 t2',
         t1 l--> t1' -> t2 l--> t2' ->
         <{t1 t2}> l--> <{t1' t2'}>
  | lST_AppAbs0 : forall x t1 v2 t1' v2',
         t1 l--> t1' -> v2 l--> v2' ->
         <{ {tm_abs x t1} v2}> l--> <{ [x:=v2']t1' }>
   where "t 'l-->' t'" := (lstep t t').

   Notation multilstep := (multi lstep).
   Notation "t1 'l-->*' t2" := (multilstep t1 t2) (at level 40).

Search eqb_string.

Search Singleton.

Search eqb_string.

Locate "<>".

Print eq.
(*
Lemma FV_sub : forall x s : var  , forall L,
  FV L x -> FV <{ \ s, L }> x \/ eqb_string x s = true.
Proof.
  intros.
  destruct (eqb_string x0 s0) eqn:E.
  - right. reflexivity.
  - left. 
    simpl.  
Admitted.*)

Print In.

Search not.

Search iff.

Locate "->".


Search (forall P Q , (P <-> Q) -> (~P <-> ~Q)).

Search (forall P Q:Prop , (P -> Q) -> (~Q -> ~P)).

Search (forall A B, (A->B)).

Lemma contrapositive: forall P Q:Prop , (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H HneQ. unfold not in HneQ. unfold not. intros H0. apply H in H0.
  apply HneQ in H0. apply H0.
Qed.




Lemma Singleton_invt: 
forall (U : Type) (x y : U), Ensembles.In U (Singleton U x) y <-> x = y .
Proof.
  intros.
  split.
  apply Singleton_inv.
  apply Singleton_intro.
Qed.

Lemma Singleton_not_invt: 
forall (U : Type) (x y : U), ~ Ensembles.In U (Singleton U x) y <-> x <> y .
Proof.
  intros.
  apply not_iff_compat.
  apply Singleton_invt.
Qed.

Lemma Singleton_not_invt0: 
forall (U : Type) (x y : U), ~ Singleton U x y <-> x <> y .
Proof.
  intros.
  apply not_iff_compat.
  apply Singleton_invt.
Qed.


Lemma eqb_string_sym:(forall P Q, eqb_string P Q = eqb_string Q P).
Proof.
  intros.
  destruct (eqb_string P Q) eqn:E1.
  - destruct (eqb_string Q P) eqn:E2.
    + reflexivity.
    + apply eqb_string_true_iff in E1.
      apply eqb_string_false_iff in E2.
      subst. destruct E2. reflexivity.
  - destruct (eqb_string Q P) eqn:E2.
    + apply eqb_string_true_iff in E2.
      apply eqb_string_false_iff in E1.
      subst. destruct E1. reflexivity.
    + reflexivity.
Qed.

Lemma FV_x : forall x L M,
  ~((FV L) (x)) -> <{([x:=M]L)}> = L.
Proof.
  intros.
  induct L.
  - unfold FV in H. simpl.
    (*assert(H00:( eq s0 )s0). { reflexivity. }
    apply Singleton_ind with (u:=x0) (P:=eq s0) in H00.*)
    assert (not (eq s0 x0)). {
        Search Singleton.
        apply Singleton_not_invt0.
        unfold not.
        unfold Ensembles.In.
        apply H.
    }
    apply eqb_string_false_iff in H0.
    assert (eqb_string s0 x0 = eqb_string x0 s0). { apply eqb_string_sym. }
    rewrite H1 in H0. rewrite H0. reflexivity.

    
  (*Singleton & eqb_string ?? admit. *)
  - simpl. 
    assert (H1: <{ [x0 := M] L1 }> = L1);
    assert (H2: <{ [x0 := M] L2 }> = L2).
    * apply IHL2. simpl in H.
    

    apply contrapositive with (Q:=Ensembles.Union var (FV L1) (FV L2) x0).
    + intros. 
      assert (Ensembles.In string (Ensembles.Union string (FV L1) (FV L2)) x0).
      { apply Union_intror. unfold Ensembles.In. apply H0. }
      apply H1.
    + apply H.
    
    (*UNION? admit. *)
    * apply IHL1. simpl in H.
        
    apply contrapositive with (Q:=Ensembles.Union var (FV L1) (FV L2) x0).
    + intros. 
      assert (Ensembles.In string (Ensembles.Union string (FV L1) (FV L2)) x0).
      { apply Union_introl. unfold Ensembles.In. apply H0. }
      apply H1.
    + apply H.

    (*UNION? admit. *)
    * apply IHL2. simpl in H.

    apply contrapositive with (Q:=Ensembles.Union var (FV L1) (FV L2) x0).
    + intros. 
      assert (Ensembles.In string (Ensembles.Union string (FV L1) (FV L2)) x0).
      { apply Union_intror. unfold Ensembles.In. apply H0. }
      apply H2.
    + apply H.
    
    (*UNION? admit. *)
    * rewrite H1. rewrite H2. reflexivity.
  - simpl. 
    (*NO x0 AFTER SUBSTRACTION*)
    destruct (eqb_string x0 s0) eqn:E.
    * simpl in H. unfold Subtract in H. unfold Setminus in H.
      reflexivity.
    * simpl. 
      rewrite IHL.
      + econstructor.
      + simpl in H. 

        apply contrapositive with (Q:=Subtract var (FV L) s0 x0).
        ++ intros. 
        
        unfold Subtract.
        apply Setminus_intro.
          +++ apply H0.
          +++ 
                  apply Singleton_not_invt0.
                  apply eqb_string_false_iff.
                  rewrite <- E.
                  apply eqb_string_sym.
        ++ apply H.
Qed.



Lemma L2116 : forall x y M N L,
  eqb_string x y = false -> ~((FV L) ( x)) ->
  <{[y:=L]([x:=N]M)}> = <{[x:=[y:=L]N]([y:=L]M)}>.
Proof.
  induct M.
  - simpl. 
  destruct (eqb_string x0 s0) eqn:E1;
  destruct (eqb_string y0 s0) eqn:E2;
  intros;simpl;
  apply eqb_string_false_iff in H.
    + apply eqb_string_true_iff in E1.
      apply eqb_string_true_iff in E2.
      subst. destruct H. reflexivity.
    + destruct (eqb_string x0 s0).
      * reflexivity. * discriminate.
    + destruct (eqb_string y0 s0).
      * simpl. subst. symmetry. apply FV_x. apply H0.
      * discriminate.
    + destruct (eqb_string x0 s0) eqn:E3;
    destruct (eqb_string y0 s0) eqn:E4.
      discriminate.
      discriminate.
      discriminate.
      reflexivity.
  - intros. simpl. 
    assert(eqb_string x0 y0 = false). apply H.
    apply IHM1 with ( N:=N )( L:=L ) in H.
    apply IHM2 with ( N:=N )( L:=L ) in H1.
    rewrite H. rewrite H1. reflexivity.
    apply H0. apply H0.
  - intros. simpl. 
  destruct (eqb_string x0 s0) eqn:E1;destruct (eqb_string y0 s0) eqn:E2.
    + apply eqb_string_false_iff in H. apply eqb_string_true_iff in E1. apply eqb_string_true_iff in E2.
      subst. destruct H. reflexivity.
    + admit. (* 2.1.13 VARIABLE CONVENTION *)
    + admit. (* WE MAY ASSUME THAT *)
    + simpl.
    destruct (eqb_string x0 s0) eqn:E3;destruct (eqb_string y0 s0) eqn:E4;try discriminate. 
    apply IHM with ( N:=N )( L:=L)in H0 .
    rewrite H0. reflexivity. apply H.
Admitted.




Search eqb_string.



Theorem T324 : forall x t1 v2 t1' v2',
t1 l--> t1' -> v2 l--> v2' ->
         <{ [x:=v2](t1) }> l--> <{ [x:=v2'](t1') }>.

Proof.
intros. revert H0. revert v2. revert v2'.
induct H.
- intros. revert H0 x1. simpl. induct x1.
  * simpl. destruct (eqb_string x0 s0). apply H0. econstructor.
  * simpl. econstructor. apply IHx1_1. apply IHx1_2.
  * simpl. destruct (eqb_string x0 s0).
      + econstructor.
      + econstructor. apply IHx1.
- intros. apply IHlstep in H0. simpl. destruct (eqb_string x0 x1).
    + econstructor. apply H.
    + econstructor. apply H0.
- intros. simpl. econstructor. 
    apply IHlstep1. apply H1. 
    apply IHlstep2. apply H1.
- simpl. 
  destruct (eqb_string x0 x1) eqn:E. 
  * (*NOT THE SAME*) admit.
  * intros. rewrite L2116. econstructor.
    + apply IHlstep1. apply H1.
    + apply IHlstep2. apply H1.
    + rewrite <- E. apply eqb_string_sym.
    + simpl. (* [ y ] should not be FV in [ N' ] *)
     unfold FV. (*BOOM*) admit.
Admitted.
(*
         Proof.
  intros. revert H0.
  induct H.
  - intros. revert H0 x1. simpl. induct x1.
    * simpl. destruct (eqb_string x0 s0). apply H0. econstructor.
    * simpl. econstructor. apply IHx1_1. apply IHx1_2.
    * simpl. destruct (eqb_string x0 s0).
        + econstructor.
        + econstructor. apply IHx1.
  - intros. apply IHlstep in H0. simpl. destruct (eqb_string x0 x1).
      + econstructor. apply H.
      + econstructor. apply H0.
  - intros. simpl. econstructor. 
      apply IHlstep1. apply H1. 
      apply IHlstep2. apply H1.
  - simpl. 
  induction (eqb_string x0 x1). 
    * (*NOT THE SAME*) admit.
    * intros. rewrite L2116.    admit.
Admitted.


Proof.
  intros. revert H0. induct H.
  - intros. revert H0 x1. simpl. induct x1.
    * simpl. destruct (eqb_string x0 s0). apply H0. econstructor.
    * simpl. econstructor. apply IHx1_1. apply IHx1_2.
    * simpl. destruct (eqb_string x0 s0).
        + econstructor.
        + econstructor. apply IHx1.
  - intros. apply IHlstep in H0. simpl. destruct (eqb_string x0 x1).
      + econstructor. apply H.
      + econstructor. apply H0.
  - intros. simpl. econstructor. 
      apply IHlstep1. apply H1. 
      apply IHlstep2. apply H1.
  - simpl. induction (eqb_string x0 x1). admit.
    intros.   admit.
Admitted.*)

Inductive l_eq: tm -> tm -> Prop :=
  | l_id : forall M,
      l_eq M M
  | lmST_AppAbs0 : forall x t1 v2 t1' v2',
      l_eq t1 t1' -> l_eq v2 v2' ->
      l_eq <{ {tm_abs x t1} v2}> <{ [x:=v2']t1' }>
  | lmST_AppAbs : forall x M1 M2,
      l_eq M1 M2 -> l_eq (tm_abs x M1)  (tm_abs x M2)
  | lmST_App1 : forall t1 t1' t2 t2',
      l_eq t1  t1' -> l_eq t2  t2' ->
      l_eq <{t1 t2}>  <{t1' t2'}>
  | l_tr : forall M N,
      l_eq M N -> l_eq N M
  | l_trans : forall M1 M2 M3,
      l_eq M1 M2 -> l_eq M2 M3 -> l_eq M1 M3
  .

Hint Constructors l_eq : core.

Theorem l_st_eqv1: forall M1 M2, M1 l--> M2 -> l_eq M1 M2.
Proof.
  eauto. 
  intros. induct H.
  - econstructor.
  - econstructor. apply IHlstep.
  - econstructor. apply IHlstep1. apply IHlstep2.
  - econstructor. apply IHlstep1. apply IHlstep2.
Qed.

Theorem T3251 : forall M M' x N,
  tm_abs x M l--> N -> M l--> M' -> l_eq N (tm_abs x M').
Proof.
  intros. apply l_st_eqv1 in H. econstructor. apply l_st_eqv1 in H0.
  assert (l_eq <{ \ x0, M' }>  <{ \ x0, M }>). { econstructor. econstructor. apply H0. }
  apply l_trans with (M2:=<{ \ x0, M }>). apply H1. apply H.
Qed.
(*
Theorem T32510 : forall M M' x N,
  tm_abs x M l--> N -> M l--> M' ->  N = (tm_abs x M').
Proof.
  intros. induct N.
  - inversion H.
  - inversion H.
  - inversion H.
    * subst.  admit.
    * subst. inversion H. subst.  admit.
Admitted.*)

Theorem T325100 : forall M x N,
  tm_abs x M l--> N -> (exists M' , M l--> M' /\  N = (tm_abs x M') ).
Proof.
  intros. inversion H.
  - subst. exists M. split. econstructor . auto.
  - subst. exists M2. split. apply H3. econstructor. 
Qed.

Theorem T325200 : forall M N L,
  tm_app M N l--> L ->
  (exists M' N', M l--> M' -> N l--> N' ->  L = (tm_app M' N'))
  \/
  (exists P P' N' x, P l--> P' -> N l--> N' -> M = (tm_abs x P) /\ L = ( subst x N' P' ))
  .
Proof.
  intros. inversion H.
  - left. exists M. exists N. intros. econstructor.
  - subst. left. exists t1'. exists t2'. intros. econstructor. 
  - subst. right. exists t1. exists t1'. exists v2'. exists x0. intros. econstructor. econstructor. econstructor. 
Qed.

Theorem T3252 : forall M N L,
  tm_app M N l--> L ->
  (exists M' N', M l--> M' /\ N l--> N' /\  L = (tm_app M' N'))
  \/
  (exists P P' N' x, P l--> P' /\ N l--> N' /\ M = (tm_abs x P) /\ L = ( subst x N' P' ))
  .
Proof.
  intros. inversion H.
  - left. exists M. exists N. intros. econstructor. econstructor. split. econstructor. econstructor.
  - subst. left. exists t1'. exists t2'. intros. econstructor. apply H2. split. apply H4. econstructor. 
  - subst. right. exists t1. exists t1'. exists v2'. exists x0. intros. econstructor. apply H2. econstructor. apply H4. econstructor. econstructor. econstructor. 
Qed.


Theorem T32520 : forall M N L,
  tm_app M N l--> L ->
  (exists M' N', M l--> M' -> N l--> N' ->  l_eq L (tm_app M' N'))
  \/
  (exists P P' N', P l--> P' -> N l--> N' -> l_eq M (tm_abs x P) /\ l_eq L ( subst x N' P' ))
  .
Proof.
  intros.
  inversion H. subst.
  - left. exists M. exists N. intros. econstructor.
  - subst. left. exists t1'. exists t2'. intros. econstructor. 
  - subst. left. exists <{ \ x0, t1 }>. exists v2'. intros. econstructor. econstructor. apply l_st_eqv1. apply H2. econstructor.
Qed.


Definition excluded_middle := forall P : Prop, P \/ ~ P.
Theorem eq_of_or' :
  excluded_middle ->
  forall P Q : Prop, (~ P -> Q) -> P \/ Q.
Proof.
  intros EM P Q.
  destruct (EM P) as [p | np].     (* <- the key part is here *)
  - left. apply p.
  - right.
    apply (H np).
    (* or, equivalently, *)
    Undo.
    apply H.
    apply np.
    Undo 2.
    (* we can also combine two `apply` into one: *)
    apply H, np.
Qed.


(*
Theorem T326_bak : forall M M1 M2, 
M l--> M1 -> M l--> M2 -> 
( exists M3, M1 l--> M3 /\ M2 l--> M3 ).
Proof.

  intros. revert M2 H0. induct H;intros.
  - exists M2. econstructor. subst. apply H0. econstructor.
  - (* CASE 4 *) 
  apply T325100 with (x:=x0) (N:=M0) in H0.
  assert ( H1:  exists M4 : tm, M2 l--> M4 /\ M2 l--> M4). { apply IHlstep. apply H. }
  destruct H1. destruct H1.
  exists (<{ \ x0, x1 }>). split.
  * econstructor. apply H1.
  * destruct H0. destruct H0. subst. econstructor. 
  
     admit. (*STUCK IN SQUARE*)
  - (* CASE 3 *) subst. simpl. apply T3252 in H1. revert H H0. induct H1.
    * (*3.1*)intros. 
    assert( H5: exists M3 : tm, t1' l--> M3 /\ t1' l--> M3 ).
    { apply IHlstep1. apply H0. }
    assert( H6: exists M3 : tm, t2' l--> M3 /\ t2' l--> M3 ).
    { apply IHlstep2. apply H1. }
    destruct H5. destruct H6. destruct H2. destruct H3.
    exists (<{ x0 x1 }> ). split.
    + econstructor. apply H2. apply H3.
    + destruct H. destruct H. 
      (*assert ( H7: t1' = x2 ). { admit. }
      assert ( H8: t2' = x3 ). { admit. }*)
      destruct H. destruct H6. subst.
      econstructor. (*apply H2. apply H3. apply H1.*)
      admit. admit.

    
    (*assert (H7: M2 = <{  x0 x1  }> ). { apply H. admit. admit. }
      rewrite H7.  econstructor.*)

    * (*3.2 NEEDS REVISION *)intros. 
    destruct H as [P1]. destruct H as [P1''].
    destruct H as [t2'']. destruct H as [x]. 
    (*assert ( H5 : t1 = x0 ). { admit. }
    assert ( H6 : t1' = x1 ). { admit. }
    assert ( H7 : t2' = x2 ). { admit. }
    symmetry in H5. symmetry in H6. symmetry in H7.
    subst.*)
    assert (H0' := H0).
    assert (H1' := H1).


    apply IHlstep1 in H0. destruct H0 as [t1''']. destruct H0.
    apply IHlstep2 in H1. destruct H1 as [t2''']. destruct H1.
    subst.
    destruct H. destruct H4. destruct H5.
    subst.

    subst.

    
    (* Lets deal with t1 , AKA P' in the book. *)
    


    (*destruct H.
    assert (H0'' := H0' ).
    apply H in H0'.
    subst.
    destruct H0'.
    subst.
    clear H.
    rewrite H4 in H0''.*)

    apply T325100 in H0'.
    destruct H0' as [P1'].
    destruct H5.
    subst.

    apply T325100 in H0.
    destruct H0 as [P1'''].
    destruct H0.
    subst.



    (*exists*)
    exists <{[x:=t2''']P1'''}>.
    split.
    + econstructor. assumption. assumption. 
    + apply T324. 



    



    assert( H5: exists M3 : tm, t1' l--> M3 /\ t1' l--> M3 ).
    { apply IHlstep1. apply H0. }
    assert( H6: exists M3 : tm, t2' l--> M3 /\ t2' l--> M3 ).
    { apply IHlstep2. apply H1. }
    destruct H5. destruct H6. destruct H2. destruct H3.
    exists (<{ x0 x1 }> ). split.
    + econstructor. apply H2. apply H3.
    + 
     admit.
  - (* CASE 2 *) subst. apply T3252 in H1. revert H H0. induct H1.
    * (*2.1*)  intros.
        assert (H5:exists M3 : tm,
        t1' l--> M3 /\ t1' l--> M3). { apply IHlstep1. apply H0. }
        assert (H6:
        exists M3 : tm,
          v2' l--> M3 /\ v2' l--> M3). { apply IHlstep2. apply H1. }
        destruct H5. destruct H2. destruct H6. destruct H4.

        destruct H. destruct H.

        exists <{ [x0 := x2] x1 }>. split.
          + apply T324. apply H2. apply H4.
          +  (*WHERE DID THAT COME FROM?*) 
          assert(H8:<{ \ x0, t1 }> l--> x3 ).
          admit.
          assert(H9:v2 l--> x4).
          admit. 
          apply H in H8. 
          rewrite H8.
          assert(H10:<{ \ x0, t1 }> l--> x3 ). admit. (*same as H8*)
          apply T32510 with (x:=x0) (N:=x3) in H10.
          admit. admit.
          apply H9.

    * (*2.2*) intros. simpl. subst.  
    
    assert (H5:exists M3 : tm,
        t1' l--> M3 /\ t1' l--> M3). { apply IHlstep1. apply H0. }
        assert (H6:
        exists M3 : tm,
          v2' l--> M3 /\ v2' l--> M3). { apply IHlstep2. apply H1. }
        destruct H5. destruct H2. destruct H6. destruct H4.
        exists <{ [x0 := x2] x1 }>. split.
          + apply T324. apply H2. apply H4.
          +    (*WHERE DID THAT COME FROM?*) admit.

  
Admitted.*)



Lemma STUPID : forall x M N,
<{ \ x, M }> l--> <{ \ x, N }> -> M l--> N.
Proof.
  intros. induct H.
  - econstructor.
  - apply H.
Qed.

Theorem T326 : forall M M1 M2, 
M l--> M1 -> M l--> M2 -> 
( exists M3, M1 l--> M3 /\ M2 l--> M3 ).
Proof.

  intros. revert M2 H0. induct H;intros.
  - exists M2. econstructor. subst. apply H0. econstructor.
  - (* CASE 4 *) 
    inversion H0. 
    * subst. apply STUPID in H0. apply IHlstep in H0. destruct H0.
      destruct H0. 
      exists ( <{ \ x0, x1 }> ).
      split.
      econstructor. assumption.
      econstructor. assumption.
    * subst. apply STUPID in H0. apply IHlstep in H4. destruct H4.
      destruct H1.
      exists ( <{ \ x0, x1 }> ).
      split.
      econstructor. assumption.
      econstructor. assumption.





 (* apply T325100 with (x:=x0) (N:=M0) in H0.
  assert ( H1:  exists M4 : tm, M2 l--> M4 /\ M2 l--> M4). { apply IHlstep. apply H. }
  destruct H1. destruct H1.
  exists (<{ \ x0, x1 }>). split.
  * econstructor. apply H1.
  * destruct H0. destruct H0. subst. econstructor. *)
  

  - (* CASE 3 *) 
    subst. simpl. apply T3252 in H1. revert H H0. induct H1.
    * (*3.1*)
      intros. 
      destruct H as [t1'']. destruct H as [t2''].
      destruct H. destruct H2.
      assert( H' := H ). assert ( H2' := H2 ).
      apply IHlstep1 in H. destruct H as [t1''']. destruct H.
      apply IHlstep2 in H2. destruct H2 as [t2''']. destruct H2.
      exists (<{ t1''' t2''' }> ).
      split.
      + econstructor. assumption. assumption.
      + rewrite H3. econstructor. assumption. assumption.

      * (*3.2 NEEDS REVISION *)intros. 
      destruct H as [P1]. destruct H as [P1''].
      destruct H as [t2'']. destruct H as [x]. 
      (*assert ( H5 : t1 = x0 ). { admit. }
      assert ( H6 : t1' = x1 ). { admit. }
      assert ( H7 : t2' = x2 ). { admit. }
      symmetry in H5. symmetry in H6. symmetry in H7.
      subst.*)
      assert (H0' := H0).
      assert (H1' := H1).


      destruct H. destruct H2. destruct H3. assert ( H2' := H2 ).
      apply IHlstep2 in H2. destruct H2 as [t2''']. destruct H2.
      assert ( H10 : <{ \ x, P1 }> l--> <{ \ x, P1'' }> ).
      { econstructor. apply H. } subst.
      assert ( H10' := H10 ).
      apply IHlstep1 in H10. destruct H10 as [t1''']. destruct H3.

      (*apply IHlstep1 in H0. destruct H0 as [t1''']. destruct H0.
      apply IHlstep2 in H1. destruct H1 as [t2''']. destruct H1.
      subst.
      destruct H. destruct H4. destruct H5.
      subst.*)

      subst.

    
    (* Lets deal with t1 , AKA P' in the book. *)
    


      (*destruct H.
      assert (H0'' := H0' ).
      apply H in H0'.
      subst.
      destruct H0'.
      subst.
      clear H.
      rewrite H4 in H0''.*)

      apply T325100 in H0'.
      destruct H0' as [P1'].
      destruct H6.
      subst.

      apply T325100 in H3.
      destruct H3 as [P1'''].
      destruct H3.
      subst.



      (*exists*)
      exists <{[x:=t2''']P1'''}>.
      split.
      + econstructor. assumption. assumption. 
      + apply T324. apply STUPID in H4. assumption. assumption.



    

  - (* CASE 2 *) 
    subst. apply T3252 in H1. revert H H0. induct H1.
    * (*2.1*)  
      intros.
      destruct H as [tmp]. destruct H as [v2''].
      destruct H. destruct H2. 
      apply T325100 in H.
      destruct H as [P'']. destruct H.
      subst.

      assert(H':=H). assert (H2':=H2).
      apply IHlstep1 in H. destruct H as [P''']. destruct H.
      apply IHlstep2 in H2. destruct H2 as [v2''']. destruct H2.
      exists (<{ [x0 := v2'''] P''' }>).
      split.
      + apply T324. assumption. assumption.
      + econstructor. assumption. assumption.



(*

        assert (H5:exists M3 : tm,
        t1' l--> M3 /\ t1' l--> M3). { apply IHlstep1. apply H0. }
        assert (H6:
        exists M3 : tm,
          v2' l--> M3 /\ v2' l--> M3). { apply IHlstep2. apply H1. }
        destruct H5. destruct H2. destruct H6. destruct H4.

        destruct H. destruct H.

        exists <{ [x0 := x2] x1 }>. split.
          + apply T324. apply H2. apply H4.
          +  (*WHERE DID THAT COME FROM?*) 
          assert(H8:<{ \ x0, t1 }> l--> x3 ).
          admit.
          assert(H9:v2 l--> x4).
          admit. 
          apply H in H8. 
          rewrite H8.
          assert(H10:<{ \ x0, t1 }> l--> x3 ). admit. (*same as H8*)
          apply T32510 with (x:=x0) (N:=x3) in H10.
          admit. admit.
          apply H9.*)

    * (*2.2*) 
      intros.
      destruct H as [P]. destruct H as [P''].
      destruct H as [Q''].
      destruct H as [x]. 
      destruct H. destruct H2. destruct H3.
      inversion H3. 
      subst.
      

      assert(H':=H). assert (H2':=H2).
      apply IHlstep1 in H. destruct H as [P''']. destruct H.
      apply IHlstep2 in H2. destruct H2 as [Q''']. destruct H2.
      exists (<{ [x := Q'''] P''' }>).
      split.
      + apply T324. assumption. assumption.
      + apply T324. assumption. assumption.
Qed.

 (*   apply H in IHlstep1. destruct H1. destruct H1. apply H1.
    exists M2 in H1. subst. exists M2. econstructor. admit. econstructor.
    * subst. exists M2. first_order.  rewrite H7. admit. econstructor. 
    subst.   admit.
  - subst. inversion H. subst. exists M2. econstructor. apply H0. econstructor.
    subst. admit.  

  - induct M2. 
  intros. inversion H.
  - exists M2. econstructor. subst. apply H0. econstructor.
  - subst. inversion H. subst. exists M2. econstructor. apply H0. econstructor.
    subst. exists M2. first_order. rewrite H7. admit. econstructor. 
    subst.   admit.
  - subst. inversion H. subst. exists M2. econstructor. apply H0. econstructor.
    subst. admit.  

  - induct M2. *)









(*
Search multi.

Theorem T327 : forall M N,
  multi lstep M N -> multi step M N.
Proof.
  intros. induct H.
  - econstructor.
  - apply multi_mstep with (y:=y0).
    * clear H0. clear IHmulti.
    induct H.
      + econstructor.
      + admit.
      + apply multi_mstep with (y:=<{ t1 t2' }>).
        ++ admit.
        ++ admit.
      + admit.
    * apply IHmulti.
Admitted.
















From Coq Require Import Relations.

Definition diamond_relation (A : Type) (R : relation A) :=
  forall a b b', R a b -> R a b' -> exists c, R b c /\ R b' c.

Theorem diamond_crt1n : forall {A : Type} {R : relation A},
  diamond_relation A R -> forall a b b',
  clos_refl_trans_1n A R a b ->
  clos_refl_trans_1n A R a b' ->
  exists c, clos_refl_trans_1n A R b c /\ clos_refl_trans_1n A R b' c.
Proof.
  intros A R Hd a b b' ab ab'.
  revert b' ab'; induction ab; intros.
  - exists b'; split; [assumption|constructor].
  - assert (exists y', clos_refl_trans_1n A R y y' /\ clos_refl_trans_1n A R b' y') as [y' [yy' b'y']].
    {
      clear - H Hd ab'; revert y H; induction ab'; intros.
      - exists y; split; [constructor|].
        apply (Relation_Operators.rt1n_trans _ _ _ y); [assumption|constructor].
      - destruct (Hd _ _ _ H H0) as [z' [yz' y0z']].
        destruct (IHab' _ yz') as [y' [z'y' zy']].
        exists y'; split; [|assumption].
        apply (Relation_Operators.rt1n_trans _ _ _ z'); assumption.
    }
    destruct (IHab _ yy') as [c [zc y'c]]; exists c; split; [assumption|].
    apply clos_rt_rt1n.
    refine (rt_trans _ _ _ _ _ (clos_rt1n_rt _ _ _ _ b'y') _).
    apply clos_rt1n_rt; assumption.
Qed.


Theorem coll1 : forall M N,
beta_eq M N -> (exists Z, M --> Z /\ N --> Z).
Proof.
  intros.
  induct H.
  (*;try inversion IHbeta_eq;try exists  <{ x0 :: M }>;try first_order;try econstructor;try apply H0;try econstructor;try apply H1.
 *) 
  - admit.
  - inversion IHbeta_eq. exists (tm_app x0 M). first_order. econstructor. apply H0. econstructor. apply H1.
  - inversion IHbeta_eq. exists (tm_app M x0). first_order. econstructor. admit. apply H0. econstructor. admit. apply H1.
  - admit.
  - inversion IHbeta_eq. exists  <{ x0 + M }>. first_order. econstructor. apply H0. econstructor. apply H1.
  - inversion IHbeta_eq. exists  <{ M + x0 }>. first_order. econstructor. admit. apply H0. econstructor. admit. apply H1.
  - inversion IHbeta_eq. exists  <{ x0 :: M }> . first_order. econstructor. apply H0. econstructor. apply H1.
  - inversion IHbeta_eq. exists  <{ M :: x0 }> . first_order. econstructor. admit. apply H0. econstructor. admit. apply H1.
  - inversion IHbeta_eq. exists  <{ case x0 of | nil => t2 | x1 :: x2 => t3 }>. first_order. econstructor. apply H0. econstructor. apply H1.
  - admit.
  - admit.
  - admit.
  - 

Admitted.

Theorem coll2 : forall M N,
beta_eq M N -> (exists Z, M -->* Z /\ N -->* Z).
Proof.
  intros.
  induct H.
  - admit.
  - inversion IHbeta_eq. exists (tm_app x0 M). first_order. econstructor.

Theorem Be_C_R2 : forall M M1 M2, M -->* M1 -> M -->* M2 -> ( exists M', M1 -->* M' /\ M2 -->* M' ).
Proof.
   eauto. intros. apply Be_C_R0. induct M. 
   - intros. inversion H. inversion H0. exists tm_invalid. first_order. econstructor. econstructor. admit.
   - intros. inversion H. 
   - intros. admit.
   - intros. apply IHM. inversion H. inversion H0.
   - intros. inversion H.
   - intros. admit.
   - intros. inversion H.
   - intros. admit.
   - intros. admit.
   - intros. admit.


(*
l reduction Proof
beta diff
*)

*)