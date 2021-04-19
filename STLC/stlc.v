Require Export Coq.Strings.String.
Require Export Coq.Arith.PeanoNat.
From Coq Require Export Datatypes.

(*string*)
Fixpoint nat2string (n : nat) : string :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
  | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9" | S (S (S (S (S (S (S (S (S (S n'))))))))) => "'" ++ nat2string n' end.

(*map*)
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition total_map (X : Type) := string -> X.

Definition t_empty {X : Type} (default : X) : total_map X :=
  (fun _ => default).

Definition t_update {X : Type} (m : total_map X)
                    (key : string) (value : X) :=
  fun x : string => if eqb_string key x then value else m x.

Notation " '_' '!->' default " := (t_empty default)
  (at level 100, right associativity).

Notation " key '!->' value ';' m " := (t_update m key value)
                              (at level 100, value at next level, right associativity).

Definition partial_map (X : Type) := total_map (option X).

Definition empty {X : Type} : partial_map X :=
  t_empty None.

Definition update {X : Type} (m : partial_map X)
           (key : string) (value : X) :=
  (key !-> Some value ; m).

Notation "key '|->' value ';' m" := (update m key value)
  (at level 100, value at next level, right associativity).

Notation "key '|->' value" := (update empty key value)
  (at level 100).

(*type*)
Inductive ty : Type :=
  | Nat  : ty
  | List : ty -> ty
  | BinaryTree : ty -> ty
  | Arrow : ty -> ty -> ty.

(*term*)
Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  
  | tconst : nat -> tm
  | tplus : tm -> tm -> tm
  | tminus : tm -> tm -> tm
  | tmult : tm -> tm -> tm
  | tif0  : tm -> tm -> tm -> tm
  
  | tnil : ty -> tm
  | tcons : tm -> tm -> tm
  | tlcase : tm -> tm -> string -> string -> tm -> tm
  
  | tleaf : tm -> tm
  | tnode : tm -> tm -> tm -> tm
  | tbcase : tm -> string -> tm -> string -> string -> string -> tm -> tm
  
  | tlet : string -> tm -> tm -> tm
  
  | tfix  : tm -> tm.

(*notation and coercion*)
Coercion var : string >-> tm.
Coercion tconst : nat >-> tm.

Declare Custom Entry stlc.
Declare Custom Entry stlc_ty.

Definition a : string := "a".
Definition b : string := "b".
Definition c : string := "c".
Definition k : string := "k".
Definition l : string := "l".
Definition l' : string := "l'".
Definition l'' : string := "l''".
Definition l1 : string := "l1".
Definition l1' : string := "l1'".
Definition l2 : string := "l2".
Definition l2' : string := "l2'".
Definition f : string := "f".
Definition g : string := "g".
Definition h : string := "h".
Definition n : string := "n".
Definition n' : string := "n'".
Definition n1 : string := "n1".
Definition n1' : string := "n1'".
Definition n2 : string := "n2".
Definition n2' : string := "n2'".
Definition t : string := "t".
Definition t' : string := "t'".
Definition t1 : string := "t1".
Definition t1' : string := "t1'".
Definition t2 : string := "t2".
Definition t2' : string := "t2'".
Definition tl : string := "tl".
Definition tr : string := "tr".
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition hd : string := "hd".
Definition hd' : string := "hd'".
Definition hd1 : string := "hd1".
Definition hd2 : string := "hd2".
Definition tail : string := "tail".
Definition tail' : string := "tail'".
Definition tail1 : string := "tail1".
Definition tail2 : string := "tail2".
Definition res : string := "res".
Definition res1 : string := "res1".
Definition res2 : string := "res2".
Definition res3 : string := "res3".
Definition res4 : string := "res4".
Definition res5 : string := "res5".

Hint Unfold a : core.
Hint Unfold b : core.
Hint Unfold c : core.
Hint Unfold k : core.
Hint Unfold l : core.
Hint Unfold l' : core.
Hint Unfold l'' : core.
Hint Unfold l1 : core.
Hint Unfold l1' : core.
Hint Unfold l2 : core.
Hint Unfold l2' : core.
Hint Unfold f : core.
Hint Unfold g : core.
Hint Unfold h : core.
Hint Unfold n : core.
Hint Unfold n' : core.
Hint Unfold n1 : core.
Hint Unfold n1' : core.
Hint Unfold n2 : core.
Hint Unfold n2' : core.
Hint Unfold t : core.
Hint Unfold t' : core.
Hint Unfold t1 : core.
Hint Unfold t1' : core.
Hint Unfold t2 : core.
Hint Unfold t2' : core.
Hint Unfold tl : core.
Hint Unfold tr : core.
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Hint Unfold hd : core.
Hint Unfold hd' : core.
Hint Unfold hd1 : core.
Hint Unfold hd2 : core.
Hint Unfold tail : core.
Hint Unfold tail' : core.
Hint Unfold tail1 : core.
Hint Unfold tail2 : core.
Hint Unfold res : core.
Hint Unfold res1 : core.
Hint Unfold res2 : core.
Hint Unfold res3 : core.
Hint Unfold res4 : core.
Hint Unfold res5 : core.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
Notation "S -> T" := (Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "x y" := (app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "x + y" := (tplus x y) (in custom stlc at level 1,
                                      left associativity).
Notation "x - y" := (tminus x y) (in custom stlc at level 1,
                                      left associativity).
Notation "x * y" := (tmult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tif0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).

Notation "'nil' T" := (tnil T) (in custom stlc at level 0, T custom stlc_ty at level 0).
Notation "h '::' t" := (tcons h t) (in custom stlc at level 2, right associativity).
Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' x '::' y '=>' t3" :=
  (tlcase t1 t2 x y t3) (in custom stlc at level 89,
                              t1 custom stlc at level 99,
                              t2 custom stlc at level 99,
                              x constr at level 1,
                              y constr at level 1,
                              t3 custom stlc at level 99,
                              left associativity).

Notation "'let' x '=' t1 'in' t2" :=
  (tlet x t1 t2) (in custom stlc at level 0).

Notation "'fix' t" := (tfix t) (in custom stlc at level 0).

Notation idNat := <{\ x : Nat, x}>.

(*substitution*)
Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var y =>
       if eqb x y then s else t
  | abs y T t1 =>
       if eqb x y then t else abs y T (subst x s t1)
  | app t1 t2 =>
       app (subst x s t1) (subst x s t2)
  
  | tconst _ =>
       t
  | tplus t1 t2 =>
       tplus (subst x s t1) (subst x s t2)
  | tminus t1 t2 =>
       tminus (subst x s t1) (subst x s t2)
  | tmult t1 t2 =>
       tmult (subst x s t1) (subst x s t2)
  | tif0 t1 t2 t3 =>
       tif0 (subst x s t1) (subst x s t2) (subst x s t3)
  
  | tnil _ =>
       t
  | tcons t1 t2 =>
       tcons (subst x s t1) (subst x s t2)
  | tlcase t1 t2 y1 y2 t3 =>
       tlcase (subst x s t1) (subst x s t2) y1 y2 (if eqb x y1 then t3 else if eqb x y2 then t3 else subst x s t3)
  
  | tleaf t1 =>
       tleaf (subst x s t1)
  | tnode t1 t2 t3 =>
       tnode (subst x s t1) (subst x s t2) (subst x s t3)
  | tbcase t1 y1 t2 y2 y3 y4 t3 =>
       tbcase (subst x s t1) y1 (if eqb x y1 then t2 else subst x s t2) y2 y3 y4 (if eqb x y2 then t3 else if eqb x y3 then t3 else if eqb x y4 then t3 else subst x s t3)
  
  | tlet y t1 t2 =>
       tlet y (subst x s t1) (if eqb x y then t2 else subst x s t2)
  
  | tfix t1 =>
       tfix (subst x s t1)
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(*value*)
Inductive value : tm -> Prop :=
  | V_Abs : forall x T t,
       value (abs x T t)
  
  | V_Nat : forall n : nat,
       value (tconst n)
  
  | V_Nil : forall T,
       value (tnil T)
  | V_Cons : forall v1 v2,
       value v1 ->
       value v2 ->
       value (tcons v1 v2)
  
  | V_Leaf : forall v1,
       value v1 ->
       value (tleaf v1)
  | V_Node : forall v1 v2 v3,
       value v1 ->
       value v2 ->
       value v3 ->
       value (tnode v1 v2 v3).

Hint Constructors value : core.

(*smallstep*)
Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | mult_refl : forall x : X, multi R x x
  | mult_step : forall x y z : X, R x y -> multi R y z -> multi R x z.

Reserved Notation "t '-->' t'" (at level 40).

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
  
  | ST_PlusConsts : forall n1 n2 : nat,
       step (tplus (tconst n1) (tconst n2)) (tconst (n1 + n2))
  | ST_Plus1 : forall t1 t1' t2,
       step t1 t1' ->
       step (tplus t1 t2) (tplus t1' t2)
  | ST_Plus2 : forall v1 t2 t2',
       value v1 ->
       step t2 t2' ->
       step (tplus v1 t2) (tplus v1 t2')
  | ST_MinusConsts : forall n1 n2 : nat,
       step (tminus (tconst n1) (tconst n2)) (tconst (n1 - n2))
  | ST_Minus1 : forall t1 t1' t2,
       step t1 t1' ->
       step (tminus t1 t2) (tminus t1' t2)
  | ST_Minus2 : forall v1 t2 t2',
       value v1 ->
       step t2 t2' ->
       step (tminus v1 t2) (tminus v1 t2')
  | ST_MultConsts : forall n1 n2 : nat,
       step (tmult (tconst n1) (tconst n2)) (tconst (n1 * n2))
  | ST_Mult1 : forall t1 t1' t2,
       step t1 t1' ->
       step (tmult t1 t2) (tmult t1' t2)
  | ST_Mult2 : forall v1 t2 t2',
       value v1 ->
       step t2 t2' ->
       step (tmult v1 t2) (tmult v1 t2')
  | ST_If0 : forall t1 t1' t2 t3,
       step t1 t1' ->
       step (tif0 t1 t2 t3) (tif0 t1' t2 t3)
  | ST_If0Zero : forall t2 t3,
       step (tif0 (tconst 0) t2 t3) t2
  | ST_If0Nonzero : forall n t2 t3,
       step (tif0 (tconst (S n)) t2 t3) t3
  
  | ST_Cons1 : forall t1 t1' t2,
       step t1 t1' ->
       step (tcons t1 t2) (tcons t1' t2)
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       step t2 t2' ->
       step (tcons v1 t2) (tcons v1 t2')
  | ST_LCase : forall t1 t1' t2 x1 x2 t3,
       step t1 t1' ->
       step (tlcase t1 t2 x1 x2 t3) (tlcase t1' t2 x1 x2 t3)
  | ST_LCaseNil : forall T t2 x1 x2 t3,
       step (tlcase (tnil T) t2 x1 x2 t3) t2
  | ST_LCaseCons : forall v1 v2 t2 x1 x2 t3,
       value v1 ->
       value v2 ->
       step (tlcase (tcons v1 v2) t2 x1 x2 t3) (subst x2 v2 (subst x1 v1 t3))
  
  | ST_Leaf : forall t1 t1',
       step t1 t1' ->
       step (tleaf t1) (tleaf t1')
  | ST_Node1 : forall t1 t1' t2 t3,
       step t1 t1' ->
       step (tnode t1 t2 t3) (tnode t1' t2 t3)
  | ST_Node2 : forall v1 t2 t2' t3,
       value v1 ->
       step t2 t2' ->
       step (tnode v1 t2 t3) (tnode v1 t2' t3)
  | ST_Node3 : forall v1 v2 t3 t3',
       value v1 ->
       value v2 ->
       step t3 t3' ->
       step (tnode v1 v2 t3) (tnode v1 v2 t3')
  | ST_BCase : forall t1 t1' x1 t2 x2 x3 x4 t3,
       step t1 t1' ->
       step (tbcase t1 x1 t2 x2 x3 x4 t3) (tbcase t1' x1 t2 x2 x3 x4 t3)
  | ST_BCaseLeaf : forall v1 x1 t2 x2 x3 x4 t3,
       value v1 ->
       step (tbcase (tleaf v1) x1 t2 x2 x3 x4 t3) (subst x1 v1 t2)
  | ST_BCaseNode : forall v1 v2 v3 x1 t2 x2 x3 x4 t3,
       value v1 ->
       value v2 ->
       value v3 ->
       step (tbcase (tnode v1 v2 v3) x1 t2 x2 x3 x4 t3) (subst x4 v3 (subst x3 v2 (subst x2 v1 t3)))
  
  | ST_Let : forall x t1 t1' t2,
       step t1 t1' ->
       step (tlet x t1 t2) (tlet x t1' t2)
  | ST_LetValue : forall x v1 t2,
       value v1 ->
       step (tlet x v1 t2) (subst x v1 t2)
  
  | ST_Fix : forall t1 t1',
       step t1 t1' ->
       step (tfix t1) (tfix t1')
  | ST_FixAbs : forall xf T t,
      step (tfix (abs xf T t)) (subst xf (tfix (abs xf T t)) t)

  where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

(*typing*)
Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
       Gamma x = Some T1 ->
       has_type Gamma x T1
  | T_Abs : forall Gamma x t1 T1 T2,
       has_type (x |-> T2 ; Gamma) t1 T1 ->
       has_type Gamma (abs x T2 t1) (Arrow T2 T1)
  | T_App : forall Gamma t1 T1 t2 T2,
       has_type Gamma t1 (Arrow T2 T1) ->
       has_type Gamma t2 T2 ->
       has_type Gamma (app t1 t2) T1
  
  | T_Nat : forall Gamma (n : nat),
       has_type Gamma n Nat
  | T_Plus : forall Gamma t1 t2,
       has_type Gamma t1 Nat ->
       has_type Gamma t2 Nat ->
       has_type Gamma (tplus t1 t2) Nat
  | T_Minus : forall Gamma t1 t2,
       has_type Gamma t1 Nat ->
       has_type Gamma t2 Nat ->
       has_type Gamma (tminus t1 t2) Nat
  | T_Mult : forall Gamma t1 t2,
       has_type Gamma t1 Nat ->
       has_type Gamma t2 Nat ->
       has_type Gamma (tmult t1 t2) Nat
  | T_If0 : forall Gamma t1 t2 t3 T0,
       has_type Gamma t1 Nat ->
       has_type Gamma t2 T0 ->
       has_type Gamma t3 T0 ->
       has_type Gamma (tif0 t1 t2 t3) T0
  
  | T_Nil : forall Gamma T1,
       has_type Gamma (tnil T1) (List T1)
  | T_Cons : forall Gamma t1 t2 T1,
       has_type Gamma t1 T1 ->
       has_type Gamma t2 (List T1) ->
       has_type Gamma (tcons t1 t2) (List T1)
  | T_LCase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
       has_type Gamma t1 (List T1) ->
       has_type Gamma t2 T2 ->
       has_type (x1 |-> T1 ; x2 |-> (List T1) ; Gamma) t3 T2 ->
       has_type Gamma (tlcase t1 t2 x1 x2 t3) T2
  
  | T_Leaf : forall Gamma t1 T1,
       has_type Gamma t1 T1 ->
       has_type Gamma (tleaf t1) (BinaryTree T1)
  | T_Node : forall Gamma t1 t2 t3 T1,
       has_type Gamma t1 T1 ->
       has_type Gamma t2 (BinaryTree T1) ->
       has_type Gamma t3 (BinaryTree T1) ->
       has_type Gamma (tnode t1 t2 t3) (BinaryTree T1)
  | T_BCase : forall Gamma t1 T1 x1 t2 T2 x2 x3 x4 t3,
       has_type Gamma t1 (BinaryTree T1) ->
       has_type (x1 |-> T1) t2 T2 ->
       has_type (x2 |-> T1 ; x3 |-> (BinaryTree T1) ; x4 |-> (BinaryTree T1) ; Gamma) t3 T2 ->
       has_type Gamma (tbcase t1 x1 t2 x2 x3 x4 t3) T2
  
  | T_Let : forall Gamma x t1 T1 t2 T2,
       has_type Gamma t1 T1 ->
       has_type (x |-> T1 ; Gamma) t2 T2 ->
       has_type Gamma (tlet x t1 t2) T2
  
  | T_Fix : forall Gamma t1 T1,
       has_type Gamma t1 (Arrow T1 T1) ->
       has_type Gamma (tfix t1) T1

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

(*tactics*)
Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply mult_step ;
            [ (eauto 25; fail) | (instantiate; simpl)]);
  apply mult_refl. 

Tactic Notation "solve_CPS" := simpl; normalize.

Hint Extern 2 (has_type _ (app _ _) _) =>
  eapply T_App; auto : core.
Hint Extern 2 (has_type _ (tlcase _ _ _ _ _) _) =>
  eapply T_LCase; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.
(*using the tactic [normalize] to prove multistep relations*)
(*using the tactic [eauto n : nat] to prove type-related propositions*)

(*example*)
Example nat_square :=
  abs "x" Nat (tmult (var "x") (var "x")).

Example do_it_three_times :=
  abs "f" (Arrow Nat Nat) (abs "y" Nat ((app (var "f") (app (var "f") (app (var "f") (var "y")))))).

Example sum_of_list :=
  tfix (abs "f" (Arrow (List Nat) Nat) (abs "l" (List Nat) (tlcase (var "l") (tconst 0) "l1" "l2" (tplus (var "l1") (app (var "f") (var "l2")))))).

Example sum_of_list_CPS :=
  tfix (abs "f" (Arrow (List Nat) (Arrow (Arrow Nat Nat) Nat)) (abs "l" (List Nat) (abs "k" (Arrow Nat Nat) (tlcase (var "l") (app (var "k") (tconst 0)) "l1" "l2" (app (app (var "f") (var "l2")) (abs "hole" Nat (app (var "k") (tplus (var "l1") (var "hole"))))))))).

Example stlc1 :
  (app nat_square (tconst 3)) -->* 9.
Proof. unfold nat_square. normalize. Qed.

Example stlc2 :
  (app (app do_it_three_times idNat) 5) -->* 5.
Proof. unfold do_it_three_times. normalize. Qed.

Example stlc3 :
  (app sum_of_list (tcons 1 (tcons 2 (tcons 3 (tcons 4 (tcons 5 (tnil Nat))))))) -->* 15.
Proof. unfold sum_of_list. normalize. Qed.

Example stlc4 :
  (app (app sum_of_list_CPS (tcons 1 (tcons 2 (tcons 3 (tcons 4 (tcons 5 (tnil Nat))))))) idNat) -->* 15.
Proof. unfold sum_of_list_CPS. normalize. Qed.

Example stlc5 :
  (app (app do_it_three_times nat_square) (tconst 2)) -->* 256.
Proof. unfold do_it_three_times. unfold nat_square. normalize. Qed.

Example type1 :
  has_type empty (app nat_square 1) Nat.
Proof with eauto. unfold nat_square. eauto 5. Qed.

Example type2 :
  has_type empty do_it_three_times (Arrow (Arrow Nat Nat) (Arrow Nat Nat)).
Proof with eauto. unfold do_it_three_times. eauto 5. Qed.

Example type3 :
  has_type empty sum_of_list (Arrow (List Nat) Nat).
Proof with eauto. unfold sum_of_list. eauto 5. Qed.

Example type4 :
  has_type empty sum_of_list_CPS (Arrow (List Nat) (Arrow (Arrow Nat Nat) Nat)).
Proof with eauto. unfold sum_of_list_CPS. eauto 5. Qed.

(*[M1 M2] where M1 is recursive*)
Definition factorial_left :=
  tfix (abs "f" (Arrow Nat Nat)
    (abs "n" Nat
      (tif0 (var "n") (tconst 1)
        (tmult (app (var "f") (tminus (var "n") (tconst 1))) (var "n"))))).

Print factorial_left.

Definition factorial_left_CPS :=
  tfix (abs "f" (Arrow Nat (Arrow (Arrow Nat Nat) Nat))
    (abs "n" Nat
      (abs "k" (Arrow Nat Nat)
        (tif0 (var "n") (app (var "k") (tconst 1))
          (app (app (var "f") (tminus (var "n") (tconst 1)))
            (abs "hole" (Arrow Nat Nat)
              (app (var "k") (tmult (var "hole") (var "n"))))))))).

Print factorial_left_CPS.

Example factorial_left_correct :
  ((app factorial_left (tconst 5)) -->* 120) /\ ((app (app factorial_left_CPS (tconst 5)) idNat) -->* 120).
Proof.
  unfold factorial_left. unfold factorial_left_CPS. split. normalize. normalize. Qed.

(*[M1 M2] where M2 is recursive*)

Definition factorial_right :=
  tfix (abs "f" (Arrow Nat Nat)
    (abs "n" Nat
      (tif0 (var "n") (tconst 1)
        (tmult (var "n") (app (var "f") (tminus (var "n") (tconst 1))))))).

Print factorial_right.

Definition factorial_right_CPS :=
  tfix (abs "f" (Arrow Nat (Arrow (Arrow Nat Nat) Nat))
    (abs "n" Nat
      (abs "k" (Arrow Nat Nat)
        (tif0 (var "n") (app (var "k") (tconst 1))
          (app (app (var "f") (tminus (var "n") (tconst 1)))
            (abs "hole" (Arrow Nat Nat)
              (app (var "k") (tmult (var "n") (var "hole"))))))))).

Print factorial_right_CPS.

Example factorial_right_correct :
  ((app factorial_right (tconst 5)) -->* 120) /\ ((app (app factorial_right_CPS (tconst 5)) idNat) -->* 120).
Proof.
  unfold factorial_right. unfold factorial_right_CPS. split. normalize. normalize. Qed.

(*CPS conversion*)

(*
  For a [tm], it is recursive if wrapped with
  [fix (\ f : _, _body_)], where the _body_ may be an
  abstration, application or other terms. For paramiterized
  non-pure STLCs, they can be thought as applications such as:

       [tm_mult t1 t2]   <{t1 * t2}>
  ==>  [M1 M2] where M1 = [tm_mult t1] and M2 = [t2]

  For an application [M1 M2], we can translate it into such a
  manner:

  if both are not recursive, we apply it to the continuation
  function k :
        [M1 M2] = k (M1 M2)

  if only M1 is recursive, that's to say M1 admit another
  parameter :
        [M1 M2] = [M1] (fun hole => k (hole M2))

  if only M2 is recursive, that's to say M2 admit another
  parameter :
        [M1 M2] = [M2] (fun hole => k (M1 hole))

  if both are recursive :
        [M1 M2] = [M1] (fun hole1 => [M2] (fun hole2 => k (hole1 hole2)))
*)

(*Some helper functions*)
Fixpoint get_output_type (type : ty) : ty :=
  match type with
  | Arrow ty1 ty2 => get_output_type ty2
  | _ => type
  end.

Fixpoint type_insert (original_type insert_type : ty) : ty :=
  match original_type with
  | Arrow ty1 ty2 => Arrow ty1 (type_insert ty2 insert_type)
  | _ => Arrow insert_type original_type
  end.

Fixpoint para_insert (para_name : string) (para_type : ty) (func_body : tm) : tm :=
  match func_body with
  | abs x1 T t1 => abs x1 T (para_insert para_name para_type t1)
  | _ => abs para_name para_type func_body
  end.

Module initial_version.

(*
  An initial version of CPS conversion which can not deal with complicated
  pattern matching and requires a parameter [fuel] to get accepted by Coq.
*)

Fixpoint find_func (func_name : string) (func_body : tm) : nat :=
  match func_body with
  | var x1 =>
       if eqb x1 func_name then 1 else 0
  | abs x1 T t1 =>
       find_func func_name t1 (*shadowing*)
  | app t1 t2 =>
       (find_func func_name t1) + (find_func func_name t2)
  
  | tconst _ =>
       0
  | tplus t1 t2 =>
       (find_func func_name t1) + (find_func func_name t2)
  | tminus t1 t2 =>
       (find_func func_name t1) + (find_func func_name t2)
  | tmult t1 t2 =>
       (find_func func_name t1) + (find_func func_name t2)
  | tif0 t1 t2 t3 =>
       (find_func func_name t2) + (find_func func_name t3) (*order*)
  
  | tnil T =>
       0
  | tcons t1 t2 =>
       (find_func func_name t1) + (find_func func_name t2)
  | tlcase t1 t2 x1 x2 t3 =>
       (find_func func_name t2) + (find_func func_name t3) (*order*)
  
  | tleaf t1 =>
       find_func func_name t1
  | tnode t1 t2 t3 =>
       (find_func func_name t1) + (find_func func_name t2) + (find_func func_name t3)
  | tbcase t1 x1 t2 x2 x3 x4 t3 =>
       (find_func func_name t2) + (find_func func_name t3) (*order*)
  
  | tlet x1 t1 t2 => (*order*)
       find_func func_name t2
  
  | tfix t1 =>
       find_func func_name t1
  end.

Fixpoint is_location (func_name : string) (func_body : tm) : bool :=
  match func_body with
  | var x1 =>
       eqb x1 func_name
  | app t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | 1, 0 => is_location func_name t1
       | _, _ => false
       end
  | _ =>
       false
  end.

Fixpoint extract_and_substitute (func_name : string) (func_body : tm) (substitution : string) : tm * tm :=
  if is_location func_name func_body
  then (func_body, var substitution)
  else match func_body with
  | abs x1 T t1 =>
       let (para1, para2) := extract_and_substitute func_name t1 substitution
       in (para1, abs x1 T para2)
  | app t1 t2 =>
       match find_func func_name t1 with
       | S _ =>
            let (para1, para2) := extract_and_substitute func_name t1 substitution
            in (para1, app para2 t2)
       | O =>
            let (para1, para2) := extract_and_substitute func_name t2 substitution
            in (para1, app t1 para2)
       end
  
  | tplus t1 t2 =>
       match find_func func_name t1 with
       | S _ =>
            let (para1, para2) := extract_and_substitute func_name t1 substitution
            in (para1, tplus para2 t2)
       | O =>
            let (para1, para2) := extract_and_substitute func_name t2 substitution
            in (para1, tplus t1 para2)
       end
  | tminus t1 t2 =>
       match find_func func_name t1 with
       | S _ =>
            let (para1, para2) := extract_and_substitute func_name t1 substitution
            in (para1, tminus para2 t2)
       | O =>
            let (para1, para2) := extract_and_substitute func_name t2 substitution
            in (para1, tminus t1 para2)
       end
  | tmult t1 t2 =>
       match find_func func_name t1 with
       | S _ =>
            let (para1, para2) := extract_and_substitute func_name t1 substitution
            in (para1, tmult para2 t2)
       | O =>
            let (para1, para2) := extract_and_substitute func_name t2 substitution
            in (para1, tmult t1 para2)
       end
  | tif0 t1 t2 t3 =>
       match find_func func_name t2 with
       | S _ =>
            let (para1, para2) := extract_and_substitute func_name t2 substitution
            in (para1, tif0 t1 para2 t3)
       | O =>
            let (para1, para2) := extract_and_substitute func_name t3 substitution
            in (para1, tif0 t1 t2 para2)
       end
  
  | tcons t1 t2 =>
       match find_func func_name t1 with
       | S _ =>
            let (para1, para2) := extract_and_substitute func_name t1 substitution
            in (para1, tcons para2 t2)
       | O =>
            let (para1, para2) := extract_and_substitute func_name t2 substitution
            in (para1, tcons t1 para2)
       end
  | tlcase t1 t2 x1 x2 t3 =>
       match find_func func_name t2 with
       | S _ =>
            let (para1, para2) := extract_and_substitute func_name t2 substitution
            in (para1, tlcase t1 para2 x1 x2 t3)
       | O =>
            let (para1, para2) := extract_and_substitute func_name t3 substitution
            in (para1, tlcase t1 t2 x1 x2 para2)
       end
  
  | tleaf t1 =>
       let (para1, para2) := extract_and_substitute func_name t1 substitution
       in (para1, tleaf para2)
  | tnode t1 t2 t3 =>
       match find_func func_name t1 with
       | S _ =>
            let (para1, para2) := extract_and_substitute func_name t1 substitution
            in (para1, tnode para2 t2 t3)
       | O =>
            match find_func func_name t2 with
            | S _ =>
                 let (para1, para2) := extract_and_substitute func_name t2 substitution
                 in (para1, tnode t1 para2 t3)
            | O =>
                 let (para1, para2) := extract_and_substitute func_name t3 substitution
                 in (para1, tnode t1 t2 para2)
            end
       end
  | tbcase t1 x1 t2 x2 x3 x4 t3 =>
       match find_func func_name t2 with
       | S _ =>
            let (para1, para2) := extract_and_substitute func_name t2 substitution
            in (para1, tbcase t1 x1 para2 x2 x3 x4 t3)
       | O =>
            let (para1, para2) := extract_and_substitute func_name t3 substitution
            in (para1, tbcase t1 x1 t2 x2 x3 x4 para2)
       end
  
  | tlet x1 t1 t2 =>
       if find_func x1 t2
       then match find_func func_name t1 with
            | S _ =>
                 let (para1, para2) := extract_and_substitute func_name t1 substitution
                 in (para1, tlet x1 para2 t2)
            | O =>
                 let (para1, para2) := extract_and_substitute func_name t2 substitution
                 in (para1, tlet x1 t1 para2)
            end
       else let (para1, para2) := extract_and_substitute func_name t2 substitution
       in (para1, tlet x1 t1 para2)
  
  | tfix t1 =>
       let (para1, para2) := extract_and_substitute func_name t1 substitution
       in (para1, tfix para2)
  
  | _ =>
       (func_body, func_body)
  end.

Fixpoint CPS (func_name : string) (output_type : ty) (func_body : tm) (naming : nat) (fuel : nat) : tm :=
  match fuel with | O => func_body | S fuel' =>
    match func_body with
    | abs x1 T t1 =>
         abs x1 T (CPS func_name output_type t1 naming fuel')
  
    | tif0 t1 t2 t3 =>
         tif0 t1 (CPS func_name output_type t2 naming fuel') (CPS func_name output_type t3 naming fuel')
  
    | tlcase t1 t2 x1 x2 t3 =>
         tlcase t1 (CPS func_name output_type t2 naming fuel') x1 x2 (CPS func_name output_type t3 naming fuel')
  
    | tbcase t1 x1 t2 x2 x3 x4 t3 =>
         tbcase t1 x1 (CPS func_name output_type t2 naming fuel') x2 x3 x4 (CPS func_name output_type t3 naming fuel')
  
    | tlet x1 t1 t2 =>
         tlet x1 (CPS func_name output_type t1 naming fuel') (CPS func_name output_type t2 naming fuel')
  
    | tfix t1 =>
         tfix (CPS func_name output_type t1 naming fuel')
  
    | _ =>
         match find_func func_name func_body with
         | 0 => app k func_body
         | S _ => let continuation_name := append "hole" (nat2string naming) in
                  let (parameterized_func, substituted_func_body) := extract_and_substitute func_name func_body continuation_name in
                    app parameterized_func (abs continuation_name output_type
                      (CPS func_name output_type substituted_func_body (naming + 1) fuel'))
         end
    end
  end.

Definition CPS_conversion (func : tm) : tm :=
  match func with
  | tfix (abs func_name func_type func_body) =>
      let func_output_type := get_output_type func_type in
      let continuation_type := Arrow func_output_type func_output_type in
      let func_new_type := type_insert func_type continuation_type in
      let func_paraed_body := para_insert k continuation_type func_body in
      let func_new_body := CPS func_name func_output_type func_paraed_body 1 999 in
        tfix (abs func_name func_new_type func_new_body)
  | _ => func
  end.

(*verification by examples*)
Module examples.

Definition factorial :=
  tfix (abs f (Arrow Nat Nat)
    (abs n Nat
      (tif0 (var n) (tconst 1)
        (tmult (app (var f) (tminus (var n) (tconst 1))) (var n))))).

Compute (CPS_conversion factorial).

Theorem factorial_correct :
  let exfun := CPS_conversion factorial in
  let input := 5 in
  let output := 120 in
  <{exfun input idNat}> -->* output.
Proof. solve_CPS. Qed.

Definition power_of_four :=
  tfix (abs f (Arrow Nat Nat)
    (abs n Nat
      (tif0 n 1
        (tplus (tplus (app f (tminus n 1)) (app f (tminus n 1))) (tplus (app f (tminus n 1)) (app f (tminus n 1))))))).

Compute (CPS_conversion power_of_four).

Theorem power_of_four_correct :
  let exfun := CPS_conversion power_of_four in
  let input := 2 in
  let output := 16 in
  <{exfun input idNat}> -->* output.
Proof. solve_CPS. Qed.

Definition sum_of_tree :=
  tfix (abs f (Arrow (BinaryTree Nat) Nat)
    (abs t (BinaryTree Nat)
      (tbcase t n n l tl tr
        (tplus (tplus l (app f tl)) (app f tr))))).

Compute (CPS_conversion sum_of_tree).

Theorem sum_of_tree_correct :
  let exfun := CPS_conversion sum_of_tree in
  let input := tnode 2 (tnode 2 (tleaf 1) (tnode 1 (tleaf 3) (tleaf 1))) (tleaf 1) in
  let output := 11 in
  <{exfun input idNat}> -->* output.
Proof. solve_CPS. Qed.

Definition multi_match_simple :=
  tfix (abs f (Arrow (List Nat) Nat)
    (abs l (List Nat)
      (tlcase l 1 x l1
        (tplus 1 (tlcase l1 1 y l2
          (app f l2)))))).

Compute (CPS_conversion multi_match_simple).

End examples.

End initial_version.

Module new_version.

(*
  A new version of CPS conversion which can deal with complicated pattern matching.
*)

(*
Fixpoint find_func (func_name : string) (func_body : tm) : bool :=
  match func_body with
  | var x1 =>
       if eqb x1 func_name then true else false
  | abs x1 _ t1 =>
       if eqb x1 func_name then false else find_func func_name t1
  | app t1 t2 =>
       orb (find_func func_name t1) (find_func func_name t2)
  
  | tconst _ =>
       false
  | tplus t1 t2 =>
       orb (find_func func_name t1) (find_func func_name t2)
  | tminus t1 t2 =>
       orb (find_func func_name t1) (find_func func_name t2)
  | tmult t1 t2 =>
       orb (find_func func_name t1) (find_func func_name t2)
  | tif0 t1 t2 t3 =>
       orb (orb (find_func func_name t1) (find_func func_name t2)) (find_func func_name t3)
  
  | tnil _ =>
       false
  | tcons t1 t2 =>
       orb (find_func func_name t1) (find_func func_name t2)
  | tlcase t1 t2 x1 x2 t3 =>
       orb (orb (find_func func_name t1) (find_func func_name t2)) (if orb (eqb x1 func_name) (eqb x2 func_name) then false else (find_func func_name t3))
  
  | tleaf t1 =>
       find_func func_name t1
  | tnode t1 t2 t3 =>
       orb (orb (find_func func_name t1) (find_func func_name t2)) (find_func func_name t3)
  | tbcase t1 x1 t2 x2 x3 x4 t3 =>
       orb (orb (find_func func_name t1) (if eqb x1 func_name then false else (find_func func_name t2))) (if orb (orb (eqb x2 func_name) (eqb x3 func_name)) (eqb x4 func_name) then false else (find_func func_name t3))
  
  | tlet x1 t1 t2 =>
       if eqb x1 func_name then find_func func_name t1 else orb (find_func func_name t1) (find_func func_name t2)
  
  | tfix t1 =>
       find_func func_name t1
  end.
*)

Fixpoint find_func (func_name : string) (func_body : tm) : nat :=
  match func_body with
  | var x1 =>
       if eqb x1 func_name then 1 else 0
  | abs x1 _ t1 =>
       if eqb x1 func_name then 0 else find_func func_name t1
  | app t1 t2 =>
       (find_func func_name t1) + (find_func func_name t2)
  
  | tconst _ =>
       0
  | tplus t1 t2 =>
       (find_func func_name t1) + (find_func func_name t2)
  | tminus t1 t2 =>
       (find_func func_name t1) + (find_func func_name t2)
  | tmult t1 t2 =>
       (find_func func_name t1) + (find_func func_name t2)
  | tif0 t1 t2 t3 =>
       (find_func func_name t1) + (find_func func_name t2) + (find_func func_name t3)
  
  | tnil _ =>
       0
  | tcons t1 t2 =>
       (find_func func_name t1) + (find_func func_name t2)
  | tlcase t1 t2 x1 x2 t3 =>
       (find_func func_name t1) + (find_func func_name t2) + (if eqb x1 func_name then 0 else if eqb x2 func_name then 0 else find_func func_name t3)
  
  | tleaf t1 =>
       find_func func_name t1
  | tnode t1 t2 t3 =>
       (find_func func_name t1) + (find_func func_name t2) + (find_func func_name t3)
  | tbcase t1 x1 t2 x2 x3 x4 t3 =>
       (find_func func_name t1) + (if eqb x1 func_name then 0 else find_func func_name t2) + (if eqb x2 func_name then 0 else if eqb x3 func_name then 0 else if eqb x4 func_name then 0 else find_func func_name t3)
  
  | tlet x1 t1 t2 =>
       (find_func func_name t1) + (if eqb x1 func_name then 0 else find_func func_name t2)
  
  | tfix t1 =>
       find_func func_name t1
  end.

Fixpoint is_recu (func_name : string) (func_body : tm) :=
  match func_body with
  | var x1 => eqb x1 func_name
  | app t1 t2 => andb (andb (find_func func_name t1 =? 1) (find_func func_name t2 =? 0) ) (is_recu func_name t1)
  | _ => false
  end.

Fixpoint CPS (continuation_name : string) (output_type: ty) (func_name : string) (func_body : tm) (naming : nat) (k : tm -> tm) {struct func_body} : tm :=
  if is_recu func_name func_body then
  let para_name := append "res" (nat2string naming) in
  let result := k (var para_name) in
  app func_body (abs para_name output_type
  match find_func func_name result with
       | O => app (var continuation_name) result
       | S n1 => result
       end)
  else match func_body with
  | var _ =>
       let result := k func_body in
       match find_func func_name result with
       | O => app (var continuation_name) result
       | S n1 => result
       end
  | abs x1 T t1 =>
       abs x1 T (CPS continuation_name output_type func_name t1 naming k) (*TODO*)
  | app t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app (var continuation_name) (k func_body)
       | S n1, O =>
            CPS continuation_name output_type func_name t1 naming (fun res : tm => k (app res t2))
       | O, S n2 =>
            CPS continuation_name output_type func_name t2 naming (fun res : tm => k (app t1 res))
       | S n1, S n2 =>
            CPS continuation_name output_type func_name t1 naming
            (fun res1 : tm => CPS continuation_name output_type func_name t2 (naming + (S n1))
            (fun res2 : tm => k (app res1 res2)))
       end
  
  | tconst n =>
       let result := k func_body in
       match find_func func_name result with
       | O => app (var continuation_name) result
       | S n1 => result
       end
  | tplus t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app (var continuation_name) (k func_body)
       | S n1, O =>
            CPS continuation_name output_type func_name t1 naming (fun res : tm => k (tplus res t2))
       | O, S n2 =>
            CPS continuation_name output_type func_name t2 naming (fun res : tm => k (tplus t1 res))
       | S n1, S n2 =>
            CPS continuation_name output_type func_name t1 naming
            (fun res1 : tm => CPS continuation_name output_type func_name t2 (naming + (S n1))
            (fun res2 : tm => k (tplus res1 res2)))
       end
  | tminus t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app (var continuation_name) (k func_body)
       | S n1, O =>
            CPS continuation_name output_type func_name t1 naming (fun res : tm => k (tminus res t2))
       | O, S n2 =>
            CPS continuation_name output_type func_name t2 naming (fun res : tm => k (tminus t1 res))
       | S n1, S n2 =>
            CPS continuation_name output_type func_name t1 naming
            (fun res1 : tm => CPS continuation_name output_type func_name t2 (naming + (S n1))
            (fun res2 : tm => k (tminus res1 res2)))
       end
  | tmult t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app (var continuation_name) (k func_body)
       | S n1, O =>
            CPS continuation_name output_type func_name t1 naming (fun res : tm => k (tmult res t2))
       | O, S n2 =>
            CPS continuation_name output_type func_name t2 naming (fun res : tm => k (tmult t1 res))
       | S n1, S n2 =>
            CPS continuation_name output_type func_name t1 naming
            (fun res1 : tm => CPS continuation_name output_type func_name t2 (naming + (S n1))
            (fun res2 : tm => k (tmult res1 res2)))
       end
  | tif0 t1 t2 t3 =>
       match find_func func_name t1 with
       | O => tif0 t1 (CPS continuation_name output_type func_name t2 naming k) (CPS continuation_name output_type func_name t3 naming k)
       | S n1 => CPS continuation_name output_type func_name t1 naming (fun res : tm => k (tif0 res t2 t3))
       end
  
  | tnil _ =>
       let result := k func_body in
       match find_func func_name result with
       | O => app (var continuation_name) result
       | S n1 => result
       end
  | tcons t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app (var continuation_name) (k func_body)
       | S n1, O =>
            CPS continuation_name output_type func_name t1 naming (fun res : tm => k (tcons res t2))
       | O, S n2 =>
            CPS continuation_name output_type func_name t2 naming (fun res : tm => k (tcons t1 res))
       | S n1, S n2 =>
            CPS continuation_name output_type func_name t1 naming
            (fun res1 : tm => CPS continuation_name output_type func_name t2 (naming + (S n1))
            (fun res2 : tm => k (tcons res1 res2)))
       end
  | tlcase t1 t2 x1 x2 t3 =>
       match find_func func_name t1 with
       | O => tlcase t1 (CPS continuation_name output_type func_name t2 naming k) x1 x2 (CPS continuation_name output_type func_name t3 naming k)
       | S n1 => CPS continuation_name output_type func_name t1 naming (fun res : tm => k (tlcase res t2 x1 x2 t3))
       end
  
  | tleaf t1 =>
       match find_func func_name t1 with
       | O => app (var continuation_name) (k func_body)
       | S n1 => CPS continuation_name output_type func_name t1 naming (fun res : tm => k (tleaf res))
       end
  | tnode t1 t2 t3 =>
       match find_func func_name t1, find_func func_name t2, find_func func_name t3 with
       | O, O, O =>
            app (var continuation_name) (k func_body)
       | S n1, O, O =>
            CPS continuation_name output_type func_name t1 naming (fun res : tm => k (tnode res t2 t3))
       | O, S n2, O =>
            CPS continuation_name output_type func_name t2 naming (fun res : tm => k (tnode t1 res t3))
       | O, O, S n3 =>
            CPS continuation_name output_type func_name t3 naming (fun res : tm => k (tnode t1 t2 res))
       | S n1, S n2, O =>
            CPS continuation_name output_type func_name t1 naming
            (fun res1 : tm => CPS continuation_name output_type func_name t2 (naming + (S n1))
            (fun res2 : tm => k (tnode res1 res2 t3)))
       | S n1, O, S n3 =>
            CPS continuation_name output_type func_name t1 naming
            (fun res1 : tm => CPS continuation_name output_type func_name t3 (naming + (S n1))
            (fun res2 : tm => k (tnode res1 t2 res2)))
       | O, S n2, S n3 =>
            CPS continuation_name output_type func_name t2 naming
            (fun res1 : tm => CPS continuation_name output_type func_name t3 (naming + (S n2))
            (fun res2 : tm => k (tnode t1 res1 res2)))
       | S n1, S n2, S n3 =>
            CPS continuation_name output_type func_name t1 naming
            (fun res1 : tm => CPS continuation_name output_type func_name t2 (naming + (S n1))
            (fun res2 : tm => CPS continuation_name output_type func_name t3 (naming + (S n1)+ (S n2))
            (fun res3 : tm => k (tnode res1 res2 res3))))
       end
  | tbcase t1 x1 t2 x2 x3 x4 t3 =>
       match find_func func_name t1 with
       | O => tbcase t1 x1 (CPS continuation_name output_type func_name t2 naming k) x2 x3 x4 (CPS continuation_name output_type func_name t3 naming k)
       | S n1 => CPS continuation_name output_type func_name t1 naming (fun res : tm => k (tbcase res x1 t2 x2 x3 x4 t3))
       end
  
  | tlet x1 t1 t2 =>
       tlet x1 (CPS continuation_name output_type func_name t1 naming k) (CPS continuation_name output_type func_name t2 naming k)
  
  | tfix t1 =>
       tfix (CPS continuation_name output_type func_name t1 naming k)
  end.

Definition CPS_conversion (func : tm) : tm :=
  match func with
  | tfix (abs func_name func_type func_body) =>
       let output_type := get_output_type func_type in
       let continuation_name := k in
       let continuation_type := Arrow output_type output_type in
       let func_new_type := type_insert func_type continuation_type in
       let func_paraed_body := para_insert continuation_name continuation_type func_body in
       tfix (abs func_name func_new_type (CPS continuation_name output_type func_name func_paraed_body 1 (fun res : tm => res)))
  | _ => func
  end.

(*verification by examples*)

Module examples.

Definition match_case1 :=
  tfix (abs f (Arrow (List Nat) Nat)
    (abs l (List Nat)
      (tlcase l 0 n1 l1
        (tlcase l1 n1 n2 l2
          (tplus n1 (tplus n2 (app f l2))))))).

Compute (CPS_conversion match_case1).

Definition match_case1_CPS :=
  tfix (abs f (Arrow (List Nat) (Arrow (Arrow Nat Nat) Nat))
    (abs l (List Nat)
      (abs k (Arrow Nat Nat)
        (tlcase l (app k 0) n1 l1
          (tlcase l1 (app k n1) n2 l2
            (app (app f l2) (abs res Nat (app k (tplus n1 (tplus n2 res)))))))))).

Theorem case1_correct :
  let origin_fun := match_case1 in
  let CPS_fun := CPS_conversion match_case1 in
  let input := tcons 4 (tcons 3 (tcons 1 (tcons 2 (tnil Nat)))) in
  let output := 10 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. unfold match_case1. simpl. split. normalize. normalize. Qed.

Definition match_case2 :=
  tfix (abs f (Arrow (List Nat) Nat)
    (abs l (List Nat)
      (tplus 1 (tlcase l 0 n1 l1
        (tplus n1 (app f l1)))))).

Compute (CPS_conversion match_case2).

Definition match_case2_CPS :=
  tfix (abs f (Arrow (List Nat) (Arrow (Arrow Nat Nat) Nat))
    (abs l (List Nat)
      (abs k (Arrow Nat Nat)
        (tlcase l (app k (tplus 1 0)) n1 l1
          (app (app f l1) (abs res Nat (app k (tplus (tplus 1 n1) res)))))))).

Theorem case2_correct :
  let origin_fun := match_case2 in
  let CPS_fun := CPS_conversion match_case2 in
  let input := tcons 4 (tcons 3 (tcons 1 (tcons 2 (tnil Nat)))) in
  let output := 15 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. unfold match_case2. simpl. split. normalize. normalize. Qed.

Definition match_case3 :=
  tfix (abs f (Arrow (List Nat) Nat)
    (abs l (List Nat)
      (tlcase l 0 n1 l1
        (tif0 (app f l1) n1 (tmult 2 n1))))).

Compute (CPS_conversion match_case3).

Definition match_case3_CPS :=
  tfix (abs f (Arrow (List Nat) (Arrow (Arrow Nat Nat) Nat))
    (abs l (List Nat)
      (abs k (Arrow Nat Nat)
        (tlcase l (app k 0) n1 l1
          (app (app f l1) (abs res Nat (app k (tif0 res n1 (tmult 2 n1))))))))).

Theorem case3_correct :
  let origin_fun := match_case3 in
  let CPS_fun := CPS_conversion match_case3 in
  let input := tcons 2 (tcons 2 (tnil Nat)) in
  let output := 4 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. unfold match_case3. simpl. split. normalize. normalize. Qed.

Definition match_case4 :=
  tfix (abs f (Arrow (List Nat) (Arrow (List Nat) Nat))
    (abs l1 (List Nat)
       (abs l2 (List Nat)
         (tplus (tlcase l1 0 n1 l'
           (tplus n1 (app (app f l') l2)))
             (tlcase l2 0 n2 l''
               (tplus n2 (app (app f l1) l''))))))).

Compute (CPS_conversion match_case4).

Definition match_case4_CPS :=
  tfix (abs f (Arrow (Arrow (List Nat) (List Nat)) (Arrow (Arrow Nat Nat) Nat))
    (abs l1 (List Nat)
      (abs l2 (List Nat)
        (abs k (Arrow Nat Nat)
          (tlcase l2 (tlcase l1 (app k (tplus 0 0)) n1 l'
            (app (app (app f l') l2) (abs res Nat (app k (tplus (tplus n1 res) 0))))) n2 l''
              (tlcase l1 (app (app (app f l1) l'') (abs res Nat (app k (tplus (tplus 0 n2) res)))) n1 l'
                (app (app (app f l') l2) (abs res1 Nat (app (app (app f l1) l'') (abs res2 Nat
                  (app k (tplus (tplus n1 res1) (tplus n2 res2))))))))))))).

Theorem case4_correct :
  let origin_fun := match_case4 in
  let CPS_fun := CPS_conversion match_case4 in
  let input1 := tcons 2 (tcons 3 (tcons 5 (tnil Nat))) in
  let input2 := tcons 4 (tcons 2 (tnil Nat)) in
  let output := 110 in
  (<{origin_fun input1 input2}> -->* output) /\ (<{CPS_fun input1 input2 idNat}> -->* output).
Proof. unfold match_case4. simpl. split. normalize. normalize. Qed.

Definition match_case5 :=
  tfix (abs f (Arrow (List Nat) Nat)
    (abs l (List Nat)
      (tplus 3 (tmult (tlcase l (tminus 2 1) n1 l'
        (tplus n1 (tplus 1 (tplus (app f l') 1)))) 5)))).

Compute (CPS_conversion match_case5).

Theorem case5_correct :
  let origin_fun := match_case5 in
  let CPS_fun := CPS_conversion match_case5 in
  let input := tcons 2 (tcons 3 (tcons 5 (tnil Nat))) in
  let output := 2113 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. unfold match_case5. simpl. split. normalize. normalize. Qed.

Definition factorial :=
  tfix (abs f (Arrow Nat Nat)
    (abs n Nat
      (tif0 (var n) (tconst 1)
        (tmult (app (var f) (tminus (var n) (tconst 1))) (var n))))).

Compute (CPS_conversion factorial).

Theorem factorial_correct :
  let exfun := CPS_conversion factorial in
  let input := 5 in
  let output := 120 in
  <{exfun input idNat}> -->* output.
Proof. solve_CPS. Qed.

Definition power_of_four :=
  tfix (abs f (Arrow Nat Nat)
    (abs n Nat
      (tif0 n 1
        (tplus (tplus (app f (tminus n 1)) (app f (tminus n 1))) (tplus (app f (tminus n 1)) (app f (tminus n 1))))))).

Compute (CPS_conversion power_of_four).

Theorem power_of_four_correct :
  let exfun := CPS_conversion power_of_four in
  let input := 2 in
  let output := 16 in
  <{exfun input idNat}> -->* output.
Proof. solve_CPS. Qed.

Definition sum_of_tree :=
  tfix (abs f (Arrow (BinaryTree Nat) Nat)
    (abs t (BinaryTree Nat)
      (tbcase t n n l tl tr
        (tplus (tplus l (app f tl)) (app f tr))))).

Compute (CPS_conversion sum_of_tree).

Theorem sum_of_tree_correct :
  let exfun := CPS_conversion sum_of_tree in
  let input := tnode 2 (tnode 2 (tleaf 1) (tnode 1 (tleaf 3) (tleaf 1))) (tleaf 1) in
  let output := 11 in
  <{exfun input idNat}> -->* output.
Proof. solve_CPS. Qed.

End examples.

End new_version.
