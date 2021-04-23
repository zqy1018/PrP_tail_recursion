From Coq Require Export Strings.String.
From Coq Require Export Arith.PeanoNat.
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
Definition F : string := "F".
Definition f : string := "f".
Definition f' : string := "f'".
Definition g : string := "g".
Definition g' : string := "g'".
Definition h : string := "h".
Definition h' : string := "h'".
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
Definition count : string := "count".
Definition count' : string := "count'".

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
Hint Unfold F : core.
Hint Unfold f : core.
Hint Unfold f' : core.
Hint Unfold g : core.
Hint Unfold g' : core.
Hint Unfold h : core.
Hint Unfold h' : core.
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
Hint Unfold count : core.
Hint Unfold count' : core.

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

Tactic Notation "solve_CPS" := cbv in *; simpl; normalize.

Hint Extern 2 (has_type _ (app _ _) _) =>
  eapply T_App; auto : core.
Hint Extern 2 (has_type _ (tlcase _ _ _ _ _) _) =>
  eapply T_LCase; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.
(*using the tactic [normalize] to prove multistep relations*)
(*using the tactic [eauto n : nat] to prove type-related propositions*)