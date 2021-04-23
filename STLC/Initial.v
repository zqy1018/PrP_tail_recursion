From STLC Require Export Definitions.

(*examples*)
Definition stlc_add :=
  abs x Nat (abs y Nat (tplus x y)).

Definition stlc_square :=
  abs x Nat (tmult x x).

Definition stlc_do_it_three_times :=
  abs F (Arrow Nat Nat)
    (abs x Nat
      (app F (app F (app F x)))).

Definition stlc_power_of_four :=
  tfix (abs F (Arrow Nat Nat)
    (abs n Nat
      (tif0 n 1
        (tplus (tplus (app F (tminus n 1)) (app F (tminus n 1))) (tplus (app F (tminus n 1)) (app F (tminus n 1))))))).

Definition stlc_factorial :=
  tfix (abs F (Arrow Nat Nat)
    (abs x Nat
      (tif0 x 1 (tmult x (app F (tminus x 1)))))).

Definition stlc_sum_of_list :=
  tfix (abs F (Arrow (List Nat) Nat)
    (abs l (List Nat)
      (tlcase l 0 n' l' (tplus n' (app F l'))))).

Definition stlc_repeat :=
  tfix (abs F (Arrow Nat (Arrow Nat (List Nat)))
    (abs count Nat
      (abs n Nat
        (tif0 count (tnil Nat) (tcons n (app (app F (tminus count 1)) n)))))).

Definition stlc_app :=
  tfix (abs F (Arrow (List Nat) (List Nat))
    (abs l1 (List Nat)
      (abs l2 (List Nat)
        (tlcase l1 l2 n' l1'
          (tcons n' (app (app F l1') l2)))))).

Definition stlc_reverse :=
  tfix (abs F (Arrow (List Nat) (List Nat))
    (abs l (List Nat)
      (tlcase l (tnil Nat) n' l'
        (app (app stlc_app (app F l')) (tcons n' (tnil Nat)))))).

Definition stlc_length :=
  tfix (abs F (Arrow (List Nat) Nat)
    (abs l (List Nat)
      (tlcase l 0 n' l'
        (tplus 1 (app F l'))))).

Definition stlc_map :=
  tfix (abs F (Arrow (Arrow Nat Nat) (Arrow (List Nat) (List Nat)))
    (abs f (Arrow Nat Nat)
      (abs l (List Nat)
        (tlcase l (tnil Nat) n' l'
          (tcons (app f n') (app (app F f) l')))))).

Definition stlc_fold :=
  tfix (abs F (Arrow (Arrow Nat (Arrow Nat Nat)) (Arrow (List Nat) (Arrow Nat Nat)))
    (abs f (Arrow Nat (Arrow Nat Nat))
      (abs l (List Nat)
        (abs b Nat
          (tlcase l b n' l'
            (app (app f n') (app (app (app F f) l') b))))))).

Definition stlc_sum_of_tree :=
  tfix (abs F (Arrow (BinaryTree Nat) Nat)
    (abs t (BinaryTree Nat)
      (tbcase t n n l tl tr
        (tplus (tplus l (app F tl)) (app F tr))))).

Theorem example_stlc_add :
  let exfun := stlc_add in
  let input1 := 5 in
  let input2 := 95 in
  let output := 100 in
  <{exfun input1 input2}> -->* output.
Proof. solve_CPS. Qed.

Theorem example_stlc_square :
  let exfun := stlc_square in
  let input := 5 in
  let output := 25 in
  <{exfun input}> -->* output.
Proof. solve_CPS. Qed.

Theorem example_stlc_do_it_three_times :
  let exfun := stlc_do_it_three_times in
  let input1 := stlc_square in
  let input2 := 2 in
  let output := 256 in
  <{exfun input1 input2}> -->* output.
Proof. solve_CPS. Qed.

Theorem example_stlc_power_of_four :
  let exfun := stlc_power_of_four in
  let input := 2 in
  let output := 16 in
  <{exfun input}> -->* output.
Proof. solve_CPS. Qed.

Theorem example_stlc_factorial :
  let exfun := stlc_factorial in
  let input := 6 in
  let output := 720 in
  <{exfun input}> -->* output.
Proof. solve_CPS. Qed.

Theorem example_stlc_sum_of_list :
  let exfun := stlc_sum_of_list in
  let input := tcons 4 (tcons 1 (tcons 10 (tcons 2 (tnil Nat)))) in
  let output := 17 in
  <{exfun input}> -->* output.
Proof. solve_CPS. Qed.

Theorem example_stlc_repeat :
  let exfun := stlc_repeat in
  let input1 := 5 in
  let input2 := 12 in
  let output := tcons 12 (tcons 12 (tcons 12 (tcons 12 (tcons 12 (tnil Nat))))) in
  <{exfun input1 input2}> -->* output.
Proof. solve_CPS. Qed.

Theorem example_stlc_app :
  let exfun := stlc_app in
  let input1 := tcons 10 (tcons 2 (tnil Nat)) in
  let input2 := tcons 5 (tcons 0 (tcons 8 (tnil Nat))) in
  let output := tcons 10 (tcons 2 (tcons 5 (tcons 0 (tcons 8 (tnil Nat))))) in
  <{exfun input1 input2}> -->* output.
Proof. solve_CPS. Qed.

Theorem example_stlc_reverse :
  let exfun := stlc_reverse in
  let input := tcons 1 (tcons 2 (tcons 3 (tcons 4 (tnil Nat)))) in
  let output := tcons 4 (tcons 3 (tcons 2 (tcons 1 (tnil Nat)))) in
  <{exfun input}> -->* output.
Proof. solve_CPS. Qed.

Theorem example_stlc_length :
  let exfun := stlc_length in
  let input := tcons 0 (tcons 2 (tcons 3 (tcons 0 (tcons 8 (tnil Nat))))) in
  let output := 5 in
  <{exfun input}> -->* output.
Proof. solve_CPS. Qed.

Theorem example_stlc_map :
  let exfun := stlc_map in
  let input1 := stlc_square in
  let input2 := tcons 4 (tcons 10 (tcons 0 (tnil Nat))) in
  let output := tcons 16 (tcons 100 (tcons 0 (tnil Nat))) in
  <{exfun input1 input2}> -->* output.
Proof. solve_CPS. Qed.

Theorem example_stlc_fold :
  let exfun := stlc_fold in
  let input1 := stlc_add in
  let input2 := tcons 1 (tcons 2 (tcons 3 (tcons 4 (tcons 5 (tnil Nat))))) in
  let input3 := 0 in
  let output := 15 in
  <{exfun input1 input2 input3}> -->* output.
Proof. solve_CPS. Qed.

Theorem example_stlc_sum_of_tree :
  let exfun := stlc_sum_of_tree in
  let input := tnode 3 (tleaf 10) (tnode 5 (tnode 2 (tleaf 1) (tleaf 2)) (tleaf 3)) in
  let output := 26 in
  <{exfun input}> -->* output.
Proof. solve_CPS. Qed.

(*CPS conversion rule*)
(*
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

Fixpoint is_recu (func_name : string) (func_body : tm) :=
  match func_body with
  | var x1 => eqb x1 func_name
  | app t1 t2 => andb (andb (find_func func_name t1 =? 1) (find_func func_name t2 =? 0) ) (is_recu func_name t1)
  | _ => false
  end.

Module initial_version.

(*
  An initial version of CPS conversion which can not deal with complicated
  pattern matching and requires a parameter [fuel] to get accepted by Coq.
*)

Fixpoint extract_and_substitute (func_name : string) (func_body : tm) (substitution : string) : tm * tm :=
  if is_recu func_name func_body
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
         | S _ => let continuation_name := append "res" (nat2string naming) in
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

Print stlc_factorial.
Compute (CPS_conversion stlc_factorial).

Theorem stlc_factorial_correct :
  let exfun := CPS_conversion stlc_factorial in
  let input := 5 in
  let output := 120 in
  <{exfun input idNat}> -->* output.
Proof. solve_CPS. Qed.

Print stlc_power_of_four.
Compute (CPS_conversion stlc_power_of_four).

Theorem stlc_power_of_four_correct :
  let exfun := CPS_conversion stlc_power_of_four in
  let input := 2 in
  let output := 16 in
  <{exfun input idNat}> -->* output.
Proof. solve_CPS. Qed.

Print stlc_sum_of_tree.
Compute (CPS_conversion stlc_sum_of_tree).

Theorem stlc_sum_of_tree_correct :
  let exfun := CPS_conversion stlc_sum_of_tree in
  let input := tnode 2 (tnode 2 (tleaf 1) (tnode 1 (tleaf 3) (tleaf 1))) (tleaf 1) in
  let output := 11 in
  <{exfun input idNat}> -->* output.
Proof. solve_CPS. Qed.

End examples.

End initial_version.
