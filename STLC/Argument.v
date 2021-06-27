From STLC Require Export PatternMatch.

(*
  Now we deal with those CPS conversions when the recursive function
  itself appears in the arguments or in the body of a recursive function.
*)

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

Fixpoint depth (func_name : string) (func_body : tm) : nat :=
  match func_body with
  | var _ =>
       1
  | abs _ t1 =>
       1 + depth func_name t1
  | app t1 t2 =>
       if is_recu func_name func_body then 1
       else match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            1
       | S n1, O =>
            1 + depth func_name t1
       | O, S n2 =>
            1 + depth func_name t2
       | S n1, S n2 =>
            1 + Coq.Arith.PeanoNat.Nat.max (depth func_name t2) (1 + depth func_name t1)
       end
  
  | tconst _ =>
       1
  | tplus t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            1
       | S n1, O =>
            1 + depth func_name t1
       | O, S n2 =>
            1 + depth func_name t2
       | S n1, S n2 =>
            1 + Coq.Arith.PeanoNat.Nat.max (depth func_name t1) (depth func_name t2)
       end
  | tminus t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            1
       | S n1, O =>
            1 + depth func_name t1
       | O, S n2 =>
            1 + depth func_name t2
       | S n1, S n2 =>
            1 + Coq.Arith.PeanoNat.Nat.max (depth func_name t1) (depth func_name t2)
       end
  | tmult t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            1
       | S n1, O =>
            1 + depth func_name t1
       | O, S n2 =>
            1 + depth func_name t2
       | S n1, S n2 =>
            1 + Coq.Arith.PeanoNat.Nat.max (depth func_name t1) (depth func_name t2)
       end
  | tif0 t1 t2 t3 =>
       match find_func func_name t1 with
       | O =>
            1 + Coq.Arith.PeanoNat.Nat.max (depth func_name t2) (depth func_name t3)
       | S n1 =>
            1 + Coq.Arith.PeanoNat.Nat.max (depth func_name t1) (Coq.Arith.PeanoNat.Nat.max (depth func_name t2) (depth func_name t3))
       end
  
  | tnil =>
       1
  | tcons t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            1
       | S n1, O =>
            1 + depth func_name t1
       | O, S n2 =>
            1 + depth func_name t2
       | S n1, S n2 =>
            1 + Coq.Arith.PeanoNat.Nat.max (depth func_name t1) (depth func_name t2)
       end
  | tlcase t1 t2 x1 x2 t3 =>
       match find_func func_name t1 with
       | O =>
            1 + Coq.Arith.PeanoNat.Nat.max (depth func_name t2) (depth func_name t3)
       | S n1 =>
            1 + Coq.Arith.PeanoNat.Nat.max (depth func_name t1) (Coq.Arith.PeanoNat.Nat.max (depth func_name t2) (depth func_name t3))
       end
  
  | tlet _ t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            1
       | S n1, O =>
            1 + depth func_name t1
       | O, S n2 =>
            1 + depth func_name t2
       | S n1, S n2 =>
            1 + Coq.Arith.PeanoNat.Nat.max (depth func_name t1) (depth func_name t2)
       end
  
  | tfix t1 =>
       1 + depth func_name t1
  end.

Fixpoint exact_and_subst_arg (func_name : string) (func_body : tm) (naming : nat) : tm * tm :=
  match func_body with
  | app t1 t2 =>
       if is_recu func_name func_body then (func_body, var (append "res" (nat2string naming)))
       else if is_app_F func_name func_body
       then match find_func func_name t1 - 1 with
            | 0 =>
                 match find_func func_name t2 with
                 | 0 =>
                      (var "invalid", var "invalid")
                 | S _ =>
                      let (para1, para2) := exact_and_subst_arg func_name t2 naming in
                      (para1, app t1 para2)
                 end
            | S _ =>
                 let (para1, para2) := exact_and_subst_arg func_name t1 naming in
                 (para1, app para2 t2)
            end
       else match find_func func_name t1 with
            | 0 =>
                 match find_func func_name t2 with
                 | 0 =>
                      (var "invalid", var "invalid")
                 | S _ =>
                      let (para1, para2) := exact_and_subst_arg func_name t2 naming in
                      (para1, app t1 para2)
                 end
            | S _ =>
                 let (para1, para2) := exact_and_subst_arg func_name t1 naming in
                 (para1, app para2 t2)
            end
  
  | tplus t1 t2 =>
       match find_func func_name t1 with
       | 0 =>
            match find_func func_name t2 with
            | 0 =>
                 (var "invalid", var "invalid")
            | S _ =>
                 let (para1, para2) := exact_and_subst_arg func_name t2 naming in
                 (para1, tplus t1 para2)
            end
       | S _ =>
            let (para1, para2) := exact_and_subst_arg func_name t1 naming in
            (para1, tplus para2 t2)
       end
  
  | tminus t1 t2 =>
       match find_func func_name t1 with
       | 0 =>
            match find_func func_name t2 with
            | 0 =>
                 (var "invalid", var "invalid")
            | S _ =>
                 let (para1, para2) := exact_and_subst_arg func_name t2 naming in
                 (para1, tminus t1 para2)
            end
       | S _ =>
            let (para1, para2) := exact_and_subst_arg func_name t1 naming in
            (para1, tminus para2 t2)
       end
  
  | tmult t1 t2 =>
       match find_func func_name t1 with
       | 0 =>
            match find_func func_name t2 with
            | 0 =>
                 (var "invalid", var "invalid")
            | S _ =>
                 let (para1, para2) := exact_and_subst_arg func_name t2 naming in
                 (para1, tmult t1 para2)
            end
       | S _ =>
            let (para1, para2) := exact_and_subst_arg func_name t1 naming in
            (para1, tmult para2 t2)
       end
  
  | tif0 t1 t2 t3 =>
       match find_func func_name t1 with
       | 0 =>
            match find_func func_name t2 with
            | 0 =>
                 match find_func func_name t3 with
                 | 0 =>
                      (var "invalid", var "invalid")
                 | S _ =>
                      let (para1, para2) := exact_and_subst_arg func_name t3 naming in
                      (para1, tif0 t1 t2 para2)
                 end
            | S _ =>
                 let (para1, para2) := exact_and_subst_arg func_name t2 naming in
                 (para1, tif0 t1 para2 t3)
            end
       | S _ =>
            let (para1, para2) := exact_and_subst_arg func_name t1 naming in
            (para1, tif0 para2 t2 t3)
       end
  
  | tcons t1 t2 =>
       match find_func func_name t1 with
       | 0 =>
            match find_func func_name t2 with
            | 0 => (var "invalid", var "invalid")
            | S _ =>
                 let (para1, para2) := exact_and_subst_arg func_name t2 naming in
                 (para1, tcons t1 para2)
            end
       | S _ =>
            let (para1, para2) := exact_and_subst_arg func_name t1 naming in
            (para1, tcons para2 t2)
       end
  
  | tlcase t1 t2 x1 x2 t3 =>
       match find_func func_name t1 with
       | 0 =>
            match find_func func_name t2 with
            | 0 =>
                 match find_func func_name t3 with
                 | 0 =>
                      (var "invalid", var "invalid")
                 | S _ =>
                      let (para1, para2) := exact_and_subst_arg func_name t3 naming in
                      (para1, tlcase t1 t2 x1 x2 para2)
                 end
            | S _ =>
                 let (para1, para2) := exact_and_subst_arg func_name t2 naming in
                 (para1, tlcase t1 para2 x1 x2 t3)
            end
       | S _ =>
            let (para1, para2) := exact_and_subst_arg func_name t1 naming in
            (para1, tlcase para2 t2 x1 x2 t3)
       end
  | _ =>
       (var "invalid", var "invalid")
  end.

Fixpoint CPS_app_F (k : tm) (func_name : string) (func_body : tm) (continuation1 continuation2 : tm -> tm) (naming : nat) (fuel : nat) : tm :=
match fuel with | 0 => func_body | S fuel' =>
  let continuation_name := (append "res" (nat2string naming)) in
  match find_func func_name func_body - 1 with
  | 0 =>
       let result := continuation1 continuation_name in
       match find_func func_name result with
       | 0 =>
            continuation2 (app func_body (abs continuation_name (app k result)))
       | S _ =>
            continuation2 (app func_body (abs continuation_name result))
       end
  | S _ =>
       let (arg, new_body) := exact_and_subst_arg func_name func_body naming in
       let new_continuation := fun res => continuation2 (app arg (abs continuation_name res)) in
       CPS_app_F k func_name new_body continuation1 new_continuation (naming + 1) fuel'
  end
end.

Fixpoint CPS (k : tm) (func_name : string) (func_body : tm) (continuation : tm -> tm) (naming : nat) : tm :=
  match func_body with
  | var _ =>
       let result := continuation func_body in
       match find_func func_name result with
       | O => app k result
       | S n1 => result
       end
  | abs x1 t1 =>
       abs x1 (CPS k func_name t1 continuation naming)
  | app t1 t2 =>
       if is_app_F func_name func_body
       then CPS_app_F k func_name func_body continuation (fun res : tm => res) naming 999
       else match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app k (continuation func_body)
       | S n1, O =>
            CPS k func_name t1 (fun res : tm => continuation (app res t2)) naming
       | O, S n2 =>
            CPS k func_name t2 (fun res : tm => continuation (app t1 res)) naming
       | S n1, S n2 =>
            CPS k func_name t1
            (fun res1 : tm => CPS k func_name t2
            (fun res2 : tm => continuation (app res1 res2)) (naming + (S n1))) naming
       end
  
  | tconst n =>
       let result := continuation func_body in
       match find_func func_name result with
       | O => app k result
       | S n1 => result
       end
  | tplus t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app k (continuation func_body)
       | S n1, O =>
            CPS k func_name t1 (fun res : tm => continuation (tplus res t2)) naming
       | O, S n2 =>
            CPS k func_name t2 (fun res : tm => continuation (tplus t1 res)) naming
       | S n1, S n2 =>
            CPS k func_name t1
            (fun res1 : tm => CPS k func_name t2
            (fun res2 : tm => continuation (tplus res1 res2)) (naming + (S n1))) naming
       end
  | tminus t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app k (continuation func_body)
       | S n1, O =>
            CPS k func_name t1 (fun res : tm => continuation (tminus res t2)) naming
       | O, S n2 =>
            CPS k func_name t2 (fun res : tm => continuation (tminus t1 res)) naming
       | S n1, S n2 =>
            CPS k func_name t1
            (fun res1 : tm => CPS k func_name t2
            (fun res2 : tm => continuation (tminus res1 res2)) (naming + (S n1))) naming
       end
  | tmult t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app k (continuation func_body)
       | S n1, O =>
            CPS k func_name t1 (fun res : tm => continuation (tmult res t2)) naming
       | O, S n2 =>
            CPS k func_name t2 (fun res : tm => continuation (tmult t1 res)) naming
       | S n1, S n2 =>
            CPS k func_name t1
            (fun res1 : tm => CPS k func_name t2
            (fun res2 : tm => continuation (tmult res1 res2)) (naming + (S n1))) naming
       end
  | tif0 t1 t2 t3 =>
       match find_func func_name t1 with
       | O =>
            tif0 t1 (CPS k func_name t2 continuation naming) (CPS k func_name t3 continuation naming)
       | S n1 =>
            CPS (abs res res) func_name t1 (fun res : tm => tif0 res
            (CPS k func_name t2 continuation (naming + (S n1)))
            (CPS k func_name t3 continuation (naming + (S n1)))) naming
       end
  
  | tnil =>
       let result := continuation func_body in
       match find_func func_name result with
       | O => app k result
       | S n1 => result
       end
  | tcons t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app k (continuation func_body)
       | S n1, O =>
            CPS k func_name t1 (fun res : tm => continuation (tcons res t2)) naming
       | O, S n2 =>
            CPS k func_name t2 (fun res : tm => continuation (tcons t1 res)) naming
       | S n1, S n2 =>
            CPS k func_name t1
            (fun res1 : tm => CPS k func_name t2
            (fun res2 : tm => continuation (tcons res1 res2)) (naming + (S n1))) naming
       end
  | tlcase t1 t2 x1 x2 t3 =>
       match find_func func_name t1 with
       | O =>
            tlcase t1 (CPS k func_name t2 continuation naming) x1 x2 (CPS k func_name t3 continuation naming)
       | S n1 =>
            CPS (abs res res) func_name t1 (fun res : tm => tlcase res
            (CPS k func_name t2 continuation (naming + (S n1))) x1 x2
            (CPS k func_name t3 continuation (naming + (S n1)))) naming
       end
  
  | tlet x1 t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app k (continuation func_body)
       | S n1, O =>
            CPS (abs res res) func_name t1 (fun res : tm => continuation (tlet x1 res (app k t2))) naming
       | O, S n2 =>
            CPS k func_name t2 (fun res : tm => continuation (tlet x1 t1 res)) naming
       | S n1, S n2 =>
              CPS (abs res res) func_name t1
              (fun res1 : tm => CPS k func_name t2
              (fun res2 : tm => continuation (tlet x1 res1 res2)) (naming + (S n1))) naming
       end
  
  | tfix t1 =>
       tfix (CPS k func_name t1 continuation naming)
  end.

Definition CPS_conversion (func : tm) : tm :=
  match func with
  | tfix (abs func_name func_body) =>
       let func_paraed_body := para_insert k func_body in
       tfix (abs func_name (CPS k func_name func_paraed_body (fun res : tm => res) 1))
  | _ => func
  end.

Module examples.

Definition stlc_match_case1 :=
  tfix (abs F
    (abs l
      (tlcase l 0 n1 l1
        (tlcase l1 n1 n2 l2
          (tplus n1 (tplus n2 (app F l2))))))).

Compute (CPS_conversion stlc_match_case1).

Theorem stlc_match_case1_correct :
  let origin_fun := stlc_match_case1 in
  let CPS_fun := CPS_conversion stlc_match_case1 in
  let input := tcons 4 (tcons 3 (tcons 1 (tcons 2 tnil))) in
  let output := 10 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

Definition stlc_match_case2 :=
  tfix (abs F
    (abs l
      (tplus 1 (tlcase l 0 n1 l1
        (tplus n1 (app F l1)))))).

Compute (CPS_conversion stlc_match_case2).

Theorem stlc_match_case2_correct :
  let origin_fun := stlc_match_case2 in
  let CPS_fun := CPS_conversion stlc_match_case2 in
  let input := tcons 4 (tcons 3 (tcons 1 (tcons 2 tnil))) in
  let output := 15 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

Definition stlc_match_case3 :=
  tfix (abs F
    (abs l
      (tlcase l 0 n1 l1
        (tif0 (app F l1) n1 (tmult 2 n1))))).

Compute (CPS_conversion stlc_match_case3).

Theorem stlc_match_case3_correct :
  let origin_fun := stlc_match_case3 in
  let CPS_fun := CPS_conversion stlc_match_case3 in
  let input := tcons 2 (tcons 2 tnil) in
  let output := 4 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

Definition stlc_match_case4 :=
  tfix (abs F
    (abs l1
       (abs l2
         (tplus (tlcase l1 0 n1 l'
           (tplus n1 (app (app F l') l2)))
             (tlcase l2 0 n2 l''
               (tplus n2 (app (app F l1) l''))))))).

Compute (CPS_conversion stlc_match_case4).

Theorem stlc_match_case4_correct :
  let origin_fun := stlc_match_case4 in
  let CPS_fun := CPS_conversion stlc_match_case4 in
  let input1 := tcons 2 (tcons 3 (tcons 5 tnil)) in
  let input2 := tcons 4 (tcons 2 tnil) in
  let output := 110 in
  (<{origin_fun input1 input2}> -->* output) /\ (<{CPS_fun input1 input2 idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

Definition stlc_match_case5 :=
  tfix (abs F
    (abs l
      (tplus 3 (tmult (tlcase l (tminus 2 1) n1 l'
        (tplus n1 (tplus 1 (tplus (app F l') 1)))) 5)))).

Compute (CPS_conversion stlc_match_case5).

Theorem stlc_match_case5_correct :
  let origin_fun := stlc_match_case5 in
  let CPS_fun := CPS_conversion stlc_match_case5 in
  let input := tcons 2 (tcons 3 (tcons 5 tnil)) in
  let output := 2113 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

(*
  F n1 n2 :=
    match n1 with
    | 0 => match n2 with
           | 0 => 0
           | S n2' => F 0 n2'
           end
    | S n1' => 1 + F n1' (F n1' n2 - 2)
    end.
  We can transfer it to CPS-style by hand:
  F n1 n2 k :=
    match n1 with
    | 0 => match n2 with
           | 0 => k 0
           | S n2' => F 0 n2' (fun res1 => k res1)
           end
    | S n1' => F n1' n2 (fun res1 => F n1' (res1 - 2) (fun res2 => k (1 + res2)))
    end.
*)

Definition stlc_argument_case1 :=
  tfix (abs F
    (abs n1
      (abs n2
        (tif0 n1 (tif0 n2 0 (app (app F 0) (tminus n2 1)))
          (tplus 1 (app (app F (tminus n1 1)) (tminus (app (app F (tminus n1 1)) n2) 2))))))).

Compute (CPS_conversion stlc_argument_case1).

Definition stlc_argument_case1_CPS :=
  tfix (abs F
    (abs n1 (abs n2
      (abs k
        (tif0 n1 (tif0 n2 (app k 0) (app (app (app F 0) (tminus n2 1))
          (abs res1 (app k res1))))
            (app (app (app F (tminus n1 1)) n2) (abs res1
              (app (app (app F (tminus n1 1)) (tminus res1 2)) (abs res2
                (app k (tplus 1 res2))))))))))).

Theorem stlc_argument_case1_correct :
  let origin_fun := stlc_argument_case1 in
  let CPS_fun := CPS_conversion stlc_argument_case1 in
  let input1 := 3 in
  let input2 := 3 in
  let output := 3 in
  (<{origin_fun input1 input2}> -->* output) /\ (<{CPS_fun input1 input2 idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

(*
  F n :=
    match n with
    | 0 => 0
    | S n' => 1 + F (F (F n'))
    end.
  We can transfer it to CPS-style by hand:
  F n k :=
    match n with
    | 0 => k 0
    | S n' => F n' (fun res1 => F res1 (fun res2 => F res2 (fun res3 => k (1 + res3))))
    end.
*)

Definition stlc_argument_case2 :=
  tfix (abs F
    (abs n
      (tif0 n 0
        (tplus 1 (app F (app F (app F (tminus n 1)))))))).

Compute (CPS_conversion stlc_argument_case2).

Definition stlc_argument_case2_CPS :=
  tfix (abs F
    (abs n
      (abs k
        (tif0 n (app k 0)
          (app (app F (tminus n 1))
            (abs res1
              (app (app F res1)
                (abs res2
                  (app (app F res2)
                    (abs res3
                      (app k (tplus 1 res3)))))))))))).

Theorem stlc_argument_case2_correct :
  let origin_fun := stlc_argument_case2 in
  let CPS_fun := CPS_conversion stlc_argument_case2 in
  let input := 4 in
  let output := 4 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

(*
  F l :=
    match l with
    | nil => 0
    | n' :: l' => n' + F (map (add (F l')) l')
    end.
  We can transfer it to CPS-style by hand:
  F l k :=
    match l with
    | nil => k 0
    | n' :: l' => F l' (fun res1 => F (map (add res1) l') (fun res2 : k (n' + res2)))
    end.
*)

Definition stlc_argument_case3 :=
  tfix (abs F
    (abs l
      (tlcase l 0 n' l'
        (tplus n'
          (app F (app (app stlc_map (app stlc_add (app F l'))) l')))))).

Compute (CPS_conversion stlc_argument_case3).

Definition stlc_argument_case3_CPS :=
  tfix (abs F
    (abs l
      (abs k
        (tlcase l (app k 0) n' l'
          (app (app F l')
            (abs res1
              (app (app F (app (app stlc_map (app stlc_add res1)) l'))
                (abs res2
                  (app k (tplus n' res2)))))))))).

Theorem stlc_argument_case3_correct :
  let origin_fun := stlc_argument_case3 in
  let CPS_fun := CPS_conversion stlc_argument_case3 in
  let input := tcons 2 (tcons 3 (tcons 5 tnil)) in
  let output := 54 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

(*
  F a b c :=
    match b with
    | 0 => 1
    | S _ => 1 + f (f a (b - 1) c - 2) (f (a - 1) (b - 1) c - 1) (f (a - 1) (b - 2) (c - 1) - 3)
    end.
  We can transfer it to CPS-style by hand:
  F a b c k :=
    match b with
    | 0 => k 1
    | S _ => f a (b - 1) c (fun res1 => f (a - 1) (b - 1) c (fun res2 => f (a - 1) (b - 2) (c - 1)
             (fun res3 => f (res1 - 2) (res2 - 1) (res3 - 3) (fun res4 => k (1 + res4)))))
    end.
*)

Definition stlc_argument_case4 :=
  tfix (abs F
    (abs a
      (abs b
        (abs c
          (tif0 b 1
            (tplus 1 <{ F (F a (b - 1) c - 2) (F (a - 1) (b - 1) c - 1) (F (a - 1) (b - 2) (c - 1) - 3) }>)))))).

Compute (CPS_conversion stlc_argument_case4).

Theorem stlc_argument_case4_correct :
  let origin_fun := stlc_argument_case4 in
  let CPS_fun := CPS_conversion stlc_argument_case4 in
  let input1 := 1 in
  let input2 := 1 in
  let input3 := 1 in
  let output := 2 in
  (<{origin_fun input1 input2 input3}> -->* output) /\ (<{CPS_fun input1 input2 input3 idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

End examples.
*)