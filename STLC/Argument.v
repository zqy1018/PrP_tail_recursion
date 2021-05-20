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

Print is_recu.

Fixpoint CPS (k : tm) (func_name : string) (func_body : tm) (continuation : tm -> tm) (naming : nat) (fuel : nat) {struct fuel} : tm :=
match fuel with | 0 => func_body | S fuel' =>
  match func_body with
  | var _ =>
       let result := continuation func_body in
       match find_func func_name result with
       | O => app k result
       | S n1 => result
       end
  | abs x1 t1 =>
       abs x1 (CPS k func_name t1 continuation naming fuel')
  | app t1 t2 =>
       if is_recu func_name func_body then
       let para_name := append "res" (nat2string naming) in
       let result := continuation (var para_name) in
       app func_body (abs para_name
                      match find_func func_name result with
                      | O => app k result
                      | S n1 => result
                      end)
       else if is_app_F func_name func_body then
       match t1 with
       | app func_name t1' =>
            CPS k func_name t1'
            (fun res1 : tm => CPS k func_name t2
            (fun res2 : tm => continuation (app res1 res2)) (naming + (S n1)) fuel') naming fuel'
       | _ =>
            CPS k func_name t1
            (fun res1 : tm => CPS k func_name t2
            (fun res2 : tm => continuation (app res1 res2)) (naming + (S n1)) fuel') naming fuel'
       end
       else match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app k (continuation func_body)
       | S n1, O =>
            CPS k func_name t1 (fun res : tm => continuation (app res t2)) naming fuel'
       | O, S n2 =>
            CPS k func_name t2 (fun res : tm => continuation (app t1 res)) naming fuel'
       | S n1, S n2 =>
            CPS k func_name t1
            (fun res1 : tm => CPS k func_name t2
            (fun res2 : tm => continuation (app res1 res2)) (naming + (S n1)) fuel') naming fuel'
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
            CPS k func_name t1 (fun res : tm => continuation (tplus res t2)) naming fuel'
       | O, S n2 =>
            CPS k func_name t2 (fun res : tm => continuation (tplus t1 res)) naming fuel'
       | S n1, S n2 =>
            CPS k func_name t1
            (fun res1 : tm => CPS k func_name t2
            (fun res2 : tm => continuation (tplus res1 res2)) (naming + (S n1)) fuel') naming fuel'
       end
  | tminus t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app k (continuation func_body)
       | S n1, O =>
            CPS k func_name t1 (fun res : tm => continuation (tminus res t2)) naming fuel'
       | O, S n2 =>
            CPS k func_name t2 (fun res : tm => continuation (tminus t1 res)) naming fuel'
       | S n1, S n2 =>
            CPS k func_name t1
            (fun res1 : tm => CPS k func_name t2
            (fun res2 : tm => continuation (tminus res1 res2)) (naming + (S n1)) fuel') naming fuel'
       end
  | tmult t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app k (continuation func_body)
       | S n1, O =>
            CPS k func_name t1 (fun res : tm => continuation (tmult res t2)) naming fuel'
       | O, S n2 =>
            CPS k func_name t2 (fun res : tm => continuation (tmult t1 res)) naming fuel'
       | S n1, S n2 =>
            CPS k func_name t1
            (fun res1 : tm => CPS k func_name t2
            (fun res2 : tm => continuation (tmult res1 res2)) (naming + (S n1)) fuel') naming fuel'
       end
  | tif0 t1 t2 t3 =>
       match find_func func_name t1 with
       | O => tif0 t1 (CPS k func_name t2 continuation naming fuel') (CPS k func_name t3 continuation naming fuel')
       | S n1 => CPS k func_name t1 (fun res : tm => continuation (tif0 res t2 t3)) naming fuel'
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
            CPS k func_name t1 (fun res : tm => continuation (tcons res t2)) naming fuel'
       | O, S n2 =>
            CPS k func_name t2 (fun res : tm => continuation (tcons t1 res)) naming fuel'
       | S n1, S n2 =>
            CPS k func_name t1
            (fun res1 : tm => CPS k func_name t2
            (fun res2 : tm => continuation (tcons res1 res2)) (naming + (S n1)) fuel') naming fuel'
       end
  | tlcase t1 t2 x1 x2 t3 =>
       match find_func func_name t1 with
       | O => tlcase t1 (CPS k func_name t2 continuation naming fuel') x1 x2 (CPS k func_name t3 continuation naming fuel')
       | S n1 => CPS k func_name t1 (fun res : tm => continuation (tlcase res t2 x1 x2 t3)) naming fuel'
       end
  
  | tlet x1 t1 t2 =>
       tlet x1 (CPS k func_name t1 continuation naming fuel') (CPS k func_name t2 continuation naming fuel')
  
  | tfix t1 =>
       tfix (CPS k func_name t1 continuation naming fuel')
  end
end.

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
       | O => 1 + Coq.Arith.PeanoNat.Nat.max (depth func_name t2) (depth func_name t3)
       | S n1 => 1 + depth func_name t1
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
       | O => 1 + Coq.Arith.PeanoNat.Nat.max (depth func_name t2) (depth func_name t3)
       | S n1 => 1 + depth func_name t1
       end
  
  | tlet _ t1 t2 =>
       1 + Coq.Arith.PeanoNat.Nat.max (depth func_name t1) (depth func_name t2)
  
  | tfix t1 =>
       1 + depth func_name t1
  end.

Definition CPS_conversion (func : tm) : tm :=
  match func with
  | tfix (abs func_name func_body) =>
       let func_paraed_body := para_insert k func_body in
       tfix (abs func_name (CPS k func_name func_paraed_body (fun res : tm => res) 1 (depth func_name func_paraed_body)))
  | _ => func
  end.

Module examples.

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

End examples.