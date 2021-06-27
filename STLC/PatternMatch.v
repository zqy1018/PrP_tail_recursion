From STLC Require Export Initial.

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

(*
  Deal with complicated pattern match, no longer using an extra parameter [fuel] to get accepted.
*)

Fixpoint CPS (continuation_name : string) (func_name : string) (func_body : tm) (naming : nat) (k : tm -> tm) {struct func_body} : tm :=
  match func_body with
  | var _ =>
       let result := k func_body in
       match find_func func_name result with
       | O => app (var continuation_name) result
       | S n1 => result
       end
  | abs x1 t1 =>
       abs x1 (CPS continuation_name func_name t1 naming k)
  | app t1 t2 =>
       if is_recu func_name func_body then
       let para_name := append "res" (nat2string naming) in
       let result := k (var para_name) in
       app func_body (abs para_name match find_func func_name result with
                                                | O => app (var continuation_name) result
                                                | S n1 => result
                                                end)
       else match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app (var continuation_name) (k func_body)
       | S n1, O =>
            CPS continuation_name func_name t1 naming (fun res : tm => k (app res t2))
       | O, S n2 =>
            CPS continuation_name func_name t2 naming (fun res : tm => k (app t1 res))
       | S n1, S n2 =>
            CPS continuation_name func_name t1 naming
            (fun res1 : tm => CPS continuation_name func_name t2 (naming + (S n1))
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
            CPS continuation_name func_name t1 naming (fun res : tm => k (tplus res t2))
       | O, S n2 =>
            CPS continuation_name func_name t2 naming (fun res : tm => k (tplus t1 res))
       | S n1, S n2 =>
            CPS continuation_name func_name t1 naming
            (fun res1 : tm => CPS continuation_name func_name t2 (naming + (S n1))
            (fun res2 : tm => k (tplus res1 res2)))
       end
  | tminus t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app (var continuation_name) (k func_body)
       | S n1, O =>
            CPS continuation_name func_name t1 naming (fun res : tm => k (tminus res t2))
       | O, S n2 =>
            CPS continuation_name func_name t2 naming (fun res : tm => k (tminus t1 res))
       | S n1, S n2 =>
            CPS continuation_name func_name t1 naming
            (fun res1 : tm => CPS continuation_name func_name t2 (naming + (S n1))
            (fun res2 : tm => k (tminus res1 res2)))
       end
  | tmult t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app (var continuation_name) (k func_body)
       | S n1, O =>
            CPS continuation_name func_name t1 naming (fun res : tm => k (tmult res t2))
       | O, S n2 =>
            CPS continuation_name func_name t2 naming (fun res : tm => k (tmult t1 res))
       | S n1, S n2 =>
            CPS continuation_name func_name t1 naming
            (fun res1 : tm => CPS continuation_name func_name t2 (naming + (S n1))
            (fun res2 : tm => k (tmult res1 res2)))
       end
  | tif0 t1 t2 t3 =>
       match find_func func_name t1 with
       | O => tif0 t1 (CPS continuation_name func_name t2 naming k) (CPS continuation_name func_name t3 naming k)
       | S n1 => CPS continuation_name func_name t1 naming (fun res : tm => k (tif0 res t2 t3))
       end
  
  | tnil =>
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
            CPS continuation_name func_name t1 naming (fun res : tm => k (tcons res t2))
       | O, S n2 =>
            CPS continuation_name func_name t2 naming (fun res : tm => k (tcons t1 res))
       | S n1, S n2 =>
            CPS continuation_name func_name t1 naming
            (fun res1 : tm => CPS continuation_name func_name t2 (naming + (S n1))
            (fun res2 : tm => k (tcons res1 res2)))
       end
  | tlcase t1 t2 x1 x2 t3 =>
       match find_func func_name t1 with
       | O => tlcase t1 (CPS continuation_name func_name t2 naming k) x1 x2 (CPS continuation_name func_name t3 naming k)
       | S n1 => CPS continuation_name func_name t1 naming (fun res : tm => k (tlcase res t2 x1 x2 t3))
       end
  
  | tlet x1 t1 t2 =>
       match find_func func_name t1, find_func func_name t2 with
       | O, O =>
            app (var continuation_name) (k func_body)
       | S n1, O =>
            CPS continuation_name func_name t1 naming (fun res : tm => k (tlet x1 res t2))
       | O, S n2 =>
            CPS continuation_name func_name t2 naming (fun res : tm => k (tlet x1 t1 res))
       | S n1, S n2 =>
            CPS continuation_name func_name t1 naming
            (fun res1 : tm => CPS continuation_name func_name t2 (naming + (S n1))
            (fun res2 : tm => k (tlet x1 res1 res2)))
       end
  
  | tfix t1 =>
       tfix (CPS continuation_name func_name t1 naming k)
  end.

Definition CPS_conversion (func : tm) : tm :=
  match func with
  | tfix (abs func_name func_body) =>
       let continuation_name := k in
       let func_paraed_body := para_insert continuation_name func_body in
       tfix (abs func_name (CPS continuation_name func_name func_paraed_body 1 (fun res : tm => res)))
  | _ => func
  end.

(*verification by examples*)

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

End examples.