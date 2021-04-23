From STLC Require Export Initial.

Module pattern_match_version.

(*
  Deal with complicated pattern match, no longer using an extra parameter [fuel] to get accepted.
*)

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
       abs x1 T (CPS continuation_name output_type func_name t1 naming k)
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

Definition stlc_match_case1 :=
  tfix (abs F (Arrow (List Nat) Nat)
    (abs l (List Nat)
      (tlcase l 0 n1 l1
        (tlcase l1 n1 n2 l2
          (tplus n1 (tplus n2 (app F l2))))))).

Compute (CPS_conversion stlc_match_case1).

Theorem stlc_match_case1_correct :
  let origin_fun := stlc_match_case1 in
  let CPS_fun := CPS_conversion stlc_match_case1 in
  let input := tcons 4 (tcons 3 (tcons 1 (tcons 2 (tnil Nat)))) in
  let output := 10 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

Definition stlc_match_case2 :=
  tfix (abs F (Arrow (List Nat) Nat)
    (abs l (List Nat)
      (tplus 1 (tlcase l 0 n1 l1
        (tplus n1 (app F l1)))))).

Compute (CPS_conversion stlc_match_case2).

Theorem stlc_match_case2_correct :
  let origin_fun := stlc_match_case2 in
  let CPS_fun := CPS_conversion stlc_match_case2 in
  let input := tcons 4 (tcons 3 (tcons 1 (tcons 2 (tnil Nat)))) in
  let output := 15 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

Definition stlc_match_case3 :=
  tfix (abs F (Arrow (List Nat) Nat)
    (abs l (List Nat)
      (tlcase l 0 n1 l1
        (tif0 (app F l1) n1 (tmult 2 n1))))).

Compute (CPS_conversion stlc_match_case3).

Theorem stlc_match_case3_correct :
  let origin_fun := stlc_match_case3 in
  let CPS_fun := CPS_conversion stlc_match_case3 in
  let input := tcons 2 (tcons 2 (tnil Nat)) in
  let output := 4 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

Definition stlc_match_case4 :=
  tfix (abs F (Arrow (List Nat) (Arrow (List Nat) Nat))
    (abs l1 (List Nat)
       (abs l2 (List Nat)
         (tplus (tlcase l1 0 n1 l'
           (tplus n1 (app (app F l') l2)))
             (tlcase l2 0 n2 l''
               (tplus n2 (app (app F l1) l''))))))).

Compute (CPS_conversion stlc_match_case4).

Theorem stlc_match_case4_correct :
  let origin_fun := stlc_match_case4 in
  let CPS_fun := CPS_conversion stlc_match_case4 in
  let input1 := tcons 2 (tcons 3 (tcons 5 (tnil Nat))) in
  let input2 := tcons 4 (tcons 2 (tnil Nat)) in
  let output := 110 in
  (<{origin_fun input1 input2}> -->* output) /\ (<{CPS_fun input1 input2 idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

Definition stlc_match_case5 :=
  tfix (abs F (Arrow (List Nat) Nat)
    (abs l (List Nat)
      (tplus 3 (tmult (tlcase l (tminus 2 1) n1 l'
        (tplus n1 (tplus 1 (tplus (app F l') 1)))) 5)))).

Compute (CPS_conversion stlc_match_case5).

Theorem stlc_match_case5_correct :
  let origin_fun := stlc_match_case5 in
  let CPS_fun := CPS_conversion stlc_match_case5 in
  let input := tcons 2 (tcons 3 (tcons 5 (tnil Nat))) in
  let output := 2113 in
  (<{origin_fun input}> -->* output) /\ (<{CPS_fun input idNat}> -->* output).
Proof. split. solve_CPS. solve_CPS. Qed.

End examples.

End pattern_match_version.