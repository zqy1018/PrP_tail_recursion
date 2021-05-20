From STLC Require Export Definitions.

(*
  An initial version of CPS conversion which can not deal with complicated
  pattern matching and requires a parameter [fuel] to get accepted by Coq.
*)

Fixpoint extract_and_substitute (func_name : string) (func_body : tm) (substitution : string) : tm * tm :=
  if is_recu func_name func_body
  then (func_body, var substitution)
  else match func_body with
  | abs x1 t1 =>
       let (para1, para2) := extract_and_substitute func_name t1 substitution
       in (para1, abs x1 para2)
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

Fixpoint CPS (func_name : string) (func_body : tm) (naming : nat) (fuel : nat) : tm :=
  match fuel with | O => func_body | S fuel' =>
    match func_body with
    | abs x1 t1 =>
         abs x1 (CPS func_name t1 naming fuel')
  
    | tif0 t1 t2 t3 =>
         tif0 t1 (CPS func_name t2 naming fuel') (CPS func_name t3 naming fuel')
  
    | tlcase t1 t2 x1 x2 t3 =>
         tlcase t1 (CPS func_name t2 naming fuel') x1 x2 (CPS func_name t3 naming fuel')
  
    | tlet x1 t1 t2 =>
         tlet x1 (CPS func_name t1 naming fuel') (CPS func_name t2 naming fuel')
  
    | tfix t1 =>
         tfix (CPS func_name t1 naming fuel')
  
    | _ =>
         match find_func func_name func_body with
         | 0 => app k func_body
         | S _ => let continuation_name := append "res" (nat2string naming) in
                  let (parameterized_func, substituted_func_body) := extract_and_substitute func_name func_body continuation_name in
                    app parameterized_func (abs continuation_name
                      (CPS func_name substituted_func_body (naming + 1) fuel'))
         end
    end
  end.

Definition CPS_conversion (func : tm) : tm :=
  match func with
  | tfix (abs func_name func_body) =>
      let func_paraed_body := para_insert k func_body in
      let func_new_body := CPS func_name func_paraed_body 1 999 in
        tfix (abs func_name func_new_body)
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

Print stlc_sum_of_list.
Compute (CPS_conversion stlc_sum_of_list).

Theorem stlc_sum_of_list_correct :
  let exfun := CPS_conversion stlc_sum_of_list in
  let input := tcons 1 (tcons 5 (tcons 8 tnil)) in
  let output := 14 in
  <{exfun input idNat}> -->* output.
Proof. solve_CPS. Qed.

End examples.