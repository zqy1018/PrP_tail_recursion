From STLC Require Export PatternMatch.

(*
  Now we consider a more tricky stlc programme.
  
  F l :=
    match l with
    | nil => 0
    | n' :: l' => n' + F (map (add (app F l')) l')
    end.
*)

Definition stlc_tricky_sum_of_list :=
  tfix (abs F (Arrow (List Nat) Nat)
    (abs l (List Nat)
      (tlcase l 0 n' l'
        (tplus n'
          (app F (app (app stlc_map (app stlc_add (app F l'))) l')))))).

Theorem example_stlc_tricky_sum_of_list :
  let exfun := stlc_tricky_sum_of_list in
  let input := tcons 5 (tcons 4 (tcons 3 (tnil Nat))) in
  let output := 45 in
  <{exfun input}> -->* output.
Proof. solve_CPS. Qed.

Compute (pattern_match_version.CPS_conversion stlc_tricky_sum_of_list).

Theorem example_stlc_tricky_sum_of_list_CPS :
  let exfun := pattern_match_version.CPS_conversion stlc_tricky_sum_of_list in
  let input := tcons 5 (tcons 4 (tcons 3 (tnil Nat))) in
  let output := 45 in
  <{exfun input idNat}> -->* output.
Proof. solve_CPS. Qed.

Module fixpoint_version.


End fixpoint_version.