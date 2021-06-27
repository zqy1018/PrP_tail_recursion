From STLC Require Export Argument.

(*
  F l1 :=
    match l1 with
    | nil => 2
    | n1 :: l1' => 1 + match l1' with
                       | nil => 2
                       | n2 :: l2' => n1 + n2 + F l2'
                       end
    end.
  We can transfer it to CPS-style by hand:
  F l1 k :=
    match l1 with
    | nil => k 2
    | n1 :: l1' => match l1' with
                   | nil => k (1 + 2)
                   | n2 :: l2' => F l2' (fun res1 => k (1 + (n1 + n2 + res1)))
                   end
    end.
*)

Definition stlc_example_1 :=
  tfix (abs F (abs l1
    (tlcase l1 2 n1 l1'
      (tplus 1 (tlcase l1' 2 n2 l2'
        (tplus (tplus n1 n2) (app F l2'))))))).

Compute (CPS_conversion stlc_example_1).

(*
  F n1 n2 n3 :=
    1 + match F n1 n2 n3 with
        | 0 => 2 + F n1 n2 (n3 - 1)
        | S _ => 3 + F n1 n2 (n3 - 2)
        end
*)

Definition stlc_example_2 :=
  tfix (abs F (abs n1 (abs n2 (abs n'
    (tplus 1 (tif0 (app (app (app F n1) n2) n')
      (tplus 2 (app (app (app F n1) n2) (tminus n' 1)))
        (tplus 3 (app (app (app F n1) n2) (tminus n' 2))))))))).
        
Compute (CPS_conversion stlc_example_2).
        