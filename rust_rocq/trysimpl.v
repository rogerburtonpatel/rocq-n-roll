Require Import Stdlib.Arith.Arith.
Theorem simple_add : forall n : nat, 0 + n = n.

Proof.   
  try simpl.
  simpl.
  reflexivity. 
Qed.
