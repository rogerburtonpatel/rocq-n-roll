Require Import Stdlib.Arith.Arith.
Theorem simple_add : forall n : nat, n + 0 = n.
Set Info Eauto. 
Theorem simple_add : forall n : nat, n + 0 = n /\ 0 + n = n.

Proof.   
  split. 
  - eauto. 
  - eauto. 
Qed.
