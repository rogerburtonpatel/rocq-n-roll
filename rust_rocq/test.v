Require Import Stdlib.Arith.Arith.
Theorem simple_add : forall n : nat, n + 0 = n.
Set Info Auto. 
Theorem simple_add : forall n : nat, n + 0 = n /\ 0 + n = n.

Proof.   
  split. 
  - auto. 
  - auto. 
Qed.

Theorem silly : forall n : nat, n = n.
Proof. 
  simpl. 
  simpl. 
  simpl. 
  reflexivity. 
Qed. 