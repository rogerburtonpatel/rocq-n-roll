Require Import Stdlib.Arith.Arith.

Theorem simple_add : forall n : nat, n + 0 = n.
Proof.
  intros n.
  simpl. 
  rewrite <- plus_n_O.
  reflexivity.
Qed.
