Require Import Coq.Arith.Arith.

Theorem good_proof : forall n : nat, n + 0 = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.