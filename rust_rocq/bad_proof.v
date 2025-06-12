Require Import Coq.Arith.Arith.

Theorem bad_proof : forall n : nat, n + 0 = n + 1.
Proof.
  intros n.
  simpl.
  (* This will fail because n + 0 ≠ n + 1 *)
  reflexivity.
Qed.