Theorem semicolon_simpl : forall n : nat, n + 0 = n.
Proof.
  intros; simpl; reflexivity.
Qed.