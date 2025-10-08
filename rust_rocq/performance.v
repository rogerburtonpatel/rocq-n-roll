Require Import Stdlib.Arith.Arith.
Set Info Auto. 
Set Info Eauto. 
Set Info Trivial.

Theorem simple_add : forall n : nat, 0 + n = n.
Proof.
    simpl. 
    reflexivity. 
Qed.

Theorem semicolon_simpl : forall n : nat, n + 0 = n.
Proof.
    intros; simpl; reflexivity.
Qed.

Theorem auto_add : forall n : nat, n + 0 = n.
Proof.
    auto.
Qed.

Theorem split_auto : forall n : nat, n + 0 = n /\ 0 + n = n.
Proof.   
  split. 
  - auto. 
  - auto. 
Qed.
