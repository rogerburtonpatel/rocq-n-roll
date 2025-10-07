(* Define natural numbers *)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(* Addition *)
Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

(* Multiplication *)
Fixpoint mul (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => add m (mul n' m)
  end.

(* List definition *)
Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

(* Length of a list *)
Fixpoint length {A} (l : list A) : nat :=
  match l with
  | nil => O
  | cons _ t => S (length t)
  end.

(* Append two lists *)
Fixpoint app {A} (l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

(* Sum of a list of natural numbers *)
Fixpoint sum (l : list nat) : nat :=
  match l with
  | nil => O
  | cons h t => add h (sum t)
  end.

(* Lemma 1: Adding zero on the left does nothing *)
Lemma add_O_l : forall n : nat, add O n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.

(* Lemma 2: Adding zero on the right does nothing *)
Lemma add_O_r : forall n : nat, add n O = n.
Proof.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* Lemma 3: Addition is associative *)
Lemma add_assoc : forall n m p : nat, add n (add m p) = add (add n m) p.
Proof.
  induction n as [| n' IH]; intros m p.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* Lemma 4: sum of appending lists *)
Lemma sum_app : forall l1 l2 : list nat,
    sum (app l1 l2) = add (sum l1) (sum l2).
Proof.
  induction l1 as [| h t IH]; intros l2.
  - simpl. reflexivity.
  - simpl. rewrite IH. rewrite add_assoc. reflexivity.
Qed.

(* Lemma 5: Length of appending lists *)
Lemma length_app : forall (A : Type) (l1 l2 : list A),
    length (app l1 l2) = add (length l1) (length l2).
Proof.
  induction l1 as [| h t IH]; intros l2.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* Lemma 6: Multiplying length by element *)
Lemma sum_mul_const : forall (n : nat) (l : list nat),
    length l = n -> forall m, sum (map (fun _ => m) l) = mul n m.
Proof.
  induction n as [| n' IH]; intros l H m.
  - destruct l as [| h t].
    + simpl. reflexivity.
    + simpl in H. discriminate.
  - destruct l as [| h t].
    + simpl in H. discriminate.
    + simpl in H. inversion H. simpl. rewrite IH with (l:=t). reflexivity. assumption.
Qed.

(* Define map for completeness *)
Fixpoint map {A B} (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons h t => cons (f h) (map f t)
  end.

(* Main theorem: sum of repeated element lists after append *)
Theorem sum_app_mul : forall (l1 l2 : list nat) (m : nat),
    sum (app (map (fun _ => m) l1) (map (fun _ => m) l2))
    = add (mul (length l1) m) (mul (length l2) m).
Proof.
  intros l1 l2 m.
  rewrite sum_app.
  rewrite sum_mul_const with (l:=l1); try reflexivity.
  rewrite sum_mul_const with (l:=l2); try reflexivity.
  reflexivity.
Qed.
