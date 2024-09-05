Require Import Arith.
Require Import ZArith.

Search Z.
Search nat.

Check Nat.add_assoc.

Theorem plus_permute2 : forall n m p : nat, n + m + p = n + p + m.
Proof.
  intros. rewrite <- Nat.add_assoc. rewrite Nat.add_assoc. rewrite <- Nat.add_assoc.
  pattern (m+p); rewrite Nat.add_comm. 
  rewrite <- Nat.add_assoc. reflexivity.
Qed.

Theorem plus_permute2' : forall n m p : nat, n + m + p = n + p + m.
Proof.
  intros. ring.
Qed.
