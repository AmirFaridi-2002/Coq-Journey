Theorem le0E : forall n:nat, n <= 0 -> n = 0.
  Proof.
    intros n H.
    induction n.
    - trivial.
    - inversion H.
  Qed.

Theorem lazy_example : forall n:nat, (S n) + 0 = S n.
  Proof. 
    intros n. lazy beta iota zeta delta.
    fold plus. auto.
  Qed.

Theorem subst_example: forall a b c d : nat, a = b + c -> c = 1 -> a+b = d -> 2*a = d+c.
Proof.
  intros a b c d H H1 H2.
  subst a. subst c. subst d. simpl.
Abort.

Require Import ZArith.
Open Scope Z_scope.
Require Import Lia.
Theorem omega_example1 : forall x y z t : Z, x <= y <= z /\ z <= t <= x -> x = t.
Proof.
  intros x y z t H. lia.
Qed.

Theorem omega_example2 : forall x y : Z, 0 <= x*x -> 3*(x*x) <= 2*y -> x*x <= y.
Proof.
  intros x y H H0. lia.
Qed.

Theorem omega_example3: forall x y : Z, 0 <= x*x -> 3*(x*x) <= 2*y -> x*x <= y.
Proof. 
  intros x y H H0. lia.
Qed.

Close Scope Z_scope.

Require Import Reals.
Open Scope R_scope.
Theorem example_for_field : forall x y : R, ~(y=0) -> (x+y) / y = 1+(x/y).
Proof.
  intros x y H. field. trivial.
Qed.

Require Import Fourier.
Theorem example_for_fourier : forall x y : R, x-y > 1 -> x - 2*y < 0 -> x > 1.
Proof.
  intros x y H H0. fourier.
Qed.

Close Scope R_scope.

Open Scope nat_scope.
Theorem example_intuition : forall n p q : nat, n <= p \/ n <= q -> n <= p \/ n <= S q.
Proof.
  intros n p q. intuition auto with arith.
Qed.

Ltac le_S_star := apply le_n || (apply le_S; le_S_star).

Theorem le_5_25 : 5 <= 25.
Proof.
  le_S_star.
Qed.


Section primes.
  Definition divides (n m : nat) := exists p:nat, p*n = m.
  Hypotheses (divides_0 : forall n:nat, divides n 0).
  Hypotheses (divides_plus : forall n m : nat, divides n m -> divides n (n+m)).
  Hypotheses (not_divides_plus : forall n m : nat, ~divides n m -> ~divides n (n+m)).
  Hypotheses (not_divides_lt : forall n m : nat,  0 < m -> m < n -> ~divides n m).
  Hypotheses (not_lt_2_divides : forall n m : nat , ~(n=1) -> n < 2 -> 0 < m -> ~divides n m).
  Hypotheses (le_plus_minus : forall n m : nat, le n m -> m = n+(m-n)).
  Hypotheses (lt_lt_or_eq : forall n m : nat, n < S m -> n < m \/ n = m).

  Ltac check_not_divides :=
    match goal with
    | [ |- (~divides ?X1 ?X2) ] =>
        cut (X1 <= X2); [ idtac | le_S_star ]; intros Hle; rewrite (le_plus_minus _ _ Hle); 
            apply not_divides_plus; simpl; clear Hle; check_not_divides
    | [ |- _ ] => apply not_divides_lt; unfold lt; le_S_star
    end.
End primes.


