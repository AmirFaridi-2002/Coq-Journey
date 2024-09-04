Require Import List.
Parameters (decomp : nat -> list nat)(decomp2 : nat -> nat*nat).

Check decomp 220.
Check decomp2 230.

Check le_n.
Check le_S.

Definition twice : forall A : Set, (A -> A) -> A -> A
    := fun A f a => f (f a).

Check twice.

Require Import ZArith.
Check twice Z.
Check twice _ S 56.

Eval compute in (twice (nat -> nat)(fun f x => f (f x))(mult 3) 1).


Theorem le_i_SSi : forall i:nat, i <= S (S i).
Proof (fun i:nat => le_S _ _ (le_S _ _ (le_n i))).

Check (le_n).
Check (le_S _ _ (le_n 1)).
Check (fun i:nat => le_S _ _ (le_S _ _ (le_n i))).




Definition compose : forall A B C : Set, (A -> B) -> (B -> C) -> A -> C
    := fun A B C f g x => g (f x).

Print compose.

Check (fun (A : Set)(f : Z->A) => compose _ _ _ Z_of_nat f).

Check le_i_SSi 10.

