Lemma all_perm : forall (A:Type) (P:A -> A -> Prop), 
                      (forall x y : A, P x y) -> forall x y : A, P y x.
Proof.
  intros. apply H.
Qed.

Lemma resolution : forall (A:Type)(P Q R S : A -> Prop), 
                  (forall a:A, Q a -> R a -> S a) -> 
                  (forall b:A, P b -> Q b) -> 
                   forall c:A, P c -> R c -> S c.
Proof.
  intros A P Q R S H1 H2 c Pc Rc. apply H1. 
  - apply H2; assumption.
  - assumption.
Qed.

Require Export ZArith List ZArithRing.
Require Arith.
(*
Require Export:
It works like Require Import, but with an additional effect: 
   it not only imports the specified modules into the current context 
    but also makes these modules available to any other modules that import the current module.
This means that if another Coq file imports your file, it will automatically import ZArith, List, and ZArithRing as well.
 *)

Parameters (prime_divisor : nat->nat)
           (prime : nat->Prop)
           (divides : nat->nat->Prop).

Parameter binary_word : nat->Set.
Definition short : Set := binary_word 32.
Definition long  : Set := binary_word 64.

Parameters (decomp : nat->list nat)
           (decomp2 : nat->nat*nat).

Parameter prime_divisor_correct : forall n:nat, 2 <= n -> let d := prime_divisor n in prime d /\ divides d n.
Parameter binary_word_concat : forall n p : nat, binary_word n -> binary_word p -> binary_word (n+p).

Fixpoint iterate (A:Type)(f:A->A)(n:nat)(x:A) : A :=
  match n with
  | O => x
  | S p => f (iterate A f p x)
  end.

Arguments iterate {A} _ _ _.
Arguments binary_word_concat {n p} _ _.

Definition binary_word_duplicate (n:nat)(w:binary_word n) : binary_word (n+n) := binary_word_concat w w.
Definition short_concat : short -> short -> long := @binary_word_concat 32 32.

Definition compose {A B C : Type} : (A->B)->(B->C)->A->C := fun f g x => g(f(x)).
Definition thrice {A:Type} (f:A->A) := compose f (compose f f).

Lemma thrice_iter3 {A:Type} (f : A->A) : thrice f = iterate f 3.
Proof. reflexivity. Qed.

Definition my_plus : nat->nat->nat := iterate  S.
Definition my_mult (n p:nat) : nat := iterate  (my_plus n) p 0.
Definition my_expt (x n:nat) : nat := iterate (my_mult x) n 1.

Definition ackermann (n:nat) : nat -> nat := iterate (fun (f:nat->nat)(p:nat) => iterate f(S p) 1) n S.

