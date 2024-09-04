Require Import List ZArith RelationClasses Morphisms Extraction.
Open Scope Z_scope.

Inductive sorted : list Z -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall z:Z, sorted (z :: nil)
  | sorted2 : forall (z1 z2 : Z) (l : list Z), z1 <= z2 -> 
      sorted (z2 :: l) -> sorted (z1 :: z2 :: l).

#[export] Hint Constructors sorted : sort.
(*
#[export]: This attribute is used to export the hint into the global hint database. 
   It ensures that the hint is available across different files and in different contexts.

Hint Constructors sorted: This part of the line tells Coq to consider the constructors of the sorted inductive type as useful hints. 
   When Coq’s proof automation tools, like auto, eauto, or ltac, are working, they will use these hints to help fill in the proof.

: sort: This specifies that the hint belongs to the hint database named sort. 
   The sort database is often used for hints related to sorting and ordering. 
   It helps in categorizing and organizing hints.
 *)

Lemma sort_2357 : sorted (2 :: 3 :: 5 :: 7 :: nil).
Proof.
  auto with sort zarith.
Qed.

Theorem sorted_inv : forall (z:Z) (l:list Z), sorted (z :: l) -> sorted l.
Proof.
  intros z l H. inversion H; auto with sort.
Qed.
(*
Suppose you have a hypothesis S m = S n, where m and n are nats. The inversion tactic allows you to conclude that m = n. 
   In general, if you have a hypothesis that states an equality between two constructors and the constructors are the same, 
   inversion helps you figure out that all the arguments to those constructors must be equal as well, 
   and it tries to rewrite the goal using that information.
*)

Fixpoint count_z (z:Z) (l:list Z) {struct l} : nat :=
  match l with
  | nil => 0%nat
  | (z' :: l') => match Z.eq_dec z z' with
                  | left _ => S (count_z z l')
                  | right _ => count_z z l'
                  end
  end.
(*
Type: Z.eq_dec has the type forall x y : Z, {x = y} + {x <> y},
   which means it takes two integers x and y and returns a proof that either x is equal to y or x is not equal to y.

Usage: Z.eq_dec is used to perform a decision procedure for equality of integers. It returns a sum type:

left _ indicates that the two integers are equal, and the underscore _ represents the proof of equality.
right _ indicates that the two integers are not equal, and the underscore _ represents the proof of inequality.
 *)

Example ex0 : count_z 3 (3 :: 7 :: 3 :: nil) = 2%nat.
Proof.
  reflexivity.
Qed.
(*
If the goal contains an equality that looks obviously true,
   the reflexivity tactic can finish off the proof, doing some basic simplification if needed.
 *)

Definition permutation (l l' : list Z) : Prop :=
  forall z:Z, count_z z l = count_z z l'.

#[global] Instance permutation_refl : Reflexive permutation.
(*
This line declares an instance named permutation_relf (short for "permutation reflexive") and states that permutation is a reflexive relation.
   The Reflexive keyword is a typeclass in Coq that requires the relation to satisfy the reflexive property.

#[global]: This attribute makes the instance globally available,
   meaning that this reflexive property of the permutation relation will be automatically
   recognized by Coq's typeclass resolution mechanism in all contexts.

Instance: Declares a typeclass instance, which in this case says that permutation is reflexive.

Reflexive permutation: This is the type of the instance, asserting that the permutation relation is reflexive.
   Reflexivity means that for any list l, permutation l l holds, i.e., any list is a permutation of itself.
 *)
Proof.
  intro x. red. trivial.
  (*
The red tactic in Coq unfolds the definition of the relation permutation.
     This tactic is used to reduce or simplify the goal by expanding the definition.
After applying red, the goal would change to proving
     forall z: Z, count_z z x = count_z z x,
     which is the unfolded form of permutation x x.
  *)
Qed.

#[global] Instance permutation_sym : Symmetric permutation.
Proof.
  intros x y Hxy. unfold permutation. info_auto. 
Qed.
(*
unfold:
Purpose: unfold specifically replaces a defined identifier with its full definition. It works at the level of named definitions (e.g., constants, functions, or propositions).
Usage: You use unfold when you want to see or work with the underlying definition of a term.
   It's particularly useful when a definition is complex and you want to break it down step by step.

red:
Purpose: red is a more general tactic that performs one step of "reduction." 
   Reduction involves simplifying a goal by expanding one level of definition or application. 
   It reduces the goal to a simpler form without necessarily unfolding everything.
Usage: red is often used when you want to simplify a goal by performing one reduction step, 
   but without fully expanding all definitions. It’s more subtle than unfold, 
   as it focuses on reducing the goal to its essential form without necessarily exposing every detail of the definition.
 *)

#[global] Instance permutation_trans : Transitive permutation.
Proof.
  intros l l' l'' H H0 z. rewrite H. now apply H0.
Qed.
(*
Purpose: The now tactic is a convenient way to quickly finish a proof.
   It attempts to solve the current goal immediately using a combination of simple tactics like
   apply, exact, trivial, reflexivity, or assumption. If it can solve the goal, it completes the proof. If not, it fails immediately.
 *)

Lemma permutation_cons : forall (z:Z) (l l' : list Z), permutation l l' 
  -> permutation (z :: l) (z :: l').
Proof.
  intros z l l' H z'. simpl. case (Z.eq_dec z' z); auto.
Qed.
(*
The simpl tactic reduces complex terms to simpler forms.
   You'll find that it's not always necessary to use simpl because other tactics
   (e.g. discriminate) can do the simplification themselves, but it's often helpful
   to try simpl to help you figure out what you, as the writer of the proof, should do next.

You can also use simpl on a hypothesis in the context with the syntax simpl in <hypothesis>.

simpl will never fail, even if no simplification can be done.
 *)

#[global] Instance cons_proper : Proper (eq ==> permutation ==> permutation) (@cons Z).
Proof.
  intros x y Hxy l l' Hll'. subst y; now apply permutation_cons.
Qed.
(*
Proper is a typeclass in Coq that expresses the idea that a function respects certain relations.
   Specifically, it indicates that the function behaves properly with respect to certain input-output relations.

(eq ==> permutation ==> permutation):
This is the signature of the Proper instance. It states that:
    If the first argument respects the equality relation (eq) and
    The second argument respects the permutation relation,
    Then the result of applying the cons function to these arguments will also respect the permutation relation.
 *)

Lemma permutation_traspose : forall (a b : Z) (l l' : list Z), permutation l l' -> permutation (a :: b :: l) (b :: a :: l').
Proof.
  intros a b l l' H z. simpl.
  case (Z.eq_dec z a); case (Z.eq_dec z b); simpl; case (H z); auto.
Qed.

#[export] Hint Resolve permutation_cons permutation_refl permutation_traspose : sort.

Fixpoint insert (z:Z) (l : list Z) : list Z :=
  match l with 
  | nil => z :: nil
  | cons a l' =>
      match Z_le_gt_dec z a with
      | left _ => z :: a :: l'
      | right _ => a :: (insert z l')
      end
  end.
Check Z_le_gt_dec.

Lemma insert_permutation : forall (l : list Z) (x:Z), permutation (x :: l)(insert x l).
Proof.
  induction l as [| a l0 H]; simpl; auto with sort.
  intros x; case (Z_le_gt_dec x a); simpl; auto with sort.
  intro H0; apply permutation_trans with (a :: x :: l0); auto with sort.
Qed.

Lemma insert_sorted : forall (l : list Z) (x:Z), sorted l -> sorted (insert x l).
Proof.
  intros l x H; induction H; simpl; info_auto with sort.
  - case (Z_le_gt_dec x z); simpl; info_auto with sort zarith.
  - revert H H0 IHsorted; simpl; case (Z_le_gt_dec x z2), (Z_le_gt_dec x z1); simpl; info_auto with sort zarith.
Qed.

Definition sort : forall l:list Z, {l' : list Z | permutation l l' /\ sorted l'}.
(*
{l' : list Z | permutation l l' /\ sorted l'}:
This part specifies the return type of the sort function.
The return type is a dependent pair (or sigma type) in Coq. It means that sort returns a pair consisting of:
l': A list of integers (list Z).
A proof that:
permutation l l': The list l' is a permutation of the input list l, meaning that l' contains the exact same elements as l, but possibly in a different order.
sorted l': The list l' is sorted in some specified order (usually in non-decreasing order).
 *)
  induction l as [| a l IHl].
  - exists (nil (A:=Z)); split; info_auto with sort.
  - case IHl; intros l' [H0 H1].
    exists (insert a l'); split.
      + transitivity (a :: l').
        * now rewrite H0.
        * apply insert_permutation.
      + now apply insert_sorted.
Defined.

Compute (proj1_sig (sort (5 :: 2 :: 1 :: 9 :: nil))).
Check (proj2_sig (sort (5 :: 2 :: 1 :: 9 :: nil))).
