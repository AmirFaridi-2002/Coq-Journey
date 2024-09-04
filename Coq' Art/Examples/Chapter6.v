Inductive month : Set := 
    | January   |   February  | March
    | April     |   May       | June
    | July      |   August    | September
    | October   |   November  | December.

Print month.
Print month_ind.
Print month_rec.

Require Import ZArith.
Open Scope Z_scope.
Inductive plane : Set := point : Z -> Z -> plane.
Print plane_ind.
Close Scope Z_scope.

Definition next_month (m:month) :=
match m with
   January   => February
 | February  => March
 | March     => April
 | April     => May
 | May       => June
 | June      => July
 | July      => August
 | August    => September
 | October   => November
 | September => October
 | November  => December
 | December  => January
end.

Theorem next_aug_then_jul :
  forall m:month, next_month m = August -> m = July.
Proof.
  intros m; case m; simpl; intros Hnext_eq;
  (discriminate Hnext_eq || reflexivity).
Qed.

Theorem plus_assoc:
    forall x y z : nat, (x+y)+z = x+(y+z).
Proof.
  intros x y z. induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Fixpoint timestwo (n : nat) : nat :=
  match n with
    0 => 0
  | S p => S (S (timestwo p))
  end.

Fixpoint plus (n m : nat){struct n} : nat :=
  match n with O => m | S p => S (plus p m) end.


Fixpoint iterate (A:Set)(f:A -> A)(n:nat)(x:A){struct n} : A :=
  match n with
  | O => x
  | S p => f (iterate A f p x)
  end.

Inductive btree : Set :=
  leaf : btree | node : nat -> btree -> btree -> btree.

Fixpoint sum_btree (t : btree) : nat :=
  match t with
  | leaf => 0
  | node v t1 t2 => 
      v + sum_btree t1 + sum_btree t2
  end.

Fixpoint has_zero (t:btree) : bool :=
  match t with
  | leaf => false
  | node 0 t1 t2 => true
  | node _ t1 t2 => if has_zero t1 then true else has_zero t2
  end.

Inductive INF_tree : Set :=
    INF_leaf : INF_tree
  | INF_node : nat -> (nat->INF_tree)->INF_tree.



Require Import List.
Print list.
Section deflist.
  Variable A : Set.
  Inductive list' : Set :=
    | nil' : list'
    | cons' : A -> list' -> list'.
  End deflist.

Print list'_ind.

Fixpoint app (A : Set)(l m : list A){struct l} : list A :=
  match l with
  | nil => m
  | cons a l1 => cons a (app A l1 m)
  end.

Print option.

Definition prednatoption (n:nat) : option nat :=
  match n with O => None | S p => Some p end.

Eval compute in prednatoption 0.
Eval compute in prednatoption 5.

Fixpoint nth_option (A:Set)(n:nat)(l:list A){struct l}
  : option A :=
  match n, l with
  | 0, cons a tl => Some a
  | S p, cons a tl => nth_option A p tl
  | _, nil => None
  end.

Print fst.

Inductive ltree (n:nat) : Set :=
  | lleaf : ltree n
  | lnode : forall p:nat, p <= n -> ltree n -> ltree n -> ltree n.

(* representation of the type of trees of height n with elements of type A. *)
Inductive htree (A:Set) : nat -> Set :=
  | hleaf : A->htree A 0
  | hnode : forall n:nat, A->htree A n -> htree A n -> htree A (S n).

Check htree_ind.

Inductive empty : Set :=.
Inductive strange : Set := cs : strange -> strange.

Theorem strange_empty : forall x:strange, False.
Proof.
  intros. induction x. trivial.
Qed.

Inductive even_line : nat->Set :=
  | even_empty_line : even_line 0
  | even_step_line : forall n:nat, even_line n -> even_line (S (S n)).
