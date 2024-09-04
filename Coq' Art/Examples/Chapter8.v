Require Import ZArith.
Open Scope Z_scope.
Inductive plane : Set := point : Z -> Z -> plane.

Inductive south_west : plane -> plane -> Prop :=
  south_west_def : forall a1 a2 b1 b2 : Z, (a1 <= b1)%Z -> (a2 <= b2)%Z -> 
    south_west (point a1 a2)(point b1 b2).

Inductive sorted (A:Set)(R:A->A->Prop) : list A -> Prop := 
  | sorted0 : sorted A R nil
  | sorted1 : forall x:A, sorted A R (cons x nil)
  | sorted2 : forall (x y : A) (l : list A), R x y -> 
      sorted A R (cons y l) -> sorted A R (cons x (cons y l)).





Close Scope Z_scope.
