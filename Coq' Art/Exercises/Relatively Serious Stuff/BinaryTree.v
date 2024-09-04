Require Import Bool ZArith.
Require Export List.

Inductive Zbtree : Type :=
|  leaf 
|  bnode (r:Z)(t1 t2: Zbtree).


Definition is_leaf (t: Zbtree) : bool :=
 match t with leaf => true | _ => false end.


Fixpoint size (t: Zbtree) : nat :=
match t with
| leaf => 1
| bnode _ t1 t2 => 1 + size t1 + size t2
end.

Fixpoint height (t:Zbtree) : nat :=
match t with 
| leaf => 0
| bnode _ t1 t2 => 1 + Nat.max (height t1 ) (height t2)
end.

Fixpoint mirror (t:Zbtree) : Zbtree :=
match t with 
| leaf => leaf
| bnode r t1 t2 => bnode r (mirror t2) (mirror t1)
end.

Fixpoint memb (n:Z)(t: Zbtree) : bool :=
match t with
| leaf => false
| bnode r t1 t2 => Z.eqb r n || memb n t1 || memb n t2 
end.

Fixpoint infix_list (t:Zbtree) : list Z :=
match t with leaf => nil
           | bnode r t1 t2 => infix_list t1 ++ (r :: infix_list t2)
end.

Fixpoint strict_majorant (m:Z)(t:Zbtree) : bool :=
match t with leaf => true
           | bnode r t1 t2 => Z.ltb r m &&
                                    strict_majorant m t1 && 
                                    strict_majorant m t2
end.

Fixpoint strict_minorant (m:Z)(t:Zbtree) : bool :=
match t with leaf => true
           | bnode r t1 t2 => Z.ltb m r &&
                                  strict_minorant m t1 && 
                                  strict_minorant m t2
end.

Fixpoint is_searchtree (t:Zbtree) : bool :=
match t with leaf => true
           | bnode n t1 t2 => strict_minorant n t2 &&
                              strict_majorant n t1  &&
                              is_searchtree t1 &&
                              is_searchtree t2 
end.

Fixpoint memb_in_searchtree (n:Z)(t: Zbtree) : bool :=
match t with 
| leaf => false
| bnode r t1 t2 => 
  match Z.compare n r with
      | Lt => memb_in_searchtree n t1
      | Eq => true
      | Gt => memb_in_searchtree n t2
  end
end.

Fixpoint insert_in_searchtree (n:Z)(t: Zbtree) : Zbtree :=
match t with
| leaf => bnode n leaf leaf
| bnode r t1 t2 =>
  match Z.compare n r with
      | Lt => bnode r (insert_in_searchtree n t1) t2
      | Eq => t
      | Gt => bnode r t1 (insert_in_searchtree n t2)
  end
end.

Fixpoint max_elem (t:Zbtree) : option Z :=
  match t with
  | leaf => None
  | bnode r _ leaf => Some r 
  | bnode _ _ t2 => max_elem t2
  end.

Fixpoint delete_from_searchtree (n:Z) (t:Zbtree) : Zbtree :=
  match t with
  | leaf => leaf 
  | bnode r t1 t2 => match Z.compare n r with
                     | Lt => bnode r (delete_from_searchtree n t1) t2
                     | Gt => bnode r t1 (delete_from_searchtree n t2)
                     | Eq => match t1, t2 with
                             | leaf, _ => t2
                             | _, leaf => t1
                             | _, _ => match max_elem t1 with 
                                       | Some max_t1 => bnode max_t1 (delete_from_searchtree max_t1 t1) t2
                                       | None => t (* Unreachable case *)
                                       end
                             end
                     end
  end.


Definition list_to_searchtree l :=
List.fold_right insert_in_searchtree leaf l.

Definition weak_sort l := 
  infix_list (list_to_searchtree l).

Compute weak_sort (4::6::9::3::8::nil)%Z.

Definition list_to_searchtree_test l : bool :=
 is_searchtree (list_to_searchtree l).

Compute is_searchtree 
  (bnode  8 
          (bnode 5 (bnode 3 leaf leaf)
                   (bnode 7 leaf leaf))
          (bnode 15 (bnode 10 leaf leaf)
                    (bnode 18 leaf leaf)))%Z.

Compute is_searchtree 
  (bnode  8 
          (bnode 5 (bnode 3 leaf leaf)
                   (bnode 7 leaf leaf))
          (bnode 15 (bnode 16 leaf leaf)
                    (bnode 18 leaf leaf)))%Z.

Compute delete_from_searchtree 10 (bnode 8 (bnode 5 leaf (bnode 6 leaf leaf)) (bnode 10 leaf (bnode 15 leaf leaf))).
(* Expected result: bnode 8 (bnode 5 leaf (bnode 6 leaf leaf)) (bnode 15 leaf leaf) *)

Compute delete_from_searchtree 5 (bnode 8 (bnode 5 leaf (bnode 6 leaf leaf)) (bnode 10 leaf (bnode 15 leaf leaf))).
(* Expected result: bnode 8 (bnode 6 leaf leaf) (bnode 10 leaf (bnode 15 leaf leaf)) *)

