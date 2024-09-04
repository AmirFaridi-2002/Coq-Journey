
type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq
 end

module Z =
 struct
  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)
 end

(** val z_le_dec : z -> z -> sumbool **)

let z_le_dec x y =
  match Z.compare x y with
  | Gt -> Right
  | _ -> Left

(** val z_le_gt_dec : z -> z -> sumbool **)

let z_le_gt_dec =
  z_le_dec

(** val insert : z -> z list -> z list **)

let rec insert z0 = function
| Nil -> Cons (z0, Nil)
| Cons (a, l') ->
  (match z_le_gt_dec z0 a with
   | Left -> Cons (z0, (Cons (a, l')))
   | Right -> Cons (a, (insert z0 l')))

(** val sort : z list -> z list **)

let rec sort = function
| Nil -> Nil
| Cons (y, l0) -> insert y (sort l0)
