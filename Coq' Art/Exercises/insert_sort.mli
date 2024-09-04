
type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

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

module Pos :
 sig
  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison
 end

module Z :
 sig
  val compare : z -> z -> comparison
 end

val z_le_dec : z -> z -> sumbool

val z_le_gt_dec : z -> z -> sumbool

val insert : z -> z list -> z list

val sort : z list -> z list
