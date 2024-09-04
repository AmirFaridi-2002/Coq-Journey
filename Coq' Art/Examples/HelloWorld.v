From Coq Require Import Arith Bool.

Check 3.
Check 3+4.
Check true.
Check True.
Check (true && false).

Eval compute in 3+4.
Eval compute in (true && false).
(* Eval compute in (True && False). *)

(* No side effects in Coq since it's a pure functional. So no printing, scanning, or reading from a file. *)
Fail Check Print.
Print bool.

Definition inc (n : nat) : nat := n + 1.
Eval compute in inc 4.
Print nat.

Inductive week_day := 
    | Monday : week_day
    | Tuesday : week_day
    | Wednesday : week_day
    | Thursday : week_day
    | Friday : week_day
    | Saturday : week_day
    | Sunday : week_day.

Definition is_monday (w : week_day) : bool := 
    match w with
    | Monday => true
    | _ => false
    end.

Check is_monday.
Eval compute in is_monday Monday.


(* We can define types which may be recursive, e.g. the type of lists *)
Inductive week_day_list :=
    | Nil : week_day_list
    | Cons : week_day -> week_day_list -> week_day_list.

Check (Cons Monday Nil).

Definition head (l : week_day_list) (default : week_day) : week_day := 
    match l with 
    | Nil => default
    | Cons v _ => v
    end.
Check (head).

Check (Cons).
Check (Cons Monday).
Eval compute in head (Cons Saturday (Cons Sunday (Cons Saturday Nil))).

Definition tail (l : week_day_list) : week_day_list :=
    match l with
    | Nil => Nil
    | Cons v rest => rest
    end.

Eval compute in tail (Cons Saturday (Cons Sunday (Cons Saturday Nil))).

Notation "[]" := Nil.
Notation "[ w ]" := (Cons w Nil).
Notation "[ w1 ; w2 ; .. ; wn ]" := (Cons w1 (Cons w2 .. (Cons wn Nil) .. )).

Definition work_week := [Monday; Tuesday; Wednesday; Thursday; Friday].
Eval compute in tail work_week.

Fixpoint len (l : week_day_list) : nat :=
    match l with 
    | [] => 0
    | Cons w rest => 1 + (len rest)
    end.

Eval compute in len (work_week).

Fixpoint is_member (w : week_day) (l : week_day_list) : bool :=
  match l with
  | [] => false
  | Cons h t => 
      match w, h with
      | Monday, Monday => true
      | Tuesday, Tuesday => true
      | Wednesday, Wednesday => true
      | Thursday, Thursday => true
      | Friday, Friday => true
      | Saturday, Saturday => true
      | Sunday, Sunday => true
      | _, _ => is_member w t  (* Continue searching in the tail *)
      end
  end.


Eval compute in is_member Monday work_week.
Eval compute in is_member Saturday work_week.

Check forall w, w = Monday.
Check exists w, w = Monday.
Check exists l : week_day_list, l = [] \/ l = [].
Check exists l : week_day_list, l = [] /\ l = [].

Check (forall l : week_day_list, l = [] \/ exists w l', l = Cons w l').


Lemma lemma_1 : forall x y : week_day, x = y -> x = y.
Proof.
    intros. apply H.
Qed.
Check lemma_1.

Lemma lemma_2 : Monday = Monday.
Proof.
    intros. reflexivity.
Qed.

Lemma lemma_3 : Monday = Friday.
Proof. 
    Fail reflexivity.
Abort.

Lemma lemma_4 : ~ Monday = Friday.
Proof.
    unfold not. intros H. discriminate.
Qed.
    

Definition ret_monday (w : week_day) : week_day := Monday.
Eval compute in ret_monday Friday.

Lemma lemma_5 : ret_monday Friday = Monday.
Proof.
    compute. reflexivity.
Qed.

Lemma lemma_6 : len work_week = 5.
Proof.
    compute. reflexivity.
Qed.

Lemma lemma_7 : forall w : week_day, ret_monday w = Monday.
Proof.
    intros. compute. reflexivity.
Qed.

Lemma lemma_8 : forall x y z : week_day, x = y -> y = z -> x = y /\ y = z.
Proof.
    intros. split.
    - apply H.
    - apply H0.
Qed.

Lemma lemma_8' : forall x y z : week_day, x = y -> y = z -> x = y /\ y = z.
Proof. 
    intros. split. (apply H || apply H0). (apply H || apply H0).
Qed.

Lemma lemma_9 : forall x y z : week_day, x = y -> x = y \/ y = z.
Proof.
    intros. left. apply H.
Qed.

Lemma lemma_10 : forall x y z : week_day, x = y /\ y = z -> y = z.
Proof.
    intros. destruct H. apply H0. (* alternative: destruct H as [H1 H2]. *)
Qed.

Lemma lemma_11 : forall x y z : week_day, x = y \/ x = z -> x = z \/ x = y.
Proof.
    intros. destruct H.
    - right. apply H.
    - left. apply H.
Qed.

Lemma lemma_12 : forall x y, x = Monday -> y = x -> y = Monday.
Proof.
    intros. rewrite H0. rewrite H. trivial.
Qed.

Lemma lemma_13 : Monday = Tuesday -> False.
Proof.
    intros. (* discriminate. *) inversion H.
Qed.





    
