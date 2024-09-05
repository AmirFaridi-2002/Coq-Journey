Theorem not_False : ~False.
Proof.
 unfold not. trivial.
Qed.

Definition not_False' : ~False := fun H => H.

Theorem triplet_neg : forall P:Prop, ~ ~ ~ P -> ~ P.
Proof.
  info_auto.
Qed.

Theorem LEM : forall P:Prop, ~P \/ P. Proof. auto. Abort.
Require Import Coq.Logic.Classical_Prop.
Check classic.

Lemma or_comm : forall A B: Prop, A \/ B <-> B \/ A.
Proof.
  intros A B.
  split.
  - intros [HA | HB].
    + right. assumption.
    + left. assumption.
  - intros [HB | HA].
    + right. assumption.
    + left. assumption.
Qed.


Theorem LEM : forall P:Prop, ~P \/ P.
Proof.
  intros. apply or_comm. apply classic.
Qed.

Theorem P3PQ : forall P Q : Prop, ~ ~ ~ P -> P -> Q.
Proof.
  tauto.
Qed.

Theorem P3PQ' : forall P Q : Prop, ~ ~ ~ P -> P -> Q.
Proof.
  intros P Q H1 H2. apply triplet_neg in H1. exfalso. contradiction.
Qed.

Theorem contrap : forall P Q : Prop, (P->Q) -> ~Q -> ~P.
Proof.
  intros P Q H1 H2. unfold not. intro HP. apply H1 in HP. contradiction.
Qed.

Lemma and_assos : forall A B C : Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  intros A B C [a [b c]]. split. split. assumption. assumption. assumption.
Qed.

Lemma and_assos' : forall A B C : Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof. 
  intros A B C [a [b c]]. repeat split; assumption.
Qed.

Lemma and_imp_dist : forall A B C D : Prop, (A -> B) /\ (C -> D) -> A /\ C -> B /\ D.
Proof.
  intros. destruct H. destruct H0. apply H in H0. apply H1 in H2.
  split; assumption.
Qed.

Lemma or_and_not : forall A B : Prop, (A \/ B) /\ ~A -> B.
Proof.
  intros. destruct H as [H1 H2]. destruct H1 as [HA | HB]; [contradiction | assumption].
Qed.

Definition my_false : Prop := forall P:Prop, P.
Definition my_not (P:Prop) : Prop := P -> my_false.

Theorem not_false : my_not my_false.
Proof.
  intro H. assumption.
Qed.

Theorem triple_neg : forall P:Prop, my_not (my_not (my_not P)) -> my_not P.
Proof.
 unfold my_not; auto.
Qed.


Theorem P3PQ'' : forall P Q:Prop, my_not (my_not (my_not P)) -> P -> Q.
Proof.
 intros P Q H p; apply (triple_neg _ H p).
Qed.

Theorem contrap'' : forall P Q:Prop, (P -> Q) -> my_not Q -> my_not P.
Proof.
 unfold my_not at 2; auto. 
Qed.


Theorem imp_absurd : forall P Q R:Prop, (P -> Q) -> (P -> my_not Q) -> P -> R.
Proof.
 intros P Q R H H0 p; apply (H0 p); auto. 
Qed.



Definition my_and (P Q:Prop) : Prop := forall R:Prop, (P -> Q -> R) -> R.

Definition my_or (P Q:Prop) : Prop :=
  forall R:Prop, (P -> R) -> (Q -> R) -> R.

Definition my_ex (A:Type) (P:A -> Prop) : Prop :=
  forall R:Prop, (forall x:A, P x -> R) -> R.


Theorem my_and_left : forall P Q:Prop, my_and P Q -> P.
Proof.
 intros P Q H; apply H; auto.
Qed.

Theorem my_and_right : forall P Q:Prop, my_and P Q -> Q.
Proof.
 intros P Q H; apply H; auto.
Qed.

Theorem my_and_ind : forall P Q R:Prop, (P -> Q -> R) -> my_and P Q -> R.
Proof.
  intros P Q R H H0; apply H0; assumption.
Qed.


Theorem my_or_introl : forall P Q:Prop, P -> my_or P Q.
Proof.
  unfold my_or; auto.  
Qed.

Theorem my_or_intror : forall P Q:Prop, Q -> my_or P Q.
Proof.
  unfold my_or; auto.  
Qed.

Theorem my_or_ind : forall P Q R:Prop, (P -> R) -> (Q -> R) -> my_or P Q -> R.
Proof.
  intros P Q R H H0 H1; apply H1; assumption.
Qed.

Theorem my_or_False : forall P:Prop, my_or P my_false -> P.
Proof.
 unfold my_false; intros P H; apply H; intro H0; apply H0.
Qed.

Theorem my_or_comm : forall P Q:Prop, my_or P Q -> my_or Q P.
Proof.
 intros P Q H; apply H; intros H0 R; auto.
Qed.


Theorem my_ex_intro : forall (A:Type) (P:A -> Prop) (a:A), P a -> my_ex A P.
Proof.
 intros A P a Ha R H; eapply H; eauto.
Qed.

Theorem my_not_ex_all :
 forall (A:Type) (P:A -> Prop), my_not (my_ex A P) -> forall a:A, my_not (P a).
Proof.
 intros A P H a H';
 apply H; eapply my_ex_intro; eauto.
Qed.




Theorem my_ex_ex : forall (A:Type) (P:A -> Prop), my_ex A P -> ex P.
Proof.
 intros A P H; apply H.
 intros x Hx; exists x; assumption.
Qed.



Theorem ex_my_ex : forall (A:Type) (P:A -> Prop), ex P -> my_ex _ P.
Proof.
 intros A P H; elim H; intros x Hx R.
 intros H0; eapply H0; eapply Hx.
Qed.
