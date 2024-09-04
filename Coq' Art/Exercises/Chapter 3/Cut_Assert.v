Section cutex.
 Variables P Q R T : Prop.
 Hypothesis H : P -> Q.
 Hypothesis H0 : Q -> R. 
 Hypothesis H1 : (P -> R) -> T -> Q.
 Hypothesis H2 : (P -> R) -> T.


 Lemma Q0 : Q.
 Proof.
  apply H1.
  - intro p. apply H0. apply H. assumption.
  - apply H2. intro p. apply H in p as q. apply H0 in q as r. assumption.
 Qed.

 Lemma Q1 : Q.
 Proof.
   info_auto.
 Qed.

 Lemma Q2 : Q.
 Proof.
   cut (P -> R).
   - intro H3. cut T.
     + intro t. apply H1 in H3 as H4; assumption.
     + apply H2 in H3 as t. assumption.
   - intro p. auto.
 Qed.

 Lemma Q3 : Q.
 Proof.
   assert (H3 : P -> R).
   - intro. apply H0. apply H. assumption.
   - assert (H4 : T); auto.
 Qed.

 Print Q0.
End cutex.


