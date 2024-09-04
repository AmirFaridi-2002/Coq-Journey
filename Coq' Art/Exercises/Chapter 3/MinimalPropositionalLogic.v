Section Minimal_Propositional_Logic.
  Variables P Q R T : Prop.

  Theorem imp_trans : (P->Q)->(Q->R)->P->R.
  Proof.
    intros. apply H in H1 as q. apply H0 in q as r. assumption.
  Qed.

  Theorem imp_trans' : (P->Q)->(Q->R)->P->R.
  Proof.
    info_auto.
  Qed.

  Theorem imp_trans_infoauto : (P->Q)->(Q->R)->P->R.
  Proof.
    intro. intro. intro. simple apply H0. simple apply H. assumption.
  Qed.
 
  Theorem delta : (P->P->Q)->P->Q.
  Proof fun (H : P->P->Q)(p : P) => H p p.

End Minimal_Propositional_Logic.
