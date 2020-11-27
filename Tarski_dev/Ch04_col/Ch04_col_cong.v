Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_FSC_cons.

Section Col_cong.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l4_17 : forall A B C P Q,
  A<>B -> Col A B C 
  -> Cong A P A Q -> Cong B P B Q 
  -> Cong C P C Q.
Proof.
    intros.
    assert (FSC A B C P A B C Q).
      induction H0.
        apply OFSC_to_FSC_1.
        apply OFSC_same_base; assumption.
      induction H0.
        apply IFSC_to_FSC.
        apply IFSC_same_base; assumption.
      apply OFSC_to_FSC_2.
      apply OFSC_same_base; assumption.
    apply l4_16 with A B A B.
      assumption.
      left. assumption.
Qed.

End Col_cong.

Print All.
