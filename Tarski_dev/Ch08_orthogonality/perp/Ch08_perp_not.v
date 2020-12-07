Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp.

Section Perp_not.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l8_14_1 : forall A B, 
  ~ Perp A B A B.
Proof.
    intros.
    intro.
    exists_and H X.
    apply not_perpat with X A B.
      assumption.
Qed.


End Perp_not.

Print All.