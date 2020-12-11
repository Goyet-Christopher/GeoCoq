Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_perpat.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_diff.

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

Lemma not_perp_12 : forall A C D,
  ~ Perp A A C D.
Proof.
    intros.
    intro.
    exists_and H X.
    assert(~ Perp_at X A A C D).
      apply not_perpat_12.
    contradiction.
Qed.

Lemma not_perp_34 : forall A B C,
  ~ Perp A B C C.
Proof.
    intros.
    intro.
    exists_and H X.
    assert(~ Perp_at X A B C C).
      apply not_perpat_34.
    contradiction.
Qed.


End Perp_not.

Print All.