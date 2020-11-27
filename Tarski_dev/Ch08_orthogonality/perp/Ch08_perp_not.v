Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_eq.

Section Perp_not.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l8_14_1 : forall A B, 
  ~ Perp A B A B.
Proof.
    intros.
    intro.
    exists_and H X.
    apply perpat_to_def in H0.
    spliter.
    assert (Per A X A).
      apply H3; apply col_trivial_112.
    assert (A = X).
      apply per_equality_2 with A.
        apply per_trivial_112.
        assumption.
    subst A.
    assert (Per B X B).
      apply H3; apply col_trivial_121.
    assert (B = X).
      apply per_equality_2 with B.
        apply per_trivial_112.
        assumption.
    subst.
    contradiction.
Qed.


End Perp_not.

Print All.
