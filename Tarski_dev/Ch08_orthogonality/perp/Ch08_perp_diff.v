Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp.

Section Perp_diff.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perp_distinct : forall A B C D,
 Perp A B C D -> A <> B /\ C <> D.
Proof.
    intros.
    exists_and H X.
    apply perpat_to_def in H0.
    spliter.
    split; assumption.
Qed.

Lemma perp_not_eq_1 : forall A B C D,
  Perp A B C D -> A<>B.
Proof.
    intros.
    assert(A <> B /\ C <> D).
      apply perp_distinct. assumption.
    spliter.
    assumption.
Qed.

Lemma perp_not_eq_2 : forall A B C D,
  Perp A B C D -> C<>D.
Proof.
    intros.
    assert(A <> B /\ C <> D).
      apply perp_distinct. assumption.
    spliter.
    assumption.
Qed.


End Perp_diff.

Print All.
