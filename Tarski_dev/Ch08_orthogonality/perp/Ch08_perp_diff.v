Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_perpat.

Section Perp_diff.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perp_distinct : forall A B C D,
 Perp A B C D -> A <> B /\ C <> D.
Proof.
    intros.
    exists_and H X.
    apply perpat_diff_1234 with X.
    assumption.
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

Lemma diff_perp2 : forall A B C C',
  Perp B A A C -> Perp A B B C' -> C <> C'.
Proof.
    intros.
    apply diff_perpat2 with A B.
    apply perp_perpat_23. assumption.
    apply perp_perpat_23. assumption.
Qed.



End Perp_diff.

Print All.
