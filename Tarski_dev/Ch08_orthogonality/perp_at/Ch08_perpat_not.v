Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_eq.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_diff.

Section Perpat_not.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma not_perpat : forall X A B, 
  ~ Perp_at X A B A B.
Proof.
    intros.
    intro.
    assert(A <> B).
      apply perpat_diff_12 with X A B.
        assumption.
    assert (X = A).
      apply perpat_identity_13 with B B.
        assumption.
    subst A.
    assert (X = B).
      apply perpat_identity_24 with X X.
        assumption.
    subst.
    contradiction.
Qed.

Lemma not_perpat_12 : forall X A C D, 
  ~ Perp_at X A A C D.
Proof.
    intros.
    intro.
    assert(A <> A).
      apply perpat_diff_12 with X C D.
        assumption.
    contradiction.
Qed.

Lemma not_perpat_34 : forall X A B C, 
  ~ Perp_at X A B C C.
Proof.
    intros.
    assert(~ Perp_at X C C A B).
      apply not_perpat_12.
    intro.
    apply H.
    apply perpat_3412. assumption.
Qed.

Lemma perpat_not_col_13 : forall X A B C D,
  A<>X -> C<>X -> Perp_at X A B C D -> ~ Col A X C.
Proof.
    intros.
    assert (Per A X C).
       apply perpat_per_13 with B D. assumption.
    apply per_not_col; try assumption.
       apply not_eq_sym. assumption.
Qed.

Lemma perpat_not_col : forall X A C,
  Perp_at X A X C X -> ~ Col A X C.
Proof.
    intros.
    assert(A<>X /\ C<>X).
      apply perpat_diff_1234 with X. assumption.
      spliter.
    assert (Per A X C).
       apply perpat_per_13 with X X. assumption.
    apply per_not_col; try assumption.
       apply not_eq_sym. assumption.
Qed.


End Perpat_not.

Print All.

