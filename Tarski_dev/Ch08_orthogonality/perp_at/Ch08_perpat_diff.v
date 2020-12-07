Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_per.

Section Perpat_diff.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perpat_diff_12 : forall X A B C D,
  Perp_at X A B C D -> A <> B.
Proof.
    intros.
    assert(A <> B /\ C <> D).
      apply perpat_diff_1234 with X. assumption.
      spliter.
    assumption.
Qed.

Lemma perpat_diff_34 : forall X A B C D,
  Perp_at X A B C D -> C <> D.
Proof.
    intros.
    assert(A <> B /\ C <> D).
      apply perpat_diff_1234 with X. assumption.
      spliter.
    assumption.
Qed.

Lemma perpat_diff_X12 : forall X A B C D,
  Perp_at X A B C D -> A <> X \/ B <> X.
Proof.
    intros.
    assert(A <> B /\ C <> D).
      apply perpat_diff_1234 with X. assumption.
      spliter.
    induction(eq_dec_points A X).
      right. subst. apply not_eq_sym. assumption.
      left. assumption.
Qed.

Lemma perpat_diff_X34 : forall X A B C D,
  Perp_at X A B C D -> C <> X \/ D <> X.
Proof.
    intros.
    apply perpat_diff_X12 with A B.
    apply perpat_symmetry.
      assumption.
Qed.

Lemma perpat_distincts : forall X A B C D,
  Perp_at X A B C D -> A <> B /\ C <> D /\ (A <> X \/ B <> X) /\ (C <> X \/ D <> X).
Proof.
    intros.
    repeat split.
      apply perpat_diff_12 with X C D. assumption.
      apply perpat_diff_34 with X A B. assumption.
      apply perpat_diff_X12 with C D. assumption.
      apply perpat_diff_X34 with A B. assumption.
Qed.

Lemma diff_perpat2 : forall A B C C',
  Perp_at A B A A C -> Perp_at B A B B C' -> C <> C'.
Proof.
    intros.
    assert(A<>B).
      apply perpat_diff_12 with B B C'. assumption.
    apply not_eq_sym.
    apply diff_per2 with A B.
      assumption.
      apply perpat_per_14 with B B. assumption.
      apply perpat_per_14 with A A. assumption.
Qed.


End Perpat_diff.

Print All.