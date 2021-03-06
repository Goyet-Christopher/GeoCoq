Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_eq.

Section Per_diff.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma diff_per2 : forall A B C C',
  A<>B -> Per A B C -> Per B A C' -> C<>C'.
Proof.
    intros.
    intro.
    subst C'.
    assert(A = B).
      apply per_equality_2 with C.
        apply per_symmetry. assumption.
        apply per_symmetry. assumption.
    contradiction.
Qed.

End Per_diff.

Print All.



