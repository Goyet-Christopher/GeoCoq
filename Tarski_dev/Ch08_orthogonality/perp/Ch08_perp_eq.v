Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_perpat.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_per.

Section Perp_eq.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l8_18_uniqueness : forall A B C X Y,
  ~ Col A B C -> Col A B X -> Perp A B C X
 -> Col A B Y -> Perp A B C Y -> X=Y.
Proof.
    intros.
    apply not_col_distincts in H.
    spliter.
    assert (Perp_at X A B C X).
      apply l8_15_1; assumption.
    assert (Perp_at Y A B C Y).
      apply l8_15_1;assumption.
    apply perpat_to_def in H7.
    apply perpat_to_def in H8.
    spliter.
    apply per_equality_2 with C.
      apply per_symmetry. apply H16. apply col_312. assumption. apply col_trivial_112.
      apply per_symmetry. apply H12. apply col_312. assumption. apply col_trivial_112.
Qed.


End Perp_eq.

Print All.
