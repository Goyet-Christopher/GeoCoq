Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_perpat.

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
    apply perpat_equality_2 with A B C; try assumption.
      apply col_312. assumption.
      apply col_312. assumption.
Qed.


End Perp_eq.

Print All.