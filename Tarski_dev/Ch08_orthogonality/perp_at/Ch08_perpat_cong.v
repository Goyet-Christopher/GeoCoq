Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_per.

Section Perpat_cong.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma mid_cong_perpat_3 : forall A B C D X C',
  Perp_at X A B C D -> Midpoint X C C' -> Cong A C A C'.
Proof.
    intros.
    apply per_mid_cong_3 with X.
      apply perpat_per_13 with B D. assumption.
      assumption.
Qed.

Lemma mid_cong_perpat_1 : forall A B C D X A',
  Perp_at X A B C D -> Midpoint X A A' -> Cong C A C A'.
Proof.
    intros.
    apply per_mid_cong_1 with X.
      apply perpat_per_13 with B D. assumption.
      assumption.
Qed.

End Perpat_cong.

Print All.
