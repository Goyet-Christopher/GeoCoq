Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_exists.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_col.

Section Perpat_per.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perpat_per : forall A B C,
 Perp_at B A B B C-> Per A B C.
Proof.
    intros.
    apply perpat_to_def in H.
    spliter.
    apply H3.
      apply col_trivial_112.
      apply col_trivial_121.
Qed.

Lemma per_perpat : forall A B C,
 A <> B -> B <> C -> Per A B C -> Perp_at B A B B C.
Proof.
    intros.
    apply def_to_perpat; try assumption.
      apply col_trivial_121.
      apply col_trivial_112.
    intros.
    apply col_col_per_per with A C; try assumption.
      apply col_132. assumption.
Qed.

End Perpat_per.

Print All.
