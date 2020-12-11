Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_per.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_perpat.

Section Perp_not_col.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perp_not_col : forall A B C,
  Perp A B C A -> ~ Col A B C.
Proof.
    intros.
    assert (Perp_at A A B C A).
      apply perp_perpat_14. assumption.
    apply not_col_213.
    apply perpat_not_col.
      apply perpat_2134. assumption.
Qed.

Lemma perp_not_col2 : forall A B C D,
  Perp A B C D -> ~ Col A B C \/ ~ Col A B D.
Proof.
    intros.
    induction (col_dec A B C).
      right.
      assert(Perp_at C A B C D).
        apply l8_14_2_1b_bis.
          assumption.
          apply col_312. assumption.
          apply col_trivial_112.
      intro.
      assert(Perp_at D A B C D).
        apply l8_14_2_1b_bis.
          assumption.
          apply col_312. assumption.
          apply col_trivial_121.
      assert(C = D).
        apply l8_14_3 with A B C D; assumption.
      apply perp_not_eq_2 in H.
      contradiction.
    left.
    assumption.
Qed.

End Perp_not_col.

Print All.

