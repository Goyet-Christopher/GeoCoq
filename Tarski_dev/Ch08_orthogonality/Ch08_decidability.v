Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.Ch08_per.

Section T8_1.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma Per_dec : forall A B C, Per A B C \/ ~ Per A B C.
Proof.
    intros.
    unfold Per.
    elim (symmetric_point_construction C B);intros C' HC'.
    elim (Cong_dec A C A C');intro.
      left.
      exists C'.
      intuition.
    right.
    intro.
    decompose [ex and] H0;clear H0.
    assert (C'=x) by (apply symmetric_point_uniqueness with C B;assumption).
    subst.
    intuition.
Qed.

Lemma Perp_in_dec : forall X A B C D,
 Perp_at X A B C D \/ ~ Perp_at X A B C D.
Proof.
    intros.
    unfold Perp_at.
    elim (eq_dec_points A B);intro; elim (eq_dec_points C D);intro; elim (Col_dec X A B);intro; elim (Col_dec X C D);intro; try tauto.
    elim (eq_dec_points B X);intro; elim (eq_dec_points D X);intro;subst;treat_equalities.
      elim (Per_dec A X C);intro.
        left;repeat split;Col;intros; apply col_col_per_per with A C;Col.
      right;intro;spliter;apply H3;apply H8;Col.
      elim (Per_dec A X D);intro.
        left;repeat split;Col;intros; apply col_col_per_per with A D;Col;ColR.
      right;intro;spliter;apply H3;apply H9;Col.
      elim (Per_dec B X C);intro.
        left;repeat split;Col;intros; apply col_col_per_per with B C;Col;ColR.
      right;intro;spliter;apply H4;apply H9;Col.
    elim (Per_dec B X D);intro.
      left;repeat split;Col;intros; apply col_col_per_per with B D;Col;ColR.
    right;intro;spliter;apply H5;apply H10;Col.
Qed.

End T8_1.

Print All.
