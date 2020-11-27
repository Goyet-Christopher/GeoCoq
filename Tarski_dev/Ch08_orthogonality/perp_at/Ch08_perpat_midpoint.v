Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_per.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_col.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_exists.

Section Perpat_midpoint.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cong_perp_or_mid : forall A B M X,
 A <> B -> Midpoint M A B -> Cong X A X B
 -> X = M \/ ( ~Col A B X /\ Perp_at M X M A B).
Proof.
    intros.
    induction(Col_dec A B X).
    (* Col A B X *)
      left.
      assert(A = B \/ Midpoint X A B).
        apply l7_20.
          apply col_132. assumption.
          assumption.
      induction H3.
        contradiction.
        apply (symmetry_same_center A B); assumption.
    (* ~ Col A B X *)
      right.
      split.
        assumption.
        assert(Col M A B).
          apply midpoint_col_123. assumption.
      assert(Per X M A).
        apply exists_per_3. exists B.
        split; assumption.
      apply perpat_col_perpat_4 with M.
        assumption.
        apply col_213. assumption.
      apply perpat_1243.
      assert(M<>A /\ M<>B).
        apply midpoint_distinct_1; assumption.
      spliter.
      apply per_perpat; try assumption.
        apply diff_symmetry.
        apply midpoint_cong_diff_2 with A B; assumption.
Qed.

End Perpat_midpoint.

Print All.
