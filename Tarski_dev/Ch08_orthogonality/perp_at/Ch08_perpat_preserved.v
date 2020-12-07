Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_per.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_diff.

Section Perpat_preserved.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cong3_preserves_perpat : forall X A B C D X' A' B' C' D',
 Perp_at X A B C D -> Cong_3 A X C A' X' C'
 -> Col X' A' B' -> Col X' C' D' -> A'<>X' \/ A<>X -> C'<>X' \/ C<>X
 -> A'<> B' -> C'<>D' -> Perp_at X' A' B' C' D'.
Proof.
    intros.
    assert(A <> B /\ C <> D).
      apply perpat_diff_1234 with X. assumption.
      spliter.
    assert(Per A X C).
      apply perpat_per_13 with B D. assumption.
    assert(Per A' X' C').
      apply cong3_preserves_per with A X C; assumption.
    assert(A' <> X').
      induction H3. assumption.
        apply cong_diff_12_34 with A X. assumption.
        apply cong3_1245 with C C'. assumption.
    assert(C' <> X').
      induction H4. assumption.
        apply cong_diff_12_34 with C X. assumption.
        apply cong3_3265 with A A'. assumption.
    apply l8_13; assumption.
Qed.

Lemma symmetry_preserves_perpat : forall Z X A B C D X' A' B' C' D',
 Perp_at X A B C D -> Midpoint Z A A' -> Midpoint Z B B'
 -> Midpoint Z C C' -> Midpoint Z D D'-> Midpoint Z X X'
 -> Perp_at X' A' B' C' D'.
Proof.
    intros.
    assert( A <> B /\ C <> D /\ (A <> X \/ B <> X) /\ (C <> X \/ D <> X)).
      apply perpat_distincts. assumption.
      spliter.
    assert(A'<>B').
      apply symmetry_preserves_diff with Z A B; assumption.
    assert(C'<>D').
      apply symmetry_preserves_diff with Z C D; assumption.
    assert(A' <> X' \/ B' <> X').
      induction H7.
        left. apply symmetry_preserves_diff with Z A X; assumption.
        right. apply symmetry_preserves_diff with Z B X; assumption.
    assert(C' <> X' \/ D' <> X').
      induction H8.
        left. apply symmetry_preserves_diff with Z C X; assumption.
        right. apply symmetry_preserves_diff with Z D X; assumption.
    assert(Per A X C).
      apply perpat_per_13 with B D. assumption.
    assert(Per A' X' C').
      apply symmetry_preserves_per with Z A X C; assumption.
    assert(Col X A B /\ Col X C D).
      apply perpat_col. assumption. spliter.
    assert(Col X' A' B').
      apply symmetry_preserves_col with X A B Z; assumption.
    assert(Col X' C' D').
      apply symmetry_preserves_col with X C D Z; assumption.
    induction H11.
      induction H12.
        apply l8_13; assumption.
        apply perpat_1243. apply l8_13; try assumption.
          apply not_eq_sym. assumption.
          apply col_132. assumption.
          apply symmetry_preserves_per with Z A X D; try assumption.
            apply perpat_per_14 with B C. assumption.
      apply not_eq_sym in H9.
      apply col_132 in H17.
      induction H12.
        apply perpat_2134. apply l8_13; try assumption.
          apply symmetry_preserves_per with Z B X C; try assumption.
            apply perpat_per_23 with A D. assumption.
        apply perpat_2143. apply l8_13; try assumption.
          apply not_eq_sym. assumption.
          apply col_132. assumption.
          apply symmetry_preserves_per with Z B X D; try assumption.
            apply perpat_per_24 with A C. assumption.
Qed.



End Perpat_preserved.

Print All.
