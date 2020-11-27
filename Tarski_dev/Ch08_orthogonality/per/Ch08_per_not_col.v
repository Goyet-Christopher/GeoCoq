Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_eq.

Section Per_not_col.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma per_not_col : forall A B C,
  A <> B -> B <> C -> Per A B C -> ~Col A B C.
Proof.
    intros.
    intro.
    exists_and H1 C'.
    assert (C = C' \/ Midpoint A C C').
      apply l7_20.
        apply col_transitivity_1 with B.
          apply diff_symmetry. assumption.
          apply col_321. assumption.
          apply bet_col_123. apply midpoint_bet1. assumption.
        assumption.
    induction H4.
      subst C'.
        assert(B = C).
          apply midpoint_identity_122. assumption.
        contradiction.
      assert(A = B).
          apply symmetry_same_center with C C'; assumption.
        contradiction.
Qed.

Lemma col_per2_cases : forall A B C D B', 
 B <> C -> B' <> C -> C <> D -> Col B C D
 -> Per A B C -> Per A B' C
 ->  B = B' \/ ~Col B' C D.
Proof.
    intros.
    induction(eq_dec_points B B').
      left. assumption.
    right.
      intro.
      assert(Col C B B').
        apply col_transitivity_1 with D.
          assumption. apply col_231. assumption.
          apply col_231. assumption.
      assert(Per A B' B).
        apply per_col_3 with C; try assumption.
          apply col_312. assumption.
      assert(Per A B B').
        apply per_col_3 with C; try assumption.
          apply col_213. assumption.
      apply H5.
      apply per_equality_2 with A; assumption.
Qed.

Lemma per_not_colp : forall A B P R,
  A <> B -> A <> P -> B <> R
 -> Per B A P -> Per A B R -> ~Col P A R.
Proof.
    intros.
    intro.
    assert (Per B A R).
      apply per_col_3 with P; try assumption.
        apply col_213. assumption.
    assert (A = B).
      apply per_equality_2 with R.
        apply per_symmetry. assumption.
        apply per_symmetry. assumption.
    contradiction.
Qed.

Lemma per_not_col_2 : forall A X P P',
  P<>P' -> P<>A -> X <> A -> Col P A P' -> Per P A X -> ~ Col X P P'.
Proof.
    intros.
    intro.
    assert(Col P A X).
      apply col_transitivity_1 with P'.
        assumption.
        apply col_132. assumption.
        apply col_231. assumption.
    assert (P = A \/ A = X).
      apply per_identity_2; assumption.
    induction H6.
      subst. contradiction.
      subst. contradiction.
Qed.

End Per_not_col.

Print All.
