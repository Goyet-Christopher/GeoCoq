Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_per.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_col.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_diff.

Section Perpat_midpoint.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma mid_cong_not_col_perpat : forall A B M X,
  A <> B -> Midpoint M A B -> Cong X A X B
 -> ~ Col A B X -> Perp_at M X M A B.
Proof.
    intros.
    assert(Col M A B).
      apply midpoint_col_123. assumption.
    assert(Per X M A).
      apply mid_cong_per_3 with B; assumption.
    assert(X<>M).
      apply not_eq_sym.
      apply midpoint_cong_diff_2 with A B; assumption.
    assert(M<>A /\ M<>B).
      apply midpoint_distinct_1; assumption.
    spliter.
    apply l8_13; try assumption.
      apply not_eq_sym. assumption.
      apply col_trivial_121.
Qed.

Lemma cong_perpat_or_mid : forall A B M X,
 A <> B -> Midpoint M A B -> Cong X A X B
 -> X = M \/ ( ~Col A B X /\ Perp_at M X M A B).
Proof.
    intros.
    induction(col_dec A B X).
    (* Col A B X *)
      left.
      apply mid_cong_eq with A B; assumption.
    (* ~ Col A B X *)
      right.
      split.
        assumption.
        apply mid_cong_not_col_perpat; assumption.
Qed.

Lemma cong_perpat : forall A B M X,
 A <> B -> X <> M -> Midpoint M A B -> Cong X A X B
 -> ~Col A B X /\ Perp_at M X M A B.
Proof.
    intros.
    assert(X = M \/ ( ~Col A B X /\ Perp_at M X M A B)).
      apply cong_perpat_or_mid; assumption.
    induction H3.
      contradiction.
      assumption.
Qed.

Lemma cong_perpat_notcol : forall A B M X,
 ~Col A B X -> Midpoint M A B -> Cong X A X B
 -> Perp_at M X M A B.
Proof.
    intros.
    assert(~Col A X M /\ ~Col B X M).
      apply not_col_midpoint; assumption.
      spliter.
    apply not_col_distincts in H.
    apply not_col_distincts in H2.
      spliter.
    assert(X = M \/ ( ~Col A B X /\ Perp_at M X M A B)).
      apply cong_perpat_or_mid; assumption.
    induction H10.
      contradiction.
      spliter.
      assumption.
Qed.

Lemma perpat_cong_mid_3 : forall X A B C D,
  Cong C A C B -> Perp_at X A B C D -> Midpoint X A B.
Proof.
    intros.
    assert(A<>B).
      apply perpat_diff_12 with X C D. assumption.
    assert(Per A X C).
      apply perpat_per_13 with B D. assumption.
    assert(Per B X C).
      apply perpat_per_23 with A D. assumption.
    assert(A<>X \/ B<>X).
      apply perpat_diff_X12 with C D. assumption.
    assert(Col X A B /\ Col X C D).
      apply perpat_col. assumption.
      spliter.
    induction H4.
      apply per_cong_mid_1 with C; assumption.
    apply midpoint_symmetry.
      apply per_cong_mid_1 with C; try assumption.
        apply not_eq_sym. assumption.
        apply col_132. assumption.
        apply cong_3412. assumption.
Qed.

Lemma perpat_cong_mid_4 : forall X A B C D,
  Cong D A D B -> Perp_at X A B C D -> Midpoint X A B.
Proof.
    intros.
    apply perpat_1243 in H0.
    apply perpat_cong_mid_3 with D C; assumption.
Qed.

Lemma perpat_cong_mid_1 : forall X A B C D,
  Cong A C A D -> Perp_at X A B C D -> Midpoint X C D.
Proof.
    intros.
    apply perpat_3412 in H0.
    apply perpat_cong_mid_3 with A B; assumption.
Qed.

Lemma perpat_cong_mid_2 : forall X A B C D,
  Cong B C B D -> Perp_at X A B C D -> Midpoint X C D.
Proof.
    intros.
    apply perpat_3421 in H0.
    apply perpat_cong_mid_3 with B A; assumption.
Qed.

Lemma mid_tri_perpap : forall X A B C D C' C'' P,
 ~ Col A X C -> Perp_at X A B C D
 -> Midpoint A C C' -> Midpoint X C C'' -> Midpoint P C' C''
 -> Perp_at A A B A P.
Proof.
    intros.
    assert(Per A X C).
      apply perpat_per_13 with B D. assumption.
    assert(Per X A P).
      apply l8_20_1 with C C' C''; assumption.
    apply not_col_distincts in H. spliter.
    assert(C<> C'' /\ X <> C'').
      apply midpoint_distinct_2; assumption. spliter.
    assert(C<>C' /\ A <> C').
      apply midpoint_distinct_2; assumption. spliter.
    assert(A <> P).
      intro. subst P.
        apply H.
        apply col_transitivity_3 with C C''.
        assumption.
        apply col_321.
        apply col_transitivity_1 with C'. assumption.
          apply midpoint_col_123. assumption.
          apply midpoint_col_132. assumption.
        apply midpoint_col_231. assumption.
        apply col_trivial_121.
    assert(Perp_at A X A A P).
      apply per_perpat; try assumption.
        apply not_eq_sym. assumption.
    assert(Col X A B /\ Col X C D).
      apply perpat_col. assumption. spliter.
    apply perpat_col_perpat_2 with X.
      apply perpat_diff_12 with X C D. assumption.
      apply col_213. assumption.
      apply perpat_2134. assumption.
Qed.

End Perpat_midpoint.

Print All.
