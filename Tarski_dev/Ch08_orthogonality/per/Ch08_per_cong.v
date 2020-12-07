Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_eq.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_diff.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_not_col.


Section Per_cong.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma per_per_cong : forall A B C A',
  Per A B C -> Per A' B C -> Cong C A C A' -> Cong B A B A'.
Proof.
    intros.
    apply per_exists_3 in H.
    exists_and H C'.
    apply per_exists_3 in H0.
    exists_and H0 C''.
    assert (C' = C'').
      apply symmetric_point_uniqueness with B C; assumption.
    subst C''.
    apply l4_17_IFSC with C C'.
      apply midpoint_bet1. assumption.
      assumption.
      apply cong_XY21_XY34 with A C.
        assumption.
        apply cong_21XY_YX43 with C A'; assumption.
Qed.

Lemma per_mid_cong_1 : forall A B C A',
  Per A B C -> Midpoint B A A' -> Cong C A C A'.
Proof.
    intros.
    apply per_symmetry in H.
    exists_and H A''.
    assert (A' = A'').
      apply symmetric_point_uniqueness with B A; assumption.
    subst A''.
    assumption.
Qed.

Lemma per_mid_cong_3 : forall A B C C',
  Per A B C -> Midpoint B C C' -> Cong A C A C'.
Proof.
    intros.
    exists_and H C''.
    assert (C' = C'').
      apply symmetric_point_uniqueness with B C; assumption.
    subst C''.
    assumption.
Qed.

Lemma per_cong : forall A B P R X ,
  A <> B -> A <> P ->
  Per B A P -> Per A B R ->
  Cong A P B R -> Col A B X -> Bet P X R ->
  Cong A R P B.
Proof.
    intros.
    symmetric P' A P.
    prolong P' X R' X R.
    assert (exists M, Midpoint M R R').
      apply l7_25 with X. assumption.
      exists_and H9 M.
    assert (B <> R).
      apply cong_diff_12_34 with A P; assumption.
    assert (Per P A X).
      apply per_col_3 with B; try assumption.
        apply per_symmetry. assumption.
    assert (Per X B R).
      apply per_col_1 with A; try assumption.
        apply col_213. assumption.
    assert(~Col P A R /\ P <> A /\ A <> R /\ P <> R).
      apply not_col_distincts.
      apply per_not_colp with B; assumption.
      spliter.
    assert (X <> A).
      apply col_not_col_diff with P R.
        apply bet_col_132. assumption.
        apply not_col_132. assumption.
    assert (Per X M R).
      apply mid_cong_per_3 with R'; assumption.
    assert (P <> P' /\ A<>P').
      apply midpoint_distinct_2; assumption.
      spliter.
    assert(~Col X P P') as H'.
      apply per_not_col_2 with A; try assumption.
        apply midpoint_col_213. assumption.
    assert (R <> X).
      intro.
      subst X. assert(R=R').
        apply cong_reverse_identity with R. assumption.
      subst R'. assert(M=R).
        apply midpoint_identity_122. assumption.
      subst M. assert(R=B).
        apply per_identity. assumption.
      subst R. assert(A=P).
        apply cong_identity with B. assumption.
      subst A. assert(P=P').
        apply midpoint_identity_112. assumption.
      subst P'.
      contradiction.
    assert (X <> R').
      intro.
      subst R'. assert(X=R).
        apply cong_identity with X. assumption.
      subst X. contradiction.
    assert (M <> X).
      intro.
      subst M.
      apply H'.
      apply col_transitivity_1 with R.
        apply not_eq_sym. assumption.
        apply bet_col_312. assumption.
      apply col_transitivity_1 with R'.
        assumption.
        apply midpoint_col_132. assumption.
        apply bet_col_312. assumption.
    assert (Cong X P X P').
      apply per_mid_cong_3 with A.
        apply per_symmetry. assumption. assumption.
    assert (Bet A X M).
      apply l7_22 with P R P' R'; assumption.
    assert(Col B X M).
      apply l6_16_a with A.
        assumption.
        apply between_symmetry. assumption.
        apply col_231. assumption.
    assert(Col B A M).
      apply l6_16_b with X.
        apply not_eq_sym. assumption.
        apply between_symmetry. assumption.
        apply col_213. assumption.
    assert (B = M).
      apply per_equality_4 with A X R; try assumption.
        apply not_eq_sym. assumption.
        apply col_213. assumption.
        apply col_213. assumption.
    subst M.
    assert (Cong P R' P' R).
      eapply OFSC_isosceles with X; assumption.
    assert (Bet P' A P).
        apply midpoint_bet2. assumption.
    assert(Bet R' B R).
        apply midpoint_bet2. assumption.
    assert(Cong P' P R' R).
        apply l2_11 with A B; try assumption.
          apply cong_XY21_YX43 with P A.
            apply midpoint_cong_2113. assumption.
            apply cong_12XY_YX34 with B R. assumption.
              apply midpoint_cong_2113. assumption.
    assert (IFSC P' A P R R' B R P).
      apply def_to_IFSC; try assumption.
        apply cong_3421. assumption.
        apply cong_1221.
    apply cong_1243.
    apply IFSC_cong_24 with P' P R' R. assumption.
Qed.


Lemma l8_22 : forall A B P R X ,
 A <> B -> A <> P ->
 Per B A P -> Per A B R ->
 Cong A P B R -> Col A B X -> Bet P X R ->
 Cong A R P B /\ Midpoint X A B /\ Midpoint X P R.
Proof.
    intros.
    assert (Cong A R P B).
      apply (per_cong A B P R X); assumption.
    split.
      assumption.
    assert (~ Col B A P).
      apply per_not_col; try assumption.
        apply not_eq_sym. assumption.
    apply l7_21.
      apply not_col_231. assumption.
      apply diff_per2 with B A; try assumption.
        apply not_eq_sym. assumption.
      assumption.
      apply cong_3421. assumption.
      apply col_132. assumption.
      apply bet_col_123. assumption.
Qed.


End Per_cong.

Print All.


