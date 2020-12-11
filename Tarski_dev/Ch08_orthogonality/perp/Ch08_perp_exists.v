Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_col.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_perpat.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_per.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_cong.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_not_col.

Section Perp_exists.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perp_proj : forall A B C D,
 Perp A B C D -> ~Col A C D
 -> exists X, Col A B X /\ Perp A X C D.
Proof.
    intros.
    assert(H' := H).
    apply perp_to_def in H.
    exists_and H X.
    exists X.
    assert(A<>X).
      apply not_col_perpat_diff with B C D; assumption.
    assert(Col X A B /\ Col X C D).
      apply perpat_col. assumption. spliter.
      apply col_231 in H2.
    split.
      assumption.
      apply perp_col_2 with B; assumption.
Qed.

Lemma l8_18_existence : forall A B C,
 ~ Col A B C -> exists X, Col A B X /\ Perp A B C X.
Proof.
    intros.
    assert(exists X, Col A B X /\ Perp_at X A B C X).
      apply not_col_proj_12. assumption.
    exists_and H0 X.
    exists X.
    split.
      assumption.
      apply perpat_perp with X.
        assumption.
Qed.



Lemma l8_21_aux : forall A B C,
 ~ Col A B C -> exists P, exists T,
   Perp A B P A /\ Col A B T /\ Bet C T P.
Proof.
    intros.
    assert (exists X : Tpoint, Col A B X /\ Perp A B C X).
      apply l8_18_existence.
        assumption.
    exists_and H0 X.
    assert (Perp_at X A B C X).
      apply not_col_distincts in H. spliter.
      apply l8_15_1; assumption.
    assert(exists C', Midpoint X C C' /\ Cong A C A C').
      apply perpat_exists_31 with B X. assumption.
      exists_and H3 C'. spliter.
    symmetric C'' A C.
    assert (exists P, Midpoint P C' C'').
      apply l7_25 with A.
        apply cong_XY12_XY34 with A C.
          assumption.
          apply midpoint_cong_1213. assumption.
    exists_and H6 P.
    assert (C <> X).
      apply perp_not_eq_2 with A B. assumption.
    assert (A <> P).
      apply l8_20_2 with C X C' C''; assumption.
    assert (exists T, Bet P T C /\ Bet A T X).
      eapply l3_17 with C'' C'.
        apply midpoint_bet2. assumption.
        apply midpoint_bet2. assumption.
        apply midpoint_bet2. assumption.
    exists_and H9 T.
    exists P.
    exists T.
    induction (eq_dec_points X A).
      subst X.
      assert (C'= C'').
        apply symmetric_point_uniqueness with A C; assumption.
      subst C''. assert(A=T).
        apply between_identity. assumption.
      subst T. assert(P=C').
        apply midpoint_identity_122. assumption.
      subst C'.
      repeat split.
        apply perp_col_3 with C; try assumption.
          apply bet_col_321. assumption.
        apply col_trivial_121.
        apply between_symmetry. assumption.
    repeat split.
      assert(Perp_at A A B A P).
        apply mid_tri_perpap with X C X C'' C'; try assumption.
          apply not_col_132.
            apply not_col_trans with B; try assumption.
            apply not_eq_sym. assumption.
            apply midpoint_symmetry. assumption.
      apply perpat_perp with A.
      apply perpat_1243. assumption.
      apply col_transitivity_2 with X; try assumption.
        apply col_312. assumption.
        apply bet_col_231. assumption.
      apply between_symmetry. assumption.
Qed.


Lemma l8_21 : forall A B C,
 A <> B -> exists P, exists T,
 Perp A B P A /\ Col A B T /\ Bet C T P.
Proof.
    intros.
    induction(col_dec A B C).
      assert (exists C', ~ Col A B C').
        apply not_col_exists. assumption.
      exists_and H1 C'.
      assert ( exists P : Tpoint, (exists T : Tpoint, Perp A B P A /\ Col A B T /\ Bet C' T P)).
        apply l8_21_aux.
        assumption.
      exists_and H1 P.
      exists_and H3 T.
      exists P.
      exists C.
      repeat split.
        assumption.
        assumption.
      apply between_trivial_112.
    apply l8_21_aux.
    assumption.
Qed.

Lemma l8_24 : forall A B P Q R T,
 Perp P A A B -> Perp Q B A B -> Col A B T
 -> Bet P T Q -> Bet B R Q -> Cong A P B R
 -> exists X, Midpoint X A B /\ Midpoint X P R.
Proof.
    intros.
    assert(P<>A /\ A <> B).
      apply perp_distinct. assumption.
    assert(Q<>B /\ A<>B).
      apply perp_distinct. assumption.
    spliter.
    assert (exists X, Bet T X B /\ Bet R X P).
      apply inner_pasch with Q; assumption.
    exists_and H9 X.
    apply between_symmetry in H9.
    assert (Col A B X).
      apply l6_16_c with T; assumption.
    assert(B<>R).
      apply cong_diff_12_34 with A P.
        apply not_eq_sym. assumption.
        assumption.
    assert(~ Col A B P).
      apply perp_not_col. apply perp_3412. assumption.
    assert (~Col B Q A).
      apply perp_not_col. apply perp_2134. assumption.
    assert (~Col B A R).
      apply not_col_trans with Q; try assumption.
      apply bet_col_132. assumption.
    apply not_col_distincts in H13. spliter.
    assert (P <> R).
      apply bet_col_not_col_diff with A B X; assumption.
    assert (Perp A B R B).
      apply perp_col_3 with Q.
        assumption.
        apply perp_3412. assumption.
        apply bet_col_231. assumption.
    assert (Cong A R P B).
      apply (perp_cong A B P R X); try assumption.
        apply perp_3412. assumption.
        apply between_symmetry. assumption.
    exists X.
      apply (l7_21 A P B R X); try assumption.
        apply not_col_132. assumption.
        apply cong_3421. assumption.
        apply col_132. assumption.
        apply bet_col_321. assumption.
Qed.

Lemma perp_existence : forall A B,
  A<>B -> exists Q, Perp A B B Q.
Proof.
    intros.
    assert (exists P : Tpoint, (exists T : Tpoint, Perp B A P B /\ Col B A T /\ Bet A T P)).
      eapply l8_21. apply not_eq_sym. assumption.
    exists_and H0 P.
    exists_and H1 T.
    exists P.
    apply perp_2143.
    assumption.
Qed.

Lemma perp_vector : forall A B,
  A <> B -> (exists X, exists Y, Perp A B X Y).
Proof.
    intros.
    exists B.
    assert(exists Y, Perp A B B Y).
      apply perp_existence. assumption.
      exists_and H0 Y.
    exists Y.
    assumption.
Qed.

End Perp_exists.

Print All.

