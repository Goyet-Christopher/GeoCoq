Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_col.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_perpat.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_per.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_exists.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_cong3.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_col.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_per.

Section Perp_exists.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perp_proj : forall A B C D,
 Perp A B C D -> ~Col A C D
 -> exists X, Col A B X /\ Perp A X C D.
Proof.
    intros.
    apply perp_to_def in H.
    exists_and H X.
    exists X.
    split.
      apply col_231.
      apply (perpat_col A B C D X). assumption.
    apply perp_col_4 with D.
      apply not_col_distincts in H0. spliter.
      assumption.
      apply perpat_perp in H1.
      apply H1.
    unfold Perp_at in H1.
    spliter.
    apply col_permutation_1.
    assumption.
Qed.

Lemma l8_18_existence : forall A B C,
 ~ Col A B C -> exists X, Col A B X /\ Perp A B C X.
Proof.
    intros.
    prolong B A Y A C.
    assert (exists P, Midpoint P C Y).
      apply l7_25 with A. assumption.
      exists_and H2 P.
    assert(Bet C P Y).
      apply midpoint_bet1. assumption.
    assert (Per A P Y).
      apply mid_cong_per with C.
        apply midpoint_symmetry. assumption.
        apply cong_3412. assumption.
    prolong4 B A Y Z Y P.
      assert(Col Z Y A).
        apply bet_col_321. 
        apply bet4_bet_234 with B. assumption.
      assert(Col Z Y B).
        apply bet_col_321. 
        apply bet4_bet_134 with A. assumption.
    prolong4 C P Y Q Y A.
      assert(Bet Q Y C).
        apply bet4_bet_431 with P. assumption.
    symmetric Q' Z Q.
    prolong Q' Y C' Y C.
    assert (exists X, Midpoint X C C').
      apply l7_25 with Y. assumption.
      exists_and H15 X.
    assert(Cong Z Q P A).
      apply OFSC_isosceles with Y.
        apply bet4_bet_432 with B. assumption.
        apply bet4_bet_234 with C. assumption.
        apply cong_3412. assumption. assumption.
   assert(Cong_3 Y Z Q Y P A).
      apply def_to_cong3.
        apply cong_3412. assumption.
        apply cong_3412. assumption.
        assumption.
    assert (Per Y Z Q).
      apply cong3_preserves_per with Y P A.
        apply per_symmetry. assumption.
        apply cong3_symmetry. assumption.
    assert(Cong Y Q Y Q').
      apply per_mid_cong with Z; assumption.
    assert(Cong Q C' Q' C /\ Cong Z C Z C').
      apply midpoint_IFSC_same_base with Y; assumption.
      spliter.
    assert (Bet Z Y X).
      apply (l7_22 Q C Q' C' Y Z X); assumption.
    apply not_col_distincts in H. spliter.
    assert(A<>Y).
      apply cong2_not_col_diff with B C Q; try assumption.
       apply cong_2134. assumption.
    assert(P<>Y).
      apply not_col_not_bet in H. spliter.
      intro. subst. assert(Y=Z).
        apply cong_reverse_identity with Y. assumption.
      subst. assert(Z=C).
        apply midpoint_identity_121. assumption.
      subst. apply between_symmetry in H0.
        contradiction.
    assert(Z<>Y).
      apply cong_diff_21_43 with Y P; assumption.
    assert(Col Z Y X).
      apply bet_col_123. assumption.
    assert(Col A B X).
      apply col_transitivity_3 with Z Y; assumption.
    assert(Col Z A X).
        apply col_transitivity_1 with Y; assumption.
    assert(C<>C').
      apply midpoint_distinct with A B X; assumption.
    assert(Q<>Y).
      apply cong_diff_21_43 with Y A; assumption.
    assert (Per Y X C).
      apply mid_cong_per with C'; assumption.
    assert (Per Z X C).
      apply mid_cong_per with C'; assumption.
    assert(Cong B C B C').
      apply l4_17 with Z Y; assumption.
    assert(Per B X C).
      apply mid_cong_per with C'; assumption.
    assert(Cong A C A C').
      apply l4_17 with Z Y; assumption.
    assert(Per A X C).
      apply mid_cong_per with C'; assumption.
    assert(X <> C /\ X <> C').
      apply midpoint_distinct_1; assumption.
        spliter.
    exists X.
    split.
      assumption.
      induction (eq_dec_points B X).
        subst X. apply perp_1243.
          apply per_perp; assumption.
        apply l8_16_2 with B; try assumption.
          apply col_trivial_122.
          apply per_symmetry. assumption.
Qed.



Lemma l8_21_aux : forall A B C,
 ~ Col A B C -> exists P, exists T, Perp A B P A /\ Col A B T /\ Bet C T P.
Proof.
    intros.
    assert (exists X : Tpoint, Col A B X /\ Perp A B C X).
      eapply l8_18_existence.
      assumption.
    ex_and H0 X.
    assert (Perp_at X A B C X).
      eapply l8_15_1; assert_diffs; auto.
    assert (Per A X C).
      unfold Perp_at in H2.
      spliter.
      apply H6.
        apply col_trivial_1.
      apply col_trivial_1.
    assert(HH:= H3).
    unfold Per in H3.
    ex_and H3 C'.
    double C A C''.
    assert (exists P, Midpoint P C' C'').
      eapply l7_25.
      unfold Midpoint in *.
      spliter.
      eapply cong_transitivity.
        apply cong_symmetry.
        apply H4.
      apply cong_left_commutativity.
      assumption; spliter.
    ex_elim H6 P.
    assert (Per X A P).
      eapply l8_20_1.
        apply HH.
        apply l7_2.
        apply H7.
        apply l7_2.
        apply H5.
      apply l7_2.
      assumption.
    assert (X <> C).
      intro.
      subst C.
      apply H.
      assumption.
    assert (A <> P).
      eapply l8_20_2.
        apply HH.
        apply l7_2.
        apply H7.
        apply l7_2.
        assumption.
        apply l7_2.
        assumption.
      assumption.
    assert (exists T, Bet P T C /\ Bet A T X).
      eapply l3_17.
        apply midpoint_bet.
        apply l7_2.
        apply H5.
        apply midpoint_bet.
        apply l7_2.
        apply H3.
      apply midpoint_bet.
      apply l7_2.
      apply H7.
    ex_and H10 T.
    induction (eq_dec_points A X).
      subst X.
      exists P.
      exists T.
      apply between_identity in H11.
      subst T.
      assert (C'= C'').
        eapply symmetric_point_uniqueness.
          apply H3.
        assumption.
      subst C''.
      apply l7_3 in H7.
      subst P.
      assert (Col A C C') by (assert_cols;ColR).
      repeat split;Col;Between.
      apply perp_col0 with C A;auto using perp_sym;assert_cols;Col.
    exists P.
    exists T.
    repeat split.
      unfold Perp.
      exists A.
      unfold Perp_at.
      repeat split.
        assert_diffs; auto.
        auto.
        apply col_trivial_1.
        apply col_trivial_3.
      unfold Perp_at in H2.
      spliter.
      intros.
      eapply per_col in H6.
        apply l8_2 in H6.
        eapply per_col in H6.
          eapply l8_2 in H6.
          apply H6.
          assumption.
        ColR.
        assumption.
      ColR.
      assert_cols;ColR.
    Between.
Qed.


Lemma l8_21 : forall A B C,
 A <> B -> exists P, exists T, Perp A B P A /\ Col A B T /\ Bet C T P.
Proof.
    intros.
    induction(Col_dec A B C).
      assert (exists C', ~ Col A B C').
        eapply not_col_exists.
        assumption.
      ex_elim H1 C'.
      assert ( exists P : Tpoint, (exists T : Tpoint, Perp A B P A /\ Col A B T /\ Bet C' T P)).
        eapply l8_21_aux.
        assumption.
      ex_elim H1 P.
      ex_and H3 T.
      exists P.
      exists C.
      repeat split.
        assumption.
        assumption.
      apply between_trivial2.
    eapply l8_21_aux.
    assumption.
Qed.




Lemma midpoint_existence_aux : forall A B P Q T,
  A<>B -> Perp A B Q B -> Perp A B P A ->
  Col A B T -> Bet Q T P -> Le A P B Q ->
  exists X : Tpoint, Midpoint X A B.
Proof.
    intros.
    unfold Le in H4.
    ex_and H4 R.
    assert (exists X, Bet T X B /\ Bet R X P).
      eapply inner_pasch.
        apply between_symmetry.
        apply H3.
      auto.
    ex_and H6 X.
    assert (Col A B X).
      induction (eq_dec_points T B).
        subst T.
        apply between_identity in H6.
        subst X.
        Col.
     assert_cols;ColR.
     induction(Col_dec A B P).
      assert (B=A \/ P=A).
        eapply l8_9.
          apply perp_per_1.
          assumption.
        apply col_permutation_4.
        assumption.
      induction H10.
        exists A.
        subst B.
        eapply l7_3_2.
      treat_equalities.
      apply perp_distinct in H1.
      spliter.
      absurde.
    assert (B <> R).
      intro.
      subst R.
      treat_equalities.
      apply H9.
      apply col_trivial_3.
    assert (~Col A B Q).
      intro.
      assert (A=B \/ Q=B).
        eapply l8_9.
          apply perp_per_2.
            auto.
          apply perp_comm.
          assumption.
        assumption.
      induction H12.
        apply H.
        assumption.
      subst Q.
      treat_equalities.
      absurde.
    assert (~Col A B R).
      intro.
      assert (Col B A Q).
        assert_cols;ColR.
      Col.
    show_distinct P R.
      intuition.
    induction (eq_dec_points A P).
      subst P.
      apply perp_distinct in H1.
      spliter.
      absurde.
    assert (Perp A B R B).
      eapply perp_col.
        assumption.
        apply perp_sym.
        apply perp_left_comm.
        eapply perp_col.
          assumption.
          apply perp_left_comm.
          apply perp_sym.
          apply H0.
        assert_cols;Col.
      Col.
    apply between_symmetry in H7.
    assert (Cong A R P B).
      apply (perp_cong A B P R X); assumption.
    assert (Midpoint X A B /\ Midpoint X P R).
      apply (l7_21 A P B R X);finish.
    spliter. exists X.
    assumption.
Qed.







Lemma l8_24 : forall A B P Q R T,
 Perp P A A B ->
 Perp Q B A B ->
 Col A B T ->
 Bet P T Q ->
 Bet B R Q ->
 Cong A P B R ->
 exists X, Midpoint X A B /\ Midpoint X P R.
Proof.
    intros.
    unfold Le in H4.
    assert (exists X, Bet T X B /\ Bet R X P).
      eapply inner_pasch.
        apply H2.
      assumption.
    ex_and H5 X.
    assert (Col A B X).
      induction (eq_dec_points T B).
        subst T.
        apply between_identity in H5.
        subst X.
        apply col_trivial_2.
      assert (Col T X B).
        unfold Col.
        left.
        assumption.
      apply col_permutation_4.
      eapply col_transitivity_1.
        intro.
        apply H7.
        apply sym_equal.
        apply H9.
        apply col_permutation_1.
        assumption.
      apply col_permutation_2.
      assumption.
    assert (A <> B).
      apply perp_distinct in H.
      spliter.
      assumption.
    assert (A <> P).
      apply perp_distinct in H.
      spliter.
      auto.
    induction(Col_dec A B P).
      assert (B=A \/ P=A).
        eapply l8_9.
          apply perp_per_1.
          apply perp_sym.
          assumption.
        apply col_permutation_4.
        assumption.
      induction H11.
        exists A.
        subst B.
        absurde.
      subst P.
      absurde.
    assert (B <> R).
      intro.
      subst R.
      apply cong_identity in H4.
      subst P.
      absurde.
    assert (Q <> B).
      apply perp_distinct in H0.
      spliter.
      assumption.
    assert (~Col A B Q).
      intro.
      assert (A=B \/ Q=B).
        eapply l8_9.
          apply perp_per_2.
            auto.
          apply perp_comm.
          apply perp_sym.
          assumption.
        assumption.
      induction H14.
        contradiction.
      subst Q.
      absurde.
    assert (~Col A B R).
      intro.
      assert (Col B A Q).
        eapply col_transitivity_1.
          apply H11.
          apply col_permutation_1.
          assumption.
        unfold Col.
        left.
        assumption.
      apply H13.
      apply col_permutation_4.
      assumption.
    assert (P <> R).
      intro.
      subst R.
      apply between_identity in H6.
      subst X.
      contradiction.
    induction (eq_dec_points A P).
      subst P.
      apply perp_distinct in H.
      spliter.
      absurde.
    assert (Perp A B R B).
      eapply perp_col.
        assumption.
        apply perp_sym.
        apply perp_left_comm.
        eapply perp_col.
          assumption.
          apply perp_left_comm.
          apply H0.
        unfold Col.
        right; left.
        apply between_symmetry.
        assumption.
      apply col_trivial_2.
    assert (Cong A R P B).
      apply (perp_cong A B P R X).
        assumption.
        assumption.
        apply perp_sym.
        assumption.
        assumption.
        assumption.
        assumption.
      apply between_symmetry.
      assumption.
    intros.
    assert (Midpoint X A B /\ Midpoint X P R).
      apply (l7_21 A P B R X).
        intro.
        apply H10.
        apply col_permutation_5.
        assumption.
        assumption.
        assumption.
        apply cong_right_commutativity.
        apply cong_symmetry.
        assumption.
        apply col_permutation_5.
        assumption.
      unfold Col.
      left.
      apply between_symmetry.
      assumption.
    exists X.
    assumption.
Qed.



End Perp_exists.

Print All.

