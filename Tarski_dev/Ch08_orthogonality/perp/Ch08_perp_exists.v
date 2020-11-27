
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



Lemma l8_18_existence : forall A B C,
 ~ Col A B C -> exists X, Col A B X /\ Perp A B C X.
Proof.
    intros.
    prolong B A Y A C.
    assert (exists P, Midpoint P C Y) by (apply l7_25 with A;Cong).
    ex_and H2 P.
    assert (Per A P Y) by (unfold Per;exists C;auto using l7_2).
    prolong A Y Z Y P.
    prolong P Y Q Y A.
    prolong Q Z Q' Q Z.
    assert (Midpoint Z Q Q') by (unfold Midpoint;split;Cong).
    prolong Q' Y C' Y C.
    assert (exists X, Midpoint X C C') by (apply l7_25 with Y;Cong).
    ex_and H13 X.
    assert (OFSC A Y Z Q Q Y P A) by (unfold OFSC;repeat split;Between;Cong).
    show_distinct A Y.
      intuition.
    assert (Cong Z Q P A) by (eauto using five_segment_with_def).
    assert (Cong_3 A P Y Q Z Y) by (unfold Cong_3;repeat split;Cong).
    assert (Per Q Z Y) by (eauto using l8_10).
    assert (Per Y Z Q) by eauto using l8_2.
    (* diversion *)
    show_distinct P Y.
      unfold Midpoint in *.
      spliter.
      treat_equalities.
      assert_cols.
      Col5.
    unfold Per in H19.
    ex_and H19 Q''.
    assert (Q' = Q'').
      eapply symmetric_point_uniqueness.
        apply H10.
      assumption.
    subst Q''.
    assert (hy:Bet Z Y X).
      apply (l7_22 Q C Q' C' Y Z X);Cong.
      assert (T:=outer_transitivity_between2 C P Y Q).
      assert_bets.
      apply between_symmetry.
      apply T;Between.
    show_distinct Q Y.
      intuition.
    assert (Per Y X C) by (unfold Per;exists C';split;Cong).
    assert_diffs.
    assert (Col P Y Q).
      unfold Col.
      left.
      assumption.
    assert(Col P Y C).
      unfold Midpoint in H3.
      spliter.
      unfold Col.
      right; right.
      assumption.
    assert (Col P Q C) by ColR.
    assert (Col Y Q C) by ColR.
    assert (Col A Y B) by (assert_cols;Col).
    assert (Col A Y Z) by (assert_cols;Col).
    assert (Col A B Z) by ColR.
    assert (Col Y B Z) by ColR.
    assert (Col Q Y P) by Col.
    assert(Q <> C).
      intro.
      subst Q.
      unfold Midpoint in *.
      spliter.
      apply H.
      assert (Bet B Y Z) by (apply outer_transitivity_between2 with A;auto).
      apply between_symmetry in H3.
      assert (Y = P).
        eapply between_equality.
          apply H3.
        assumption.
      treat_equalities.
      intuition.
    assert (Col Y B Z) by ColR. 
    show_distinct Y Q'. intuition.
    assert (Col Y Q' C') by (assert_cols;Col).
    assert (Q <> Q').
      intro.
      unfold OFSC, Cong_3 in *.
      spliter.
      treat_equalities.
      apply H.
      ColR.
    assert (C <> C').
      intro.
      subst C'.
      apply l7_3 in H14.
      subst X.
      assert (Col Z Q Q') by (assert_cols;ColR).
      assert (Y <> Z).
        intro.
        subst Z.
        unfold OFSC, Cong_3, Midpoint in *.
        spliter.
        treat_equalities.
        intuition.
      apply H.
      ColR.
    (* end of C<>C' *)
    assert(OFSC Q Y C Z Q' Y C' Z).
      unfold OFSC.
      repeat split;Between;Cong.
      unfold OFSC, Midpoint in *.
      spliter.
      eapply outer_transitivity_between with P;Between;Cong.
    assert (Cong C Z C' Z) by (eauto using five_segment_with_def).
    assert (Col Z Y X) by (assert_cols;Col).
    show_distinct Y Z. intuition.
    assert(C <> X).
      intro.
      subst X.
      unfold OFSC,Cong_3,Midpoint in *.
      spliter.
      treat_equalities.
      intuition.
    assert(X <> Y).
      intro.
      subst X.
      unfold OFSC,Cong_3,Midpoint in *.
      spliter.
      clean_duplicated_hyps.
      clean_trivial_hyps.
      show_distinct C' Y.
        intuition.
      assert (Col Y C' P ).
        eapply col_transitivity_1 with C.
          intuition.
          unfold Col.
          right;right.
          apply between_symmetry.
          assumption.
        apply col_permutation_1.
        assumption.
      show_distinct P Q.
        intuition.
      assert (Col Y P Q') by ColR.
      assert (Col Y Q Q') by ColR.
      assert (Col Q Y Z) by (assert_cols;ColR).
      assert (Col Y Z C) by (assert_bets;assert_cols;ColR).
      apply H.
      ColR.
    assert (Perp_at X Y Z C X).
      eapply l8_13_2;Col.
      exists Y.
      exists C.
      repeat split;Col.
    assert (Col A B X) by ColR.
    exists X.
    split.
      assumption.
    unfold Perp.
    exists X.
    unfold Perp_at.
    repeat split;Col.
    intros.
    unfold Perp_at in H52.
    spliter.
    apply H57;ColR.
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


Lemma perp_proj : forall A B C D,
 Perp A B C D -> ~Col A C D
 -> exists X, Col A B X /\ Perp A X C D.
Proof.
    intros.
    unfold Perp in H.
    ex_and H X.
    exists X.
    split.
      unfold Perp_at in H1.
      spliter.
      apply col_permutation_1.
      assumption.
    eapply perp_col.
      intro.
      subst X.
      unfold Perp_at in H1.
      spliter.
      apply H0.
      assumption.
      apply perp_in_perp in H1.
      apply H1.
    unfold Perp_at in H1.
    spliter.
    apply col_permutation_1.
    assumption.
Qed.

