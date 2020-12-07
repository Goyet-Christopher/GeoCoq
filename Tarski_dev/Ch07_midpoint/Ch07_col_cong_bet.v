Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_col.
Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_eq.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma col_cong_bet : forall A B C D,
 Col A B D -> Cong A B C D -> Bet A C B
 -> Bet C A D \/ Bet C B D.
Proof.
    intros.
    prolong4 B C A D1 B C.
      apply bet4_symmetry in H2.
    prolong4 A C B D2 A C.
    assert(Bet_5 D1 A C B D2).
      induction (eq_dec_points A B).
        subst. apply cong_reverse_identity in H0.
        subst. apply between_identity_2 in H1.
        subst. apply cong_reverse_identity in H3.
        subst. apply cong_reverse_identity in H5.
        subst. apply bet5_trivial.
      apply bet5_bet4_15. right. left. assumption.
         assumption. assumption.
    assert(Cong_3 A C B C A D1).
      apply l2_11_cong3_reverse. assumption.
      apply H2. apply cong_1212.
      apply cong_2143. assumption.
    assert(Cong_3 A C B D2 B C).
      apply l2_11_cong3_reverse; try assumption.
        apply H4. apply cong_1212.
    assert(Cong_3 C A D1 D2 B C).
      apply cong3_transitivity_X1_X2 with A C B; assumption.
    assert(Col D C D1).
      induction (eq_dec_points A B).
      (* A = B *)
        subst B.
        apply cong_reverse_identity in H0.
        subst D.
          apply col_trivial_112.
      (* A <> B *)
        apply bet_col_132 in H1.
        assert(Col A B D1).
          apply bet_col_312.
          apply bet4_bet_124 with C. assumption.
      apply col_transitivity_3 with A B; assumption.
    assert(D = D1 \/ Midpoint C D D1).
      apply l7_20. assumption.
        apply cong_XY12_XY34 with A B.
          assumption. apply H7.
    induction H11.
    (* D = D1 -> Bet C A D *)
      subst D1.
      left. apply between_symmetry.
      apply bet5_bet_123 with B D2. assumption.
    (* Midpoint C D D1 -> Bet C B D *)
      assert(Midpoint C D2 D1).
    split.
      apply between_symmetry. apply H6.
      apply cong3_4613 with A B. assumption.
    assert(D = D2).
      apply symmetric_point_uniqueness_sym with C D1; assumption.
    subst D2.
    right.
    apply H6.
Qed.

Lemma col_cong2_bet1 : forall A B C D,
 Col A B D -> Bet A C B -> Cong A B C D -> Cong A C B D
 -> Bet C B D.
Proof.
    intros.
    induction(eq_dec_points A C).
      subst C. apply cong_reverse_identity in H2.
      subst D.
      apply between_trivial_122.
    assert(HH:=col_cong_bet A B C D H H1 H0).
    induction HH.
    (* Bet C A D *)
      assert(B = C /\ A = D ).
        apply between_symmetry in H0.
        apply not_eq_sym in H3.
        apply bet_cong_eq.
          assumption.
          apply between_outer_transitivity_2 with C; assumption.
        apply cong_2134. assumption.
      spliter.
      subst D. subst C. apply between_trivial_112.
    (*  Bet C B D *)
      assumption.
Qed.

Lemma col_cong2_bet2 : forall A B C D,
 Col A B D -> Bet A C B -> Cong A B C D -> Cong A D B C
 -> Bet C A D.
Proof.
    intros.
    induction(eq_dec_points B C).
      subst C. apply cong_identity in H2.
      subst D. apply between_trivial_122.
    assert(HH:=col_cong_bet A B C D H H1 H0).
    induction HH.
      assumption.
      assert(D = B /\ C = A).
        apply between_symmetry in H4.
        apply between_symmetry in H0.
        apply bet_cong_eq.
          assumption.
          apply between_outer_transitivity_2 with B; assumption.
          apply cong_3421. assumption.
      spliter.
      subst D. subst C. assumption.
Qed.

Lemma col_cong2_bet3 : forall A B C D,
 Col A B D -> Bet A B C -> Cong A B C D -> Cong A C B D
 -> Bet B C D.
Proof.
    intros.
    induction(eq_dec_points A B).
      subst B. apply cong_reverse_identity in H1.
      subst D. apply between_trivial_122.
    apply col_cong2_bet2 with A.
      apply bet_col_123 in H0.
      apply col_213. apply col_transitivity_1 with B; assumption.
      apply between_symmetry. assumption.
      apply cong_2134. assumption.
      apply cong_3412. assumption.
Qed.

Lemma col_cong2_bet4 : forall A B C D,
 Col A B C -> Bet A B D -> Cong A B C D -> Cong A D B C
 -> Bet B D C.
Proof.
    intros.
    induction(eq_dec_points A B).
      subst B. apply cong_reverse_identity in H1.
      subst D. apply between_trivial_122.
    apply (col_cong2_bet1 A D B C).
      apply bet_col_123 in H0.
      apply col_transitivity_1 with B; assumption.
      assumption.
      assumption.
      apply cong_1243. assumption.
Qed.

Lemma col_bet2_cong1 : forall A B C D,
  Col A B D -> Bet A C B -> Cong A B C D -> Bet C B D
 -> Cong A C D B.
Proof.
    intros.
    apply (l4_3 A C B D B C).
      assumption.
      apply between_symmetry. assumption.
      apply cong_1243. assumption.
      apply cong_1221.
Qed.

Lemma col_bet2_cong2 : forall A B C D,
  Col A B D -> Bet A C B -> Cong A B C D -> Bet C A D
 -> Cong D A B C.
Proof.
    intros.
    eapply l4_3 with C A.
      apply between_symmetry. assumption.
      apply between_symmetry. assumption.
      apply cong_4321. assumption.
      apply cong_1221.
Qed.

End T7_1.

Print All.
