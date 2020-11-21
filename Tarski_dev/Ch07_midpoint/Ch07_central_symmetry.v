Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** l7_13 *) 
Lemma symmetry_preserves_length : forall A P Q P' Q',
 Midpoint A P P' -> Midpoint A Q Q' -> Cong P Q P' Q'.
Proof.
    intros.
    apply midpoint_to_def in H.
    apply midpoint_to_def in H0.
    spliter.
    induction (eq_dec_points P A).
      subst P.
      assert(A = P').
        apply cong_reverse_identity with A. assumption.
      subst P'.
        apply cong_2134. assumption.
    prolong P' P X Q A.
      apply between_symmetry in H4.
      apply cong_4312 in H5.
    prolong X P' X' Q A.
      apply cong_3412 in H7.
    prolong Q' Q Y P A.
      apply between_symmetry in H8.
      apply cong_1243 in H9.
    prolong Y Q' Y' P A.
    assert(Bet_5 X P A P' X').
      apply bet5_bet_4; assumption.
    assert(Bet_5 Y Q A Q' Y').
      apply bet5_bet_4; assumption.
    assert(Cong_3 X A X' Y A Y' /\ Cong_3 X P A A Q Y /\ Cong_3 A P' X' Y' Q' A  /\ Cong X X' Y Y').
      apply (l2_11_bet5_2143 X P A P' X' Y Q A Q' Y'); try assumption.
        apply cong_1234_1256 with P A; assumption.
        apply cong_1234_3456 with Q A; assumption.
    assert(Cong_3 X A X' Y' A Y /\ Cong_3 X P A A Q' Y' /\ Cong_3 A P' X' Y Q A  /\ Cong X X' Y Y').
      apply (l2_11_bet5_3412 X P A P' X' Y Q A Q' Y'); try assumption.
        apply cong_1234_3456 with Q A; assumption.
        apply cong_1234_1256 with P A; assumption.
    spliter.
    assert (X <> A).
      apply bet_neq23__neq with P.
        apply bet5_bet_123 with P' X'. assumption.
        assumption.
    assert (Cong X' Y' Y X).
      apply FSC_cong_34 with X A Y' A.
        apply def_to_FSC.
          apply bet_col_123. apply bet5_bet_135 with P P'. assumption.
          assumption.
          apply cong_1221.
          apply cong3_4631 with P Q'. assumption.
        left. assumption.
    assert (Cong X' A A X).
      apply cong_1234_3456 with A Y.
        apply cong_2134. apply H15.
        apply cong_3421. apply H19.
    assert(Cong_3 Y A Y' Y' A Y).
      apply cong3_transitivity_12_13_23 with X A X'; assumption.
    assert (Cong Q X Q' X').
      apply IFSC_cong_24 with Y A Y' A.
        apply def_to_IFSC.
        apply H13. apply between_symmetry. apply H13.
        apply H25.
        apply cong_1243. assumption.
        apply cong_3421. assumption.
        apply cong_3421. assumption.
    apply IFSC_cong_24 with X A X' A.
      apply def_to_IFSC.
        apply H12. apply between_symmetry. apply H12.
        apply cong_4312. assumption.
        apply cong_1243. assumption.
        apply cong_2143. assumption.
        apply cong_2134. assumption.
Qed.

(** l7_15 *) 
Lemma symmetry_preserves_bet : forall P Q R P' Q' R' A,
 Midpoint A P P' -> Midpoint A Q Q' -> Midpoint A R R'
 -> Bet P Q R -> Bet P' Q' R'.
Proof.
    intros.
    apply l4_6 with P Q R.
      assumption.
    apply def_to_cong3.
    apply symmetry_preserves_length with A; assumption.
    apply symmetry_preserves_length with A; assumption.
    apply symmetry_preserves_length with A; assumption.
Qed.

(** l7_16 *) 
Lemma symmetry_preserves_cong : forall P Q R S P' Q' R' S' A,
  Midpoint A P P' -> Midpoint A Q Q' ->
  Midpoint A R R' -> Midpoint A S S' ->
  Cong P Q R S -> Cong P' Q' R' S'.
Proof.
    intros.
    assert (Cong P Q P' Q').
      apply symmetry_preserves_length with A; assumption.
    assert (Cong R S R' S').
      apply symmetry_preserves_length with A; assumption.
    apply cong_1234_1256 with P Q.
      assumption.
      apply cong_1234_3456 with R S; assumption.
Qed.

Lemma symmetry_preserves_midpoint : forall A B C A' B' C' Z,
  Midpoint Z A A' -> Midpoint Z B B'
 -> Midpoint Z C C' -> Midpoint B A C
 -> Midpoint B' A' C'.
Proof.
    intros.
    assert(Bet A B C).
      apply midpoint_bet1. assumption.
    assert(Cong A B B C).
      apply midpoint_cong. assumption.
    apply def_to_midpoint.
      apply symmetry_preserves_bet with A B C Z; assumption.
    apply symmetry_preserves_cong with A B B C Z; assumption.
Qed.

End T7_1.

Print All.

