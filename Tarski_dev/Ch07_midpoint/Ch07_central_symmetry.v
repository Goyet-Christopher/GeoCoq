Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma midpoint_prolong_cong : forall A P P' B Q Q',
  Midpoint A P P' -> Midpoint B Q Q' 
-> exists X X' Y Y', Bet_5 X P A P' X' /\ Bet_5 Y Q B Q' Y' /\
  Midpoint A X X' /\ Midpoint B Y Y' /\
  Cong_3 X A X' Y B Y' /\ Cong_3 X A X' Y' B Y /\
  Cong_3 X P A B Q Y   /\ Cong_3 A P' X' Y' Q' B /\
  Cong_3 X P A B Q' Y' /\ Cong_3 A P' X' Y Q B.
Proof.
    intros.
    apply midpoint_to_def in H.
    apply midpoint_to_def in H0.
    spliter.
    prolong P' P X Q B.
      apply between_symmetry in H3.
      apply cong_4312 in H4.
    prolong X P' X' Q B.
      apply cong_3412 in H6.
    prolong Q' Q Y P A.
      apply between_symmetry in H7.
      apply cong_1243 in H8.
    prolong Y Q' Y' P A.
    exists X. exists X'. exists Y. exists Y'.
    assert(Bet_5 X P A P' X').
      apply bet5_bet_4; assumption.
    assert(Bet_5 Y Q B Q' Y').
      apply bet5_bet_4; assumption.
    assert(Cong_3 X A X' Y B Y' /\ Cong_3 X P A B Q Y /\ Cong_3 A P' X' Y' Q' B  /\ Cong X X' Y Y').
      apply (l2_11_bet5_2143 X P A P' X' Y Q B Q' Y'); try assumption.
        apply cong_XY12_XY34 with P A; assumption.
        apply cong_12XY_XY34 with Q B; assumption.
    assert(Cong_3 X A X' Y' B Y /\ Cong_3 X P A B Q' Y' /\ Cong_3 A P' X' Y Q B  /\ Cong X X' Y Y').
      apply (l2_11_bet5_3412 X P A P' X' Y Q B Q' Y'); try assumption.
        apply cong_12XY_XY34 with Q B; assumption.
        apply cong_XY12_XY34 with P A; assumption.
    spliter.
    assert(Cong_3 Y B Y' Y' B Y).
      apply cong3_transitivity_X1_X2 with X A X'; assumption.
    assert(Cong_3 X A X' X' A X).
      apply cong3_transitivity_1X_2X with Y B Y'.
        assumption. apply cong3_swap_321. assumption.
    repeat (split; try assumption).
      apply H11.
      apply cong3_1254 with X' X. assumption.
      apply H12.
      apply cong3_1254 with Y' Y. assumption.
Qed.

(** l7_13 *) 
Lemma symmetry_preserves_length : forall A P Q P' Q',
 Midpoint A P P' -> Midpoint A Q Q' -> Cong P Q P' Q'.
Proof.
    intros.
    assert(H' := midpoint_prolong_cong A P P' A Q Q' H H0).
      exists_and H' X. exists_and H1 X'.
      exists_and H2 Y. exists_and H1 Y'.
    assert (Cong_3 A X Y A Y' X').
      apply OFSC_isosceles_cong3.
        left. apply H1. assumption.
    assert (Cong Q X Q' X').
      apply IFSC_cong_24 with Y A Y' A.
        apply def_to_IFSC.
        apply H2. apply between_symmetry. apply H2.
        apply midpoint_cong_2131. assumption.
        apply midpoint_cong_2131. assumption.
        apply cong3_3256 with A A. assumption.
        apply midpoint_cong_1213. assumption.
    apply IFSC_cong_24 with X A X' A.
      apply def_to_IFSC.
        apply H1. apply between_symmetry. apply H1.
        apply midpoint_cong_2131. assumption.
        apply midpoint_cong_2131. assumption.
        apply cong_2143. assumption.
        apply midpoint_cong_1213. assumption.
Qed.

Lemma symmetry_preserves_length_cong3 : forall A P Q R P' Q' R',
 Midpoint A P P' -> Midpoint A Q Q' -> Midpoint A R R'
 -> Cong_3 P Q R P' Q' R'.
Proof.
    intros.
    apply def_to_cong3.
    apply symmetry_preserves_length with A; assumption.
    apply symmetry_preserves_length with A; assumption.
    apply symmetry_preserves_length with A; assumption.
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
    apply cong_XY12_XY34 with P Q.
      assumption.
      apply cong_12XY_XY34 with R S; assumption.
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

