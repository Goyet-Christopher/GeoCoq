Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_eq.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cong_mid2_cong3_1 : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B' ->
 Cong A B A' B' -> Cong_3 A M B A' M' B'.
Proof.
    intros.
    assert(exists M'', Bet A' M'' B' /\ Cong_3 A M B A' M'' B').
      eapply l4_5_b. apply H.
        assumption.
    exists_and H2 M''.
    assert (Midpoint M'' A' B').
      split.
        assumption.
      apply cong_XY12_XY34 with A M.
        apply H3.
        apply cong_12XY_XY34 with M B.
          apply H. apply H3.
    assert(M'=M'').
      apply symmetry_same_center with A' B'; assumption.
    subst M''.
    assumption.
Qed.

Lemma cong_cong_half_1 : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B' ->
 Cong A B A' B' -> Cong A M A' M'.
Proof.
    intros.
    assert(Cong_3 A M B A' M' B').
      apply cong_mid2_cong3_1; assumption.
    apply H2.
Qed.

Lemma cong_cong_half_2 : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B' ->
 Cong A B A' B' -> Cong B M B' M'.
Proof.
    intros.
    apply cong_cong_half_1 with A A'.
      apply midpoint_symmetry. assumption.
      apply midpoint_symmetry. assumption.
    apply cong_2143. assumption.
Qed.

Lemma cong_mid2_cong : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B' ->
 Cong A M A' M' -> Cong A B A' B'.
Proof.
    intros.
    apply midpoint_to_def in H.
    apply midpoint_to_def in H0.
    spliter.
    apply l2_11 with M M'; try assumption.
      apply cong_XY12_XY34 with A M.
        assumption.
        apply cong_12XY_XY34 with A' M'; assumption.
Qed.

Lemma cong_mid2_cong3_2 : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B' ->
 Cong A M A' M' -> Cong_3 A M B A' M' B'.
Proof.
    intros.
    assert(Cong A B A' B').
      apply cong_mid2_cong with M M'; assumption.
    apply midpoint_to_def in H.
    apply midpoint_to_def in H0.
    spliter.
    apply bet_cong1213_cong3; assumption.
Qed.

Lemma cong_mid2_cong3_3 : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B' ->
 Cong M B M' B' -> Cong_3 A M B A' M' B'.
Proof.
    intros.
    apply cong3_swap_321.
    apply cong_mid2_cong3_2.
      apply midpoint_symmetry. assumption.
      apply midpoint_symmetry. assumption.
      apply cong_2143. assumption.
Qed.

Lemma cong_mid2_cong_2 : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B' ->
 Cong M B M' B' -> Cong A B A' B'.
Proof.
    intros.
    apply cong3_1346 with M M'.
    apply cong_mid2_cong3_3; assumption.
Qed.

Lemma cong_mid2_cong_3 : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B' ->
 Cong M B M' B' -> Cong A M A' M'.
Proof.
    intros.
    apply cong3_1245 with B B'.
    apply cong_mid2_cong3_3; assumption.
Qed.

Lemma cong_mid2_cong_1 : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B' ->
 Cong A M A' M' -> Cong M B M' B'.
Proof.
    intros.
    apply cong3_2356 with A A'.
    apply cong_mid2_cong3_2; assumption.
Qed.

Lemma mid2_qequi : forall M A B A' B',
  Midpoint M A A' -> Midpoint M B B' -> Cong A B A B'
-> QEqui A B A' B'.
Proof.
    intros.
    apply qequi_2adj_1op_3.
      assumption.
      apply cong_12XY_YX34 with A B'.
        assumption.
        apply symmetry_preserves_length with M.
          apply midpoint_symmetry. assumption.
          assumption.
     apply symmetry_preserves_length with M; assumption.
Qed.

Lemma mid2_cong3_OFSC : forall A B C D A' B' C' D',
  Cong_3 A B C A' B' C' -> Midpoint B C D -> Midpoint B' C' D'
-> OFSC C B D A C' B' D' A'.
Proof.
    intros.
    apply def_to_OFSC_with_cong3.
      apply midpoint_bet1. assumption.
      apply midpoint_bet1. assumption.
      apply cong3_swap_321. assumption.
      apply cong_XY12_XY34 with C B.
        apply midpoint_cong. assumption.
      apply cong_XY12_XY34 with C' B'.
        apply cong3_6532 with A A'. assumption.
        apply midpoint_cong. assumption.
Qed.

End T7_1.

Print All.


