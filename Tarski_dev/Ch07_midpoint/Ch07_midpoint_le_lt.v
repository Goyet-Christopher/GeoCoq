Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_diff.
Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_cong.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma mid_lt : forall A M B,
 A <> B -> Midpoint M A B
 -> Lt A M A B.
Proof.
    intros.
    assert(M<>A /\ M<>B).
      apply midpoint_distinct_1; assumption.
    spliter.
    split.
      exists M. 
      split. apply H0. apply cong_1212.
    intro.
    assert(M = B).
      apply between_cong with A.
        apply H0. assumption.
    subst.
    contradiction.
Qed.

Lemma le_mid2_le13 : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B'
 -> Le A M A' M' -> Le A B A' B'.
Proof.
    intros.
    apply midpoint_to_def in H.
    apply midpoint_to_def in H0.
    spliter.
    apply bet2_le2_le_13 with M M'; try assumption.
      apply (l5_6 A M A' M'); assumption.
Qed.

Lemma le_mid2_le12 : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B'
 -> Le A B A' B' -> Le A M A' M'.
Proof.
    intros.
    assert(Le A M A' M' \/ Le A' M' A M).
      apply le_cases_min.
    induction H2.
      assumption.
    assert(Le A' B' A B).
      apply le_mid2_le13 with M' M; assumption.
    assert(Cong A B A' B').
      apply le_anti_symmetry; assumption.
    apply cong_le_1234.
    apply cong_cong_half_1 with B B'; assumption.
Qed.

Lemma lt_mid2_lt13 : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B'
 -> Lt A M A' M' -> Lt A B A' B'.
Proof.
    intros.
    apply lt_to_def in H1.
    spliter.
    split.
      apply le_mid2_le13 with M M'; assumption.
    intro.
      apply H2.
      apply cong_cong_half_1 with B B'; assumption.
Qed.

Lemma lt_mid2_lt12 : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B'
 -> Lt A B A' B' -> Lt A M A' M'.
Proof.
    intros.
    apply lt_to_def in H1.
    spliter.
    split.
      apply le_mid2_le12 with B B'; assumption.
    intro.
      apply H2.
      apply cong_mid2_cong with M M'; assumption.
Qed.

End T7_1.

Print All.

