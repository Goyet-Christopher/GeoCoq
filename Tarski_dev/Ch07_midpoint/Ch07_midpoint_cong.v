Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_eq.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cong_cong_half_1 : forall A M B A' M' B',
 Midpoint M A B -> Midpoint M' A' B' ->
 Cong A B A' B' -> Cong A M A' M'.
Proof.
    intros.
    assert(exists M'', Bet A' M'' B' /\ Cong_3 A M B A' M'' B').
      eapply l4_5_b. apply H.
        assumption.
    exists_and H2 M''.
    assert (Midpoint M'' A' B').
      split.
        assumption.
      apply cong_1234_1256 with A M.
        apply H3.
        apply cong_1234_3456 with M B.
          apply H. apply H3.
    assert(M'=M'').
      apply l7_17 with A' B'; assumption.
    subst M''.
    apply H3.
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
      apply cong_1234_1256 with A' M'.
        apply cong_1234_1256 with A M; assumption.
        assumption.
Qed.

End T7_1.

Print All.


