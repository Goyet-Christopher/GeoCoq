Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_diff.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma not_midpoint_symmetry : forall I A B,
  ~ Midpoint I A B -> ~ Midpoint I B A .
Proof.
    intros.
    intro.
    apply H.
    apply midpoint_symmetry.
      assumption.
Qed.

Lemma midpoint_not_midpoint : forall I A B,
  A<>B -> Midpoint I A B
 -> ~ Midpoint B A I.
Proof.
    intros.
    assert(I<>A /\ I<>B).
      apply midpoint_distinct_1; assumption.
      spliter.
    intro.
    assert (I=B).
      apply between_equality_2 with A.
        apply H0. apply H3.
    subst.
    contradiction.
Qed.

Lemma midpoint_not_midpoint_sym : forall I A B,
  A<>B -> Midpoint I A B
 -> ~ Midpoint A B I.
Proof.
    intros.
    apply midpoint_not_midpoint.
      apply diff_symmetry. assumption.
      apply midpoint_symmetry. assumption.
Qed.

Lemma not_midpoint_cases : forall I A B,
  ~ Bet A I B \/ ~ Cong A I I B -> ~ Midpoint I A B.
Proof.
    intros.
    induction H.
      intro. apply H. apply H0.
      intro. apply H. apply H0.
Qed.

End T7_1.

Print All.