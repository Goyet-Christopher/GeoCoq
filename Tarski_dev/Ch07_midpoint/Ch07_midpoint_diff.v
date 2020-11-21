Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_eq.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma midpoint_distinct_1 : forall I A B,
 A<>B -> Midpoint I A B 
 -> I<>A /\ I<>B.
Proof.
    intros.
    split.
    intro.
      subst.
      assert(A=B).
        apply midpoint_identity_112. assumption.
      subst.
      apply H.
        apply midpoint_identity_122. assumption.
    intro.
      subst.
      assert(B=A).
        apply midpoint_identity_121. assumption.
      subst.
      apply H.
        apply midpoint_identity_122. assumption.
Qed.

Lemma midpoint_distinct_2 : forall I A B,
 I<>A -> Midpoint I A B
  -> A<>B /\ I<>B.
Proof.
    intros.
    assert (A<>B).
      intro.
      subst.
      apply H.
        apply midpoint_identity_122. assumption.
    split.
      assumption.
    apply midpoint_distinct_1 in H0.
    spliter.
    assumption.
    assumption.
Qed.


Lemma midpoint_distinct_3 : forall I A B,
 I<>B -> Midpoint I A B
 -> A<>B /\ I<>A.
Proof.
    intros.
    assert (A<>B).
      intro.
      subst.
        apply H.
        apply midpoint_identity_122. assumption.
    split.
      assumption.
    apply midpoint_distinct_1 in H0.
    spliter.
    assumption.
    assumption.
Qed.

End T7_1.

Print All.

