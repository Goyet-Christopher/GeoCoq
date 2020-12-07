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

Lemma midpoint_distinct : forall A B X C C',
 ~ Col A B C -> Col A B X -> Midpoint X C C' -> C <> C'.
Proof.
    intros.
    intro.
    subst C'.
    apply midpoint_identity_122 in H1.
    subst X.
    contradiction.
Qed.

Lemma l8_20_2 : forall A1 A2 A3 P Q A',
 Midpoint P A1 A' -> Midpoint Q A3 A'
 -> Midpoint A2 A1 A3 -> A1<>A2 -> P<>Q.
Proof.
    intros.
    intro.
    subst P.
    assert (A1 = A3).
      apply symmetric_point_uniqueness_sym with Q A'; assumption.
    subst A3.
    assert (A2 = A1).
      apply midpoint_identity_122. assumption.
    subst A2.
    contradiction.
Qed.

Lemma midpoint_cong_diff : forall A X P P',
  X <> A -> Midpoint A P P' -> Cong X P X P' -> X<>P /\ X<>P'.
Proof.
    intros.
    assert(X <> P).
      intro.
      subst.
      apply cong_reverse_identity in H1.
      subst.
      apply midpoint_identity_122 in H0.
      subst.
      apply H.
      apply eq_refl.
    split.
      assumption.
      apply cong_diff_12_34 with X P; assumption.
Qed.

Lemma midpoint_cong_diff_2 : forall A X P P',
  ~ Col P P' X -> Midpoint A P P' -> A<>X.
Proof.
    intros.
    intro.
    subst A.
    apply H.
    apply midpoint_col_231.
      assumption.
Qed.

End T7_1.

Print All.

