Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col_transitivity.

Section T4_4.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma not_col_distincts_12 : forall A B C,
 ~ Col A B C -> A <> B.
Proof.
    intros.
    intro.
    subst.
    apply H.
    apply col_trivial_112.
Qed.

Lemma not_col_distincts_13 : forall A B C,
 ~ Col A B C -> A <> C.
Proof.
    intros.
    intro.
    subst.
    apply H.
    apply col_trivial_121.
Qed.

Lemma not_col_distincts_23 : forall A B C,
 ~ Col A B C -> B <> C.
Proof.
    intros.
    intro.
    subst.
    apply H.
    apply col_trivial_122.
Qed.

Lemma not_col_distincts : forall A B C,
 ~ Col A B C ->
 ~ Col A B C /\ A <> B /\ B <> C /\ A <> C.
Proof.
    intros.
    repeat split.
      assumption.
      apply not_col_distincts_12 with C. assumption.
      apply not_col_distincts_23 with A. assumption.
      apply not_col_distincts_13 with B. assumption.
Qed.

Lemma col_not_col_diff : forall A B X Y,
  Col A B X -> ~ Col A B Y -> X<>Y.
Proof.
    intros.
    intro.
    subst.
    apply H0.
    assumption.
Qed.

Lemma cong2_not_col_diff : forall A B C X Y,
  ~ Col A B C -> Cong A C A X -> Cong A X X Y
-> A <> X.
Proof.
    intros.
    intro.
    subst A.
    assert(X = Y).
      apply cong_reverse_identity with X. assumption.
    subst.
    assert(Y = C).
      apply cong_identity with Y. assumption.
    subst.
    apply not_col_distincts in H. spliter.
    contradiction.
Qed.

End T4_4.

Print All.