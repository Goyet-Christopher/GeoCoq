Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col_transitivity.

Section T4_4.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma not_col_distincts : forall A B C ,
 ~ Col A B C ->
 ~ Col A B C /\ A <> B /\ B <> C /\ A <> C.
Proof.
    intros.
    repeat split;(auto;intro); subst; apply H.
    apply col_trivial_112.
    apply col_trivial_122.
    apply col_trivial_121.
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

End T4_4.

Print All.