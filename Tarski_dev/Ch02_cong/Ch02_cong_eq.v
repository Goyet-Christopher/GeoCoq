Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong_transitivity.

Section T1_1.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong_reverse_identity : forall A C D,
 Cong A A C D -> C=D.
Proof.
    intros.
    apply cong_symmetry in H.
    apply (cong_identity C D A).
    assumption.
Qed.

Lemma construction_uniqueness : forall Q A B C X Y,
 Q <> A -> Bet Q A X -> Cong A X B C -> Bet Q A Y -> Cong A Y B C -> X=Y.
Proof.
    intros.
    assert (Cong Q A Q A) by apply cong_1212.
    assert (Cong Q Y Q Y) by apply cong_1212.
    assert (Cong A Y A Y) by apply cong_1212.
    assert (Cong A X A Y).
      apply cong_inner_transitivity_2 with B C; assumption.
    apply cong_identity with Y.
    apply five_segment with Q Q A A; assumption.
Qed.

Lemma construction_uniqueness_sym : forall Q A B C X Y,
 Q <> A -> Bet Q A X -> Cong B C A X -> Bet Q A Y -> Cong B C A Y -> X=Y.
Proof.
    intros.
    apply construction_uniqueness with Q A B C.
    assumption. assumption.
    apply cong_symmetry. assumption.
    assumption.
    apply cong_symmetry. assumption.
Qed.

End T1_1.

Print All.