Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_FSC.


Section T4_4.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma l4_18 : forall A B C C',
  A<>B -> Col A B C 
  -> Cong A C A C' -> Cong B C B C'
  -> C=C'.
Proof.
    intros.
    apply cong_reverse_identity with C.
    apply (l4_17 A B); assumption.
Qed.

Lemma l4_19 : forall A B C C',
 Bet A C B -> Cong A C A C' -> Cong B C B C' -> C=C'.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst. apply between_identity in H.
      subst. apply cong_reverse_identity with C.
      assumption.
    assert(Col A B C).
      apply bet_col_132; assumption.
    apply l4_18 with A B; assumption.
Qed.

Lemma col_cong_3_cong_3_eq : forall A B C A' B' C1 C2,
  A <>B -> Col A B C 
  -> Cong_3 A B C A' B' C1 -> Cong_3 A B C A' B' C2 
  -> C1 = C2.
Proof.
    intros.
    assert(Cong_3 A' B' C1 A' B' C2).
      apply cong3_transitivity_12_13_23 with A B C;
      assumption.
    apply l4_18 with A' B'.
      apply cong_diff_12_34 with A B. assumption.
      apply cong3_12 with C C1. assumption.
      apply l4_13 with A B C; assumption.
    apply H3.
    apply H3.
Qed.

End T4_4.

Print All.

