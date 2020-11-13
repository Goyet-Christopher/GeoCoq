Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_FSC.
Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col_transitivity.
Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col_not.


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


Lemma l6_21 : forall A B C D P Q,
  ~ Col A B C -> C<>D 
-> Col A B P -> Col A B Q -> Col C D P -> Col C D Q 
-> P=Q.
Proof.
    intros.
    induction (eq_dec_points P Q).
      assumption.
    apply not_col_distincts in H.
    apply col_perm in H1.
    apply col_perm in H2.
    apply col_perm in H3.
    apply col_perm in H4.
    spliter.
    assert(Q<>P).
      apply diff_symmetry; assumption.
    assert(B<>A).
      apply diff_symmetry; assumption.
    assert (Col C P Q).
      apply col_transitivity_1 with D; assumption.
    assert (Col Q B C).
      apply col_transitivity_1 with P.
        assumption.
        apply col_321. apply col_transitivity_1 with A; assumption.
        apply col_321; assumption.
    assert (Col A B C).
      apply col_perm in H31.
      apply col_perm in H32.
      spliter.
      induction (eq_dec_points Q A).
        subst Q; assumption.
      induction (eq_dec_points Q B).
        subst. apply col_213. 
          apply col_transitivity_1 with P; assumption.
        apply col_213.
          apply col_transitivity_1 with Q; try assumption.
          apply diff_symmetry; assumption.
    contradiction.
Qed.

End T4_4.

Print All.

