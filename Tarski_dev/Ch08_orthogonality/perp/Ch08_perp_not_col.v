
Lemma perp_not_col2 : forall A B C D,
 Perp A B C D -> ~ Col A B C \/ ~ Col A B D.
Proof.
    intros.
    induction (Col_dec A B C).
      right.
      assert(Perp_at C A B C D).
        apply l8_14_2_1b_bis; Col.
      intro.
      assert(Perp_at D A B C D).
        apply l8_14_2_1b_bis; Col.
      assert(C = D).
        eapply l8_14_3.
          apply H1.
        assumption.
      apply perp_not_eq_2 in H.
      contradiction.
    left.
    assumption.
Qed.

Lemma perp_not_col : forall A B P,
 Perp A B P A -> ~ Col A B P.
Proof.
    intros.
    assert (Perp_at A A B P A).
      apply perp_perp_in.
      assumption.
    assert (Per P A B).
      apply perp_in_per.
      apply perp_in_sym.
      assumption.
    apply perp_in_left_comm in H0.
    assert (~ Col B A P  -> ~ Col A B P).
      intro.
      intro.
      apply H2.
      apply col_permutation_4.
      assumption.
    apply H2.
    apply perp_distinct in H.
    spliter.
    apply per_not_col.
      auto.
      auto.
    apply perp_in_per.
    apply perp_in_right_comm.
    assumption.
Qed.
