Require Export GeoCoq.Tarski_dev.Ch05_bet_le.Ch05_bet_le.

Section T5.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet_cong_eq : forall A B C D,
  Bet A B C -> Bet A C D -> Cong B C A D 
-> A = B /\ C = D.
Proof.
    intros.
    assert(A = B).
      assert(Le B C A C).
        apply bet_le_2313; assumption.
      assert(Le A C B C).
        eapply l5_6 with A C A D.
          apply bet_le_1213; assumption.
          apply cong_1212.
          apply cong_3412. assumption.
      assert(Cong A C B C).
        apply le_anti_symmetry; assumption.
      apply between_cong_reverse with C; assumption.
    split.
    assumption.
    subst A.
      apply between_cong with B; assumption.
Qed.

Lemma bet_cong_eq2 : forall A B C A' B' C',
  Bet A B C -> Cong A B A' B' -> Cong A C A' C'
  -> Bet A' C' B' -> B = C /\ B' = C'.
Proof.
    intros.
    assert (Le A' C' A' B').
      apply def2_to_le.
      exists B'.
      split.
        assumption.
        apply cong_1212.
    assert(Le A' B' A' C').
      apply l5_6 with A B A C.
        apply def2_to_le.
          exists C.
          split.
            assumption.
            apply cong_1212; assumption.
        assumption.
        assumption.
    assert(Cong A' B' A' C').
      apply le_anti_symmetry; assumption.
    assert(C' = B').
      apply between_cong with A'.
        assumption.
        apply cong_3412; assumption.
    split.
      subst B'.
      assert(Cong A B A C).
        apply cong_1234_5634 with A' C'; assumption.
      apply between_cong with A; assumption.
    apply eq_sym. assumption.
Qed.

End T5.

Print All.
