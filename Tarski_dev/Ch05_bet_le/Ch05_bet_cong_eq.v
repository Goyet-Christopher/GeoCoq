Require Export GeoCoq.Tarski_dev.Ch05_bet_le.Ch05_bet_le.

Section T5.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet_cong_eq : forall A B C D,
  Bet A B C -> Bet A C D -> Cong B C A D 
-> C = D /\ A = B.
Proof.
    intros.
    assert(C = D).
      assert(Le A C A D).
        apply bet_le_1213; assumption.
      assert(Le A D A C).
        apply l5_6 with C B C A.
          apply bet_le_3231; assumption.
          apply cong_2134; assumption.
          apply cong_1221.
      assert(Cong A C A D).
        apply le_anti_symmetry; assumption.
      apply between_cong with A; assumption.
    split.
    assumption.
    subst D.
    apply between_cong_reverse with C.
      assumption.
      apply cong_3412; assumption.
Qed.

End T5.

Print All.