Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet.

Section Bet_l2_11.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l2_11_reverse : forall A B C A' B' C',
  Bet A B C -> Bet A' B' C' -> Cong A B B' C' -> Cong B C A' B' -> Cong A C A' C'.
Proof.
    intros.
    apply cong_1243.
    apply l2_11 with B B'.
    assumption.
    apply between_symmetry; assumption.
    apply cong_1243; assumption.
    apply cong_1243; assumption.
Qed.

Lemma l2_11_cong3_reverse : forall A B C A' B' C',
  Bet A B C -> Bet A' B' C' -> Cong A B B' C' -> Cong B C A' B' -> Cong_3 A B C C' B' A'.
Proof.
    intros.
    assert(Cong A C A' C').
      apply l2_11_reverse with B B'; assumption.
    apply def_to_cong3_reverse; assumption.
Qed.



End Bet_l2_11.

Print All.