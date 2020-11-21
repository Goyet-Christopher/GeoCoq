Require Export GeoCoq.Tarski_dev.Ch03_bet.bet4.Ch03_bet4.

Section Bet4_l2_11.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l2_11_bet4_123 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B A' B' -> Cong B C B' C' -> Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D' /\ Cong A D A' D'.
Proof.
    intros.
      apply bet4_to_def in H.
      apply bet4_to_def in H0.
      spliter.
    assert(Cong A C A' C').
      apply l2_11 with B B'; assumption.
    assert(Cong A D A' D').
      apply l2_11 with C C'; assumption.
    assert(Cong B D B' D').
      apply l2_11 with C C'; assumption.
    split.
    apply def_to_cong4; assumption.
    assumption.
Qed.

Lemma l2_11_bet4_132 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B A' B' -> Cong B C C' D' -> Cong C D B' C'
  -> Cong_3 A B D A' B' D' /\ Cong_3 B C D D' C' B' /\ Cong A D A' D'.
Proof.
    intros.
      apply bet4_to_def in H.
      apply bet4_to_def in H0.
      spliter.
    assert(Cong B D B' D').
      apply l2_11_reverse with C C'; assumption.
    assert(Cong A D A' D').
      apply l2_11 with B B'; assumption.
    split.
      apply def_to_cong3; assumption.
    split.
      apply def_to_cong3_reverse; assumption.
      assumption.
Qed.

Lemma l2_11_bet4_213 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B B' C' -> Cong B C A' B' -> Cong C D C' D'
  -> Cong_3 A C D A' C' D' /\ Cong_3 A B C C' B' A' /\ Cong A D A' D'.
Proof.
    intros.
      apply bet4_to_def in H.
      apply bet4_to_def in H0.
      spliter.
    assert(Cong A C A' C').
      apply l2_11_reverse with B B'; assumption.
    assert(Cong A D A' D').
      apply l2_11 with C C'; assumption.
    split.
      apply def_to_cong3; assumption.
    split.
      apply def_to_cong3_reverse; assumption.
      assumption.
Qed.

Lemma l2_11_bet4_231 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B B' C' -> Cong B C C' D' -> Cong C D A' B'
  -> Cong_3 A C D D' B' A' /\ Cong_3 A B C B' C' D' /\ Cong A D A' D'.
Proof.
    intros.
      apply bet4_to_def in H.
      apply bet4_to_def in H0.
      spliter.
    assert(Cong A C B' D').
      apply l2_11 with B C'; assumption.
    assert(Cong A D A' D').
      apply l2_11_reverse with C B'; assumption.
    split.
      apply def_to_cong3_reverse; assumption.
    split.
      apply def_to_cong3; assumption.
      assumption.
Qed.

Lemma l2_11_bet4_312 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B C' D' -> Cong B C A' B' -> Cong C D B' C'
  -> Cong_3 A B D D' C' A' /\ Cong_3 B C D A' B' C' /\ Cong A D A' D'.
Proof.
    intros.
      apply bet4_to_def in H.
      apply bet4_to_def in H0.
      spliter.
    assert(Cong B D A' C').
      apply l2_11 with C B'; assumption.
    assert(Cong A D A' D').
      apply l2_11_reverse with B C'; assumption.
    split.
      apply def_to_cong3_reverse; assumption.
    split.
      apply def_to_cong3; assumption.
      assumption.
Qed.


Lemma l2_11_bet4_321 : forall A B C D A' B' C' D',
    Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B C' D' -> Cong B C B' C' -> Cong C D A' B'
  -> Cong_4 A B C D D' C' B' A' /\ Cong A D A' D'.
Proof.
    intros.
      apply bet4_to_def in H.
      apply bet4_to_def in H0.
      spliter.
    assert(Cong B D A' C').
      apply l2_11_reverse with C B'; assumption.
    assert(Cong A C B' D').
      apply l2_11_reverse with B C'; assumption.
    assert(Cong A D A' D').
      apply l2_11_reverse with C B'; assumption.
    split.
      apply def_to_cong4_reverse; assumption.
      apply l2_11_reverse with B C'; assumption.
Qed.

End Bet4_l2_11.

Print All.