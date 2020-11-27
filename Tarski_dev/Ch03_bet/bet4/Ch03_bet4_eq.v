Require Export GeoCoq.Tarski_dev.Ch03_bet.bet4.Ch03_bet4_bet.

Section Bet4_eq.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet4_equality : forall A B C D,
  Bet_4 A B C D -> Bet_4 A D C B
  -> B = C /\ C = D.
Proof.
    intros.
    repeat split.
    apply between_equality_2 with A.
      apply H. apply H0.
    apply between_equality_2 with A.
      apply H. apply H0.
Qed.

Lemma bet4_equality_2 : forall A B C,
  Bet_4 A B C A
  -> A = B /\ B = C.
Proof.
    intros.
    assert(A = B).
    apply between_equality_2 with A.
      apply between_trivial_112. 
      apply bet4_bet_124 with C; assumption.
    repeat split.
    assumption.
    subst.
    apply between_identity.
    apply bet4_bet_234 with B.
    assumption.
Qed.

End Bet4_eq.

Print All.

