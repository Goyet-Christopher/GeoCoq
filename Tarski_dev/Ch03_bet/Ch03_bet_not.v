Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_eq.

Section T2_1.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma not_bet_symmetry : forall A B C,
  ~ Bet A B C -> ~ Bet C B A.
Proof.
    intros.
    intro. apply H.
    apply between_symmetry. assumption.
Qed.

Lemma not_bet_213 : forall A B C,
  A <> B -> Bet A B C -> ~ Bet B A C.
Proof.
    intros.
    intro.
    apply H.
    apply between_equality with C; assumption.
Qed.

Lemma not_bet_312 : forall A B C,
  A <> B -> Bet A B C -> ~ Bet C A B.
Proof.
    intros.
    intro.
    apply H.
    apply between_equality with C.
      assumption.
      apply between_symmetry; assumption.
Qed.

Lemma not_bet_distincts : forall A B C, 
  ~ Bet A B C -> A <> B /\ B <> C.
Proof.
    intros A B C HNBet. 
    repeat split; intro; subst B; apply HNBet.
      apply between_trivial_112.
      apply between_trivial_122.
Qed.

Lemma lower_dim_and :
  exists A B C, ~ Bet A B C /\ ~ Bet B C A /\ ~ Bet C A B.
Proof.
  assert(H:=lower_dim).
    exists_and H A.
    exists_and H0 B.
    exists_and H C.
    exists A, B, C.
    repeat split; intro; apply H0.
    left; assumption.
    right; left; assumption.
    right; right; assumption.
Qed.

End T2_1.

Print All.