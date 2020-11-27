Require Export GeoCoq.Tarski_dev.Ch03_bet.bet4.Ch03_bet4.

Section Bet4_bet.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma bet4_bet_123 : forall A B C D,
  Bet_4 A B C D 
-> Bet A B C.
Proof.
    intros.
    apply H.
Qed.

Lemma bet4_bet_321 : forall A B C D,
  Bet_4 A B C D 
-> Bet C B A.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.

Lemma bet4_bet_124 : forall A B C D,
  Bet_4 A B C D 
-> Bet A B D.
Proof.
    intros.
    apply H.
Qed.

Lemma bet4_bet_421 : forall A B C D,
  Bet_4 A B C D 
-> Bet D B A.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.

Lemma bet4_bet_234 : forall A B C D,
  Bet_4 A B C D 
-> Bet B C D.
Proof.
    intros.
    apply H.
Qed.

Lemma bet4_bet_432 : forall A B C D,
  Bet_4 A B C D 
-> Bet D C B.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.

Lemma bet4_bet_134 : forall A B C D,
  Bet_4 A B C D 
-> Bet A C D.
Proof.
    intros.
    apply H.
Qed.

Lemma bet4_bet_431 : forall A B C D,
  Bet_4 A B C D 
-> Bet D C A.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.

End Bet4_bet.


Section Bet4_constructors.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet_123_134_bet4 : forall A B C D,
  Bet A B C -> Bet A C D -> Bet_4 A B C D.
Proof.
    intros.
    apply def_to_bet4.
    assumption.
    apply between_exchange_1 with A; assumption.
    assumption.
    apply between_exchange_3 with C; assumption.
Qed.

Lemma bet_124_234_bet4 : forall A B C D,
  Bet A B D -> Bet B C D -> Bet_4 A B C D.
Proof.
    intros.
    apply bet4_symmetry.
    apply bet_123_134_bet4.
    apply between_symmetry; assumption.
    apply between_symmetry; assumption.
Qed.

Lemma bet4_sides : forall A B C D, 
B<>C -> Bet A B C -> Bet B C D -> Bet_4 A B C D.
Proof.
    intros.
    apply def_to_bet4.
    assumption. assumption.
    apply between_outer_transitivity_2 with B; assumption.
    apply between_outer_transitivity_3 with C; assumption.
Qed.

Lemma bet4_sides2 : forall A B C D E, 
 Bet A C E -> Bet A B C -> Bet C D E -> Bet_4 A B D E.
Proof.
    intros.
    apply bet_124_234_bet4.
      apply between_exchange_3 with C; assumption.
    assert(Bet B C E).
      apply between_exchange_1 with A; assumption.
      apply between_exchange_2 with C; assumption.
Qed.


End Bet4_constructors.

Print All.

