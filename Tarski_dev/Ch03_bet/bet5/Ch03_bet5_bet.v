Require Export GeoCoq.Tarski_dev.Ch03_bet.bet5.Ch03_bet5_bet4.
Require Export GeoCoq.Tarski_dev.Ch03_bet.bet4.Ch03_bet4_bet.

Section Bet5_bet.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma all_to_bet5 : forall A B C D E,
  Bet A B C -> Bet A B D -> Bet A B E ->
               Bet A C D -> Bet A C E ->
               Bet A D E ->
               Bet B C D -> Bet B C E ->
               Bet B D E ->
               Bet C D E
 -> Bet_5 A B C D E.
Proof.
    intros.
    unfold Bet_5.
    unfold Bet_4.
    repeat split; assumption.
Qed.

Lemma bet5_to_all : forall A B C D E,
 Bet_5 A B C D E -> Bet A B C /\ Bet A B D /\ Bet A B E /\
                    Bet A C D /\ Bet A C E /\
                    Bet A D E /\
                    Bet B C D /\ Bet B C E /\
                    Bet B D E /\
                    Bet C D E.
Proof.
    unfold Bet_5.
    unfold Bet_4.
    intros.
    spliter.
    repeat split; assumption.
Qed.


Lemma bet5_bet_123 : forall A B C D E,
Bet_5 A B C D E -> Bet A B C.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    apply bet4_bet_123 with D.
    assumption.
Qed.

Lemma bet5_bet_124 : forall A B C D E,
Bet_5 A B C D E -> Bet A B D.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    apply bet4_bet_124 with C.
    assumption.
Qed.

Lemma bet5_bet_125 : forall A B C D E,
Bet_5 A B C D E -> Bet A B E.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    apply bet4_bet_124 with C.
    assumption.
Qed.

Lemma bet5_bet_134 : forall A B C D E,
Bet_5 A B C D E -> Bet A C D.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    apply bet4_bet_123 with E.
    assumption.
Qed.

Lemma bet5_bet_135 : forall A B C D E,
Bet_5 A B C D E -> Bet A C E.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    apply bet4_bet_134 with B.
    assumption.
Qed.

Lemma bet5_bet_145 : forall A B C D E,
Bet_5 A B C D E -> Bet A D E.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    apply bet4_bet_134 with B.
    assumption.
Qed.

Lemma bet5_bet_234 : forall A B C D E,
Bet_5 A B C D E -> Bet B C D.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    apply bet4_bet_234 with A.
    assumption.
Qed.

Lemma bet5_bet_235 : forall A B C D E,
Bet_5 A B C D E -> Bet B C E.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    apply bet4_bet_234 with A.
    assumption.
Qed.

Lemma bet5_bet_245 : forall A B C D E,
Bet_5 A B C D E -> Bet B D E.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    apply bet4_bet_234 with A.
    assumption.
Qed.

Lemma bet5_bet_345 : forall A B C D E,
Bet_5 A B C D E -> Bet C D E.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    apply bet4_bet_234 with B.
    assumption.
Qed.

End Bet5_bet.

Section Bet5_cons.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet5_bet_1 : forall A B C D E,
  Bet A C E -> Bet A B C -> Bet C D E
 -> Bet_5 A B C D E.
Proof.
    intros.
    assert(Bet_4 A B C E).
      apply bet_123_134_bet4; assumption.
    assert(Bet_4 A C D E).
      apply bet_124_234_bet4; assumption.
    apply bet5_bet4_24; assumption.
Qed.

Lemma bet5_bet_2 : forall A B C D E,
 Bet A B C -> Bet A D E -> Bet A C D
-> Bet_5 A B C D E.
Proof.
    intros.
    assert(Bet_4 A C D E).
      apply bet_123_134_bet4; assumption.
    assert(Bet_4 A B C D).
      apply bet_123_134_bet4; assumption.
    apply bet5_bet4_25; assumption.
Qed.

Lemma bet5_bet_3 : forall A B C D E,
C<>D -> Bet A B C -> Bet A C D -> Bet C D E
-> Bet_5 A B C D E.
Proof.
    intros.
    assert(Bet_4 A B C D).
      apply bet_123_134_bet4; assumption.
    assert(Bet_4 A C D E).
      apply bet4_sides; assumption.
    apply bet5_bet4_25; assumption.
Qed.

Lemma bet5_bet_4 : forall A B C D E,
 Bet B C D -> Bet A B D -> Bet A D E
-> Bet_5 A B C D E.
Proof.
    intros.
    assert(Bet_4 A B D E).
      apply bet_123_134_bet4; assumption.
    assert(Bet_4 A B C D).
      apply bet_124_234_bet4; assumption.
    apply bet5_bet4_35; assumption.
Qed.

Lemma bet5_bet_5 : forall A B C D E,
 Bet B C D -> Bet B D E -> Bet A B E
-> Bet_5 A B C D E.
Proof.
    intros.
    assert(Bet_4 B C D E).
      apply bet_123_134_bet4; assumption.
    assert(Bet_4 A B D E).
      apply bet_124_234_bet4; assumption.
    apply bet5_bet4_13; assumption.
Qed.

End Bet5_cons.

Print All.


