Require Export GeoCoq.Tarski_dev.Ch03_bet.bet5.Ch03_bet5.

Section Bet5_bet4.
Context `{Tn:Tarski_neutral_dimensionless}.


Lemma bet5_bet4_1234 : forall A B C D E,
 Bet_5 A B C D E -> Bet_4 A B C D.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    assumption.
Qed.

Lemma bet5_bet4_2345 : forall A B C D E,
 Bet_5 A B C D E -> Bet_4 B C D E.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    assumption.
Qed.

Lemma bet5_bet4_1345 : forall A B C D E,
 Bet_5 A B C D E -> Bet_4 A C D E.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    assumption.
Qed.

Lemma bet5_bet4_1245 : forall A B C D E,
 Bet_5 A B C D E -> Bet_4 A B D E.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    assumption.
Qed.

Lemma bet5_bet4_1235 : forall A B C D E,
 Bet_5 A B C D E -> Bet_4 A B C E.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    assumption.
Qed.

End Bet5_bet4.


Section bet5_cons.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet5_bet4_13 : forall A B C D E,
  Bet_4 B C D E -> Bet_4 A B D E 
  -> Bet_5 A B C D E.
Proof.
    intros.
    assert(Bet_4 A C D E /\ Bet_4 A B C D /\ Bet_4 A B C E).
        apply bet4_transitivity_13; assumption.
    spliter.
    apply def_to_bet5; assumption.
Qed.

Lemma bet5_bet4_14 : forall A B C D E,
  Bet_4 B C D E -> Bet_4 A B C E 
  -> Bet_5 A B C D E.
Proof.
    intros.
    assert(Bet_4 A C D E /\ Bet_4 A B D E /\ Bet_4 A B C D).
        apply bet4_transitivity_14; assumption.
    spliter.
    apply def_to_bet5; assumption.
Qed.

Lemma bet5_bet4_15 : forall A B C D E,
  B <> C \/ B <> D \/ C <> D -> Bet_4 A B C D -> Bet_4 B C D E 
  -> Bet_5 A B C D E.
Proof.
    intros.
    assert(Bet_4 A C D E /\ Bet_4 A B D E /\ Bet_4 A B C E).
        apply bet4_transitivity_15; assumption.
    spliter.
    apply def_to_bet5; assumption.
Qed.


Lemma bet5_bet4_24 : forall A B C D E,
  Bet_4 A C D E -> Bet_4 A B C E 
  -> Bet_5 A B C D E.
Proof.
    intros.
    assert(Bet_4 A B C D /\ Bet_4 A B D E /\ Bet_4 B C D E).
        apply bet4_transitivity_24; assumption.
    spliter.
    apply def_to_bet5; assumption.
Qed.


Lemma bet5_bet4_25 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 A C D E -> Bet_5 A B C D E.
Proof.
    intros.
    assert(Bet_4 B C D E /\ Bet_4 A B D E /\ Bet_4 A B C E).
        apply bet4_transitivity_25; assumption.
    spliter.
    apply def_to_bet5; assumption.
Qed.

Lemma bet5_bet4_35 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 A B D E 
  -> Bet_5 A B C D E.
Proof.
    intros.
    assert(Bet_4 B C D E /\ Bet_4 A C D E /\ Bet_4 A B C E).
        apply bet4_transitivity_35; assumption.
    spliter.
    apply def_to_bet5; assumption.
Qed.

End bet5_cons.


Print All.
