Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet4.

Section Bet5.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma def_to_bet5 : forall A B C D E,
Bet_4 A B C D -> Bet_4 B C D E -> Bet_4 A C D E -> 
Bet_4 A B D E -> Bet_4 A B C E -> Bet_5 A B C D E.
Proof.
    unfold Bet_5.
    intros.
    repeat (split;auto).
Qed.

Lemma bet5_to_def : forall A B C D E,
 Bet_5 A B C D E -> 
Bet_4 A B C D /\ Bet_4 B C D E /\ 
   Bet_4 A C D E /\ Bet_4 A B D E /\ Bet_4 A B C E.
Proof.
    unfold Bet_5.
    intros.
    assumption.
Qed.

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

Lemma bet5_symmetry : forall A B C D E, 
Bet_5 A B C D E -> Bet_5 E D C B A.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    apply def_to_bet5; apply bet4_symmetry; assumption.
Qed.

(*
Lemma bet5_identity : forall A B C D E E',
A<>B -> Bet_5 A B C D E -> Bet_5 A B C D E' -> Cong D E D E' -> E = E'.
Proof.
    intros.
    assert( Bet A D E).
        apply Bet_5_bet145 with B C; assumption.
    assert( Bet A D E').
        apply Bet_5_bet145 with B C; assumption.
    assert( Bet A B D).
        apply Bet_5_bet124 with C E; assumption.
    assert(A <> D).
        apply bet_neq12__neq with B; assumption.
    apply (construction_uniqueness_simple A D E E'); auto with cong.
Qed.
*)

End Bet5.

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

End bet5_cons.

Print All.
