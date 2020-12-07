Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_final.

Section T2_1.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma col_to_def : forall A B C, 
  Col A B C -> Bet A B C \/ Bet A C B \/ Bet B A C.
Proof.
    intros.
    assumption.
Qed.

Lemma col_to_all : forall A B C, 
  Col A B C -> (Bet A B C /\ Bet C B A) 
            \/ (Bet A C B /\ Bet B C A)
            \/ (Bet B A C /\ Bet C A B).
Proof.
    intros.
    induction H.
      left. split.
        assumption.
        apply between_symmetry. assumption.
    induction H.
      right. left. split.
        assumption.
        apply between_symmetry. assumption.
      right. right. split.
        assumption.
        apply between_symmetry. assumption.
Qed.

Lemma def_to_col : forall A B C, 
  Bet A B C \/ Bet A C B \/ Bet B A C -> Col A B C.
Proof.
    intros.
    assumption.
Qed.

Lemma bet_col_123 : forall A B C, 
  Bet A B C -> Col A B C.
Proof.
    intros.
    apply def_to_col.
    left.
    assumption.
Qed.

Lemma bet_col_132 : forall A B C, 
  Bet A C B -> Col A B C.
Proof.
    intros.
    apply def_to_col.
    right. left.
    assumption.
Qed.

Lemma bet_col_213 : forall A B C, 
  Bet B A C -> Col A B C.
Proof.
    intros.
    apply def_to_col.
    right. right.
    assumption.
Qed.

Lemma bet_col_231 : forall A B C, 
  Bet B C A -> Col A B C.
Proof.
    intros.
    apply def_to_col.
    right. left.
    apply between_symmetry.
    assumption.
Qed.

Lemma bet_col_312 : forall A B C, 
  Bet C A B -> Col A B C.
Proof.
    intros.
    apply def_to_col.
    right. right.
    apply between_symmetry.
    assumption.
Qed.

Lemma bet_col_321 : forall A B C, 
  Bet C B A -> Col A B C.
Proof.
    intros.
    apply def_to_col.
    left.
    apply between_symmetry.
    assumption.
Qed.


End T2_1.

Section T4_1.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma col_231 : forall A B C,
  Col A B C -> Col B C A.
Proof.
    intros.
    repeat induction H.
    apply bet_col_312; assumption.
    apply bet_col_321; assumption.
    apply bet_col_132; assumption.
Qed.

Lemma col_312 : forall A B C, 
  Col A B C -> Col C A B.
Proof.
    intros.
    apply col_231.
    apply col_231.
    assumption.
Qed.

Lemma col_321 : forall A B C, 
  Col A B C -> Col C B A.
Proof.
    intros.
    repeat induction H.
    apply bet_col_321; assumption.
    apply bet_col_312; assumption.
    apply bet_col_231; assumption.
Qed.

Lemma col_213 : forall A B C, 
  Col A B C -> Col B A C.
Proof.
    intros.
    apply col_231.
    apply col_321.
    assumption.
Qed.

Lemma col_132 : forall A B C, 
  Col A B C -> Col A C B.
Proof.
    intros.
    apply col_312.
    apply col_321.
    assumption.
Qed.

End T4_1.


Section T4_3.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma col_cases : forall A B C,
 Col A B C \/ Col A C B \/ Col B A C \/
 Col B C A \/ Col C A B \/ Col C B A ->
 Col A B C.
Proof.
    intros.
    induction H.
    assumption.
    induction H.
    apply col_132; assumption.
    induction H.
    apply col_213; assumption.
    induction H.
    apply col_312; assumption.
    induction H.
    apply col_231; assumption.
    apply col_321; assumption.
Qed.

Lemma col_perm : forall A B C,
 Col A B C ->
 Col A B C /\ Col A C B /\ Col B A C /\
 Col B C A /\ Col C A B /\ Col C B A.
Proof.
    intros.
    repeat split.
    assumption.
    apply col_132; assumption.
    apply col_213; assumption.
    apply col_231; assumption.
    apply col_312; assumption.
    apply col_321; assumption.
Qed.

Lemma col_trivial_112 : forall A B, 
  Col A A B.
Proof.
    intros.
    apply bet_col_123.
    apply between_trivial_112.
Qed.

Lemma col_trivial_122 : forall A B, 
  Col A B B.
Proof.
    intros.
    apply bet_col_123.
    apply between_trivial_122.
Qed.

Lemma col_trivial_121 : forall A B, 
  Col A B A.
Proof.
    intros.
    apply col_132.
    apply col_trivial_112.

Qed.


End T4_3.

Section col_bet_cases.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma fourth_point : forall A B C P,
  A <> B -> B <> C -> Col A B P -> Bet A B C ->
  Bet P A B \/ Bet A P B \/ Bet B P C \/ Bet B C P.
Proof.
    intros.
    induction H1.
      assert(HH:= l5_2 A B C P H H2 H1).
      right. right. 
      apply disjunction_commutativity. assumption.
    induction H1.
      right. left. assumption.
    left. apply between_symmetry. assumption.
Qed.

End col_bet_cases.


Section col_cons.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma col_exchange_1 : forall A B C D,
  Bet A B C -> Bet A C D -> Col B C D.
Proof.
    intros.
    assert(Bet B C D).
      apply between_exchange_1 with A; assumption.
    apply bet_col_123. assumption.
Qed.

Lemma col_exchange_2 : forall A B C D,
  Bet A B D -> Bet B C D -> Col A C D.
Proof.
    intros.
    assert(Bet A C D).
      apply between_exchange_2 with B; assumption.
    apply bet_col_123. assumption.
Qed.

Lemma col_exchange_3 : forall A B C D,
  Bet A B C -> Bet A C D -> Col A B D.
Proof.
    intros.
    assert(Bet A B D).
      apply between_exchange_3 with C; assumption.
    apply bet_col_123. assumption.
Qed.

Lemma col_exchange_4 : forall A B C D,
  Bet A B D -> Bet B C D -> Col A B C.
Proof.
    intros.
    assert(Bet A B C).
      apply between_exchange_4 with D; assumption.
    apply bet_col_123. assumption.
Qed.

Lemma col_outer_transitivity_2 : forall A B C D,
  B <> C -> Bet A B C -> Bet B C D -> Col A C D.
Proof.
    intros.
    assert(Bet A C D).
      apply between_outer_transitivity_2 with B; assumption.
    apply bet_col_123. assumption.
Qed.

Lemma col_outer_transitivity_3 : forall A B C D,
  B <> C -> Bet A B C -> Bet B C D -> Col A B D.
Proof.
    intros.
    assert(Bet A B D).
      apply between_outer_transitivity_3 with C; assumption.
    apply bet_col_123. assumption.
Qed.

Lemma col_inner : forall A B C D E,
  Bet A C E -> Bet A B C -> Bet C D E -> Col B C D.
Proof.
    intros.
    assert(Bet B C D).
      apply between_inner with A E; assumption.
    apply bet_col_123. assumption.
Qed.

Lemma col_inner_2 : forall A B C D E,
  Bet A B E -> Bet A D E -> Bet B C D -> Col A C E.
Proof.
    intros.
    assert(Bet A C E).
      apply between_inner_2 with B D; assumption.
    apply bet_col_123. assumption.
Qed.

Lemma bet2_col_1 : forall A B C D,
  A <> B -> Bet A B C -> Bet A B D -> Col B C D.
Proof.
    intros.
    assert(Bet B C D \/ Bet B D C ).
      apply l5_2 with A; assumption.
    induction H2.
      apply bet_col_123. assumption.
      apply bet_col_132. assumption.
Qed.

Lemma bet2_col_2 : forall A B C D,
  A <> B -> Bet A B C -> Bet A B D -> Col A C D.
Proof.
    intros.
    assert(Bet A C D \/ Bet A D C).
      apply l5_1 with B; assumption.
    induction H2.
      apply bet_col_123. assumption.
      apply bet_col_132. assumption.
Qed.

Lemma bet2_col_4 : forall A B C D,
  Bet A B D -> Bet A C D -> Col A B C.
Proof.
    intros.
    assert(Bet A B C \/ Bet A C B).
      apply l5_3 with D; assumption.
    induction H1.
      apply bet_col_123. assumption.
      apply bet_col_132. assumption.
Qed.

Lemma bet3_col_45 : forall A B C D E,
  A<>B-> Bet A B E -> Bet A B C -> Bet A D E -> Col A C D.
Proof.
    intros.
    assert(Bet A C D \/ Bet A D C).
      apply l5_4 with B E; assumption.
    induction H3.
      apply bet_col_123. assumption.
      apply bet_col_132. assumption.
Qed.


Lemma OFSC_col1 : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Col A B C.
Proof.
    intros.
    apply bet_col_123.
    apply OFSC_bet1 with D A' B' C' D'.
    assumption.
Qed.

Lemma OFSC_col2 : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Col A' B' C'.
Proof.
    intros.
    apply bet_col_123.
    apply OFSC_bet2 with A B C D D'.
    assumption.
Qed.

Lemma IFSC_col1 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Col A B C.
Proof.
    intros.
    apply bet_col_123.
    apply IFSC_bet1 with D A' B' C' D'.
    assumption.
Qed.

Lemma IFSC_col2 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Col A' B' C'.
Proof.
    intros.
    apply bet_col_123.
    apply IFSC_bet2 with A B C D D'.
    assumption.
Qed.

Lemma l4_13 : forall A B C A' B' C',
 Col A B C -> Cong_3 A B C A' B' C' -> Col A' B' C'.
Proof.
    intros.
    repeat induction H.
    apply bet_col_123.
    apply l4_6 with A B C; assumption.
    apply bet_col_132.
    apply l4_6_bet_132 with A B C; assumption.
    apply bet_col_213.
    apply l4_6_bet_213 with A B C; assumption.
Qed.

Lemma l4_13_bis  : forall A B C A' B' C',
 Col A B C \/ Col A' B' C' -> Cong_3 A B C A' B' C' -> Col A B C.
Proof.
    intros.
    induction H.
      assumption.
      apply l4_13 with A' B' C'.
        assumption.
        apply cong3_symmetry. assumption.
Qed.

End col_cons.



Print All.
