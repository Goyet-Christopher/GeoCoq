Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_final.

Section T2_1.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma col_to_def : forall A B C, 
  Col A B C -> Bet A B C \/ Bet A C B \/ Bet B A C.
Proof.
    intros.
    assumption.
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

Lemma Col_cases : forall A B C,
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

Lemma Col_perm : forall A B C,
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

Section OFSC_IFSC.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

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

End OFSC_IFSC.

Section T4_4.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

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

End T4_4.

Print All.
