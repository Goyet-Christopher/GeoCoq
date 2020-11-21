Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col.

Section FSC_def.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma FSC_to_def : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' ->  Col A B C /\
  Cong_3 A B C A' B' C' /\
  Cong A D A' D' /\
  Cong B D B' D'.
Proof.
    intros.
    assumption.
Qed.

Lemma def_to_FSC : forall A B C D A' B' C' D',
  Col A B C ->
  Cong_3 A B C A' B' C' ->
  Cong A D A' D' ->
  Cong B D B' D'-> FSC A B C D A' B' C' D'.
Proof.
    intros.
    repeat (split; try assumption).
Qed.

Lemma FSC_col1 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' ->  Col A B C.
Proof.
    intros.
    apply H.
Qed.

Lemma FSC_col2 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' ->  Col A' B' C'.
Proof.
    intros.
    apply FSC_to_def in H.
    spliter.
    apply l4_13 with A B C; assumption.
Qed.

Lemma FSC_cong3 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' ->  Cong_3 A B C A' B' C'.
Proof.
    intros.
    apply H.
Qed.

Lemma FSC_cong_12 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' ->  Cong A B A' B'.
Proof.
    intros.
    apply H.
Qed.

Lemma FSC_cong_13 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' ->  Cong A C A' C'.
Proof.
    intros.
    apply H.
Qed.

Lemma FSC_cong_14 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' ->  Cong A D A' D'.
Proof.
    intros.
    apply H.
Qed.

Lemma FSC_cong_23 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' ->  Cong B C B' C'.
Proof.
    intros.
    apply H.
Qed.

Lemma FSC_cong_24 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' ->  Cong B D B' D'.
Proof.
    intros.
    apply H.
Qed.

End FSC_def.

Section FSC_cons.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma FSC_cons_1213 : forall A B C D A' B' C' D',
  Bet A B C -> Bet A' B' C'
  -> Cong A B A' B'
  -> Cong A C A' C'
  -> Cong A D A' D'
  -> Cong B D B' D'
  -> FSC A B C D A' B' C' D'.
Proof.
    intros.
    apply def_to_FSC.
    apply bet_col_123. assumption.
    apply bet_cong1213_cong3; assumption.
    assumption.
    assumption.
Qed.

Lemma FSC_cons_1223 : forall A B C D A' B' C' D',
  Bet A B C -> Bet A' B' C'
  -> Cong A B A' B'
  -> Cong B C B' C'
  -> Cong A D A' D'
  -> Cong B D B' D'
  -> FSC A B C D A' B' C' D'.
Proof.
    intros.
    apply def_to_FSC.
    apply bet_col_123. assumption.
    apply bet_cong1223_cong3; assumption.
    assumption.
    assumption.
Qed.

Lemma FSC_cons_1323 : forall A B C D A' B' C' D',
  Bet A B C -> Bet A' B' C'
  -> Cong A C A' C'
  -> Cong B C B' C'
  -> Cong A D A' D'
  -> Cong B D B' D'
  -> FSC A B C D A' B' C' D'.
Proof.
    intros.
    apply def_to_FSC.
    apply bet_col_123. assumption.
    apply bet_cong1323_cong3; assumption.
    assumption.
    assumption.
Qed.

End FSC_cons.

Section FSC_prop.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma OFSC_to_FSC_1 : forall A B C D A' B' C' D',
  OFSC A B C D A' B' C' D' -> FSC A B C D A' B' C' D'.
Proof.
    intros.
    apply OFSC_to_def in H.
    spliter.
    split. apply bet_col_123 in H; assumption.
    split. apply bet_cong1223_cong3; assumption.
    repeat split; assumption.
Qed.

Lemma OFSC_to_FSC_2 : forall A B C D A' B' C' D',
  OFSC B A C D B' A' C' D' -> FSC A B C D A' B' C' D'.
Proof.
    intros.
    apply OFSC_to_def in H.
    spliter.
    split. apply bet_col_213; assumption.
    split. apply cong3_swap_213.
    apply bet_cong1223_cong3; assumption.
    split ; assumption.
Qed.

Lemma IFSC_to_FSC : forall A B C D A' B' C' D',
  IFSC A C B D A' C' B' D' -> FSC A B C D A' B' C' D'.
Proof.
    intros.
    apply IFSC_cong3 in H.
    spliter.
    split.
    apply bet_col_132; assumption.
    split. apply cong3_swap_132; assumption.
    split. apply cong3_1346 with B B'; assumption.
    apply cong3_2356 with A A'; assumption.
Qed.

Lemma FSC_cases : forall A B C D A' B' C' D',
  OFSC A B C D A' B' C' D'
  \/ OFSC B A C D B' A' C' D'
  \/ IFSC A C B D A' C' B' D'
 -> FSC A B C D A' B' C' D'.
Proof.
    intros.
    induction H.
    apply OFSC_to_FSC_1; assumption.
    induction H.
    apply OFSC_to_FSC_2; assumption.
    apply IFSC_to_FSC; assumption.
Qed.

Lemma FSC_bet_123 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' -> Bet A B C
  -> OFSC A B C D A' B' C' D'.
Proof.
    intros.
    apply FSC_to_def in H.
    spliter.
    assert(Bet A' B' C').
      apply l4_6 with A B C; assumption.
    apply cong3_to_def in H1.
    spliter.
    apply def_to_OFSC; assumption.
Qed.

Lemma FSC_bet_231 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' -> Bet A C B
  -> IFSC A C B D A' C' B' D'.
Proof.
    intros.
    apply FSC_to_def in H.
    spliter.
    assert(Bet A' C' B').
      apply l4_6_bet_132 with A B C; assumption.
    apply cong3_to_def in H1.
    spliter.
    apply cong_2143 in H6.
    apply def_to_IFSC; assumption.
Qed.

Lemma FSC_bet_312 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' -> Bet B A C
  -> OFSC B A C D B' A' C' D'.
Proof.
    intros.
    apply FSC_to_def in H.
    spliter.
    assert(Bet B' A' C').
      apply l4_6_bet_213 with A B C; assumption.
    apply cong3_to_def in H1.
    spliter.
    apply cong_2143 in H1.
    apply def_to_OFSC; assumption.
Qed.

End FSC_prop.

Section T4_4.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l4_16 : forall A B C D A' B' C' D',
   FSC A B C D A' B' C' D' -> A<>B \/ A'<>B' -> Cong C D C' D'.
Proof.
    intros.
    assert(Col A B C).
      apply H.
    apply col_to_def in H1.
    induction H1.
    apply OFSC_cong_34 with A B A' B'.
    apply FSC_bet_123; assumption.
    assumption.
    induction H1.
    apply IFSC_cong_24 with A B A' B'.
    apply FSC_bet_231; assumption.
    apply OFSC_cong_34 with B A B' A'.
    apply FSC_bet_312; assumption.
      induction H0.
      left. apply diff_symmetry; assumption.
      right. apply diff_symmetry; assumption.
Qed.

Definition FSC_cong_34 A B C D A' B' C' D' :=
    l4_16 A B C D A' B' C' D' .

Lemma l4_17 : forall A B C P Q,
  A<>B -> Col A B C 
  -> Cong A P A Q -> Cong B P B Q 
  -> Cong C P C Q.
Proof.
    intros.
    assert (FSC A B C P A B C Q).
      induction H0.
        apply OFSC_to_FSC_1.
        apply OFSC_axial_sym; assumption.
      induction H0.
        apply IFSC_to_FSC.
        apply IFSC_axial_sym; assumption.
      apply OFSC_to_FSC_2.
      apply OFSC_axial_sym; assumption.
    apply l4_16 with A B A B.
      assumption.
      left. assumption.
Qed.

End T4_4.

Print All.