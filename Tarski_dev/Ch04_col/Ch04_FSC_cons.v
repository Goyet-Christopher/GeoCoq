Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_FSC.

Section FSC_col_cons.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma FSC_with_cong3_123 : forall A B C D A' B' C' D',
  Col A B C \/ Col A' B' C' ->
  Cong_3 A B C A' B' C' ->
  Cong A D A' D' ->
  Cong B D B' D'-> FSC A B C D A' B' C' D'.
Proof.
    intros.
    split.
      apply l4_13_bis with A' B' C'; assumption.
    apply cong3_to_def in H0. spliter.
    repeat split; try assumption.
Qed.

Lemma FSC_with_cong3_124 : forall A B C D A' B' C' D',
  Col A B C \/ Col A' B' C' ->
  Cong_3 A B D A' B' D' ->
  Cong A C A' C' ->
  Cong B C B' C'-> FSC A B C D A' B' C' D'.
Proof.
    intros.
    apply cong3_to_def in H0. spliter.
    assert(Cong_3 A B C A' B' C').
      apply def_to_cong3; assumption.
    repeat split; try assumption.
    apply l4_13_bis with A' B' C'; assumption.
Qed.

Lemma FSC_with_cong3_134 : forall A B C D A' B' C' D',
  Col A B C \/ Col A' B' C' ->
  Cong_3 A C D A' C' D' ->
  Cong A B A' B' ->
  Cong B C B' C'->
  Cong B D B' D'-> FSC A B C D A' B' C' D'.
Proof.
    intros.
    apply cong3_to_def in H0. spliter.
    assert(Cong_3 A B C A' B' C').
      apply def_to_cong3; assumption.
    repeat split; try assumption.
    apply l4_13_bis with A' B' C'; assumption.
Qed.

Lemma FSC_with_cong3_234 : forall A B C D A' B' C' D',
  Col A B C \/ Col A' B' C' ->
  Cong_3 B C D B' C' D' ->
  Cong A B A' B' ->
  Cong A C A' C'->
  Cong A D A' D'-> FSC A B C D A' B' C' D'.
Proof.
    intros.
    apply cong3_to_def in H0. spliter.
    repeat split; try assumption.
    apply l4_13_bis with A' B' C'.
      assumption.
      apply def_to_cong3; assumption.
Qed.

Lemma FSC_with_cong : forall A B C D A' B' C' D',
  Col A B C \/ Col A' B' C' ->
  Cong A B A' B' ->
  Cong A C A' C' ->
  Cong A D A' D' ->
  Cong B C B' C' ->
  Cong B D B' D' -> FSC A B C D A' B' C' D'.
Proof.
    intros.
    assert(Cong_3 A B C A' B' C').
      apply def_to_cong3; assumption.
    apply def_to_FSC; try assumption.
      apply l4_13_bis with A' B' C'; assumption.
Qed.

End FSC_col_cons.

Section FSC_bet_cons.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma FSC_bet_1213 : forall A B C D A' B' C' D',
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

Lemma FSC_bet_1223 : forall A B C D A' B' C' D',
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

Lemma FSC_bet_1323 : forall A B C D A' B' C' D',
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

Lemma FSC_bet_13_cong3 : forall A B C D A' B' C' D',
  Bet A B C -> Bet A' B' C'
  -> Cong_3 A B D A' B' D'
  -> Cong A C A' C'
  -> FSC A B C D A' B' C' D'.
Proof.
    intros.
    apply cong3_to_def in H1. spliter.
    apply FSC_bet_1213; assumption.
Qed.

Lemma FSC_bet_23_cong3 : forall A B C D A' B' C' D',
  Bet A B C -> Bet A' B' C'
  -> Cong_3 A B D A' B' D'
  -> Cong B C B' C'
  -> FSC A B C D A' B' C' D'.
Proof.
    intros.
    apply cong3_to_def in H1. spliter.
    apply FSC_bet_1223; assumption.
Qed.

Lemma FSC_bet_1424_cong3 : forall A B C D A' B' C' D',
  Bet A B C \/ Bet A' B' C'
  -> Cong_3 A B C A' B' C'
  -> Cong A D A' D'
  -> Cong B D B' D'
  -> FSC A B C D A' B' C' D'.
Proof.
    intros.
    apply def_to_FSC; try assumption.
      apply bet_col_123.
      induction H.
        assumption.
        apply l4_6 with A' B' C'. assumption.
          apply cong3_symmetry. assumption.
Qed.


End FSC_bet_cons.

Section FSC_cons.
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


End FSC_cons.

Print All.

