Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col.

Section FSC_def.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma def_to_FSC : forall A B C D A' B' C' D',
  Col A B C ->
  Cong_3 A B C A' B' C' ->
  Cong A D A' D' ->
  Cong B D B' D'-> FSC A B C D A' B' C' D'.
Proof.
    intros.
    repeat (split; try assumption).
Qed.

Lemma FSC_to_def : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' ->  Col A B C /\
  Cong_3 A B C A' B' C' /\
  Cong A D A' D' /\
  Cong B D B' D'.
Proof.
    intros.
    assumption.
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

Lemma FSC_cong3_123 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' ->  Cong_3 A B C A' B' C'.
Proof.
    intros.
    apply H.
Qed.

Lemma FSC_cong3_124 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' ->  Cong_3 A B D A' B' D'.
Proof.
    intros.
    apply FSC_to_def in H. spliter.
    apply cong3_to_def in H0. spliter.
    repeat split; assumption.
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

Lemma FSC_cong : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' -> 
    Cong A B A' B' /\
    Cong A C A' C' /\
    Cong A D A' D' /\
    Cong B C B' C' /\
    Cong B D B' D'.
Proof.
    intros.
    apply FSC_to_def in H.
    spliter.
    apply cong3_to_def in H0.
    spliter.
    repeat split; assumption.
Qed.

End FSC_def.


Section FSC_prop.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

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

Lemma FSC_cong3_134 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' -> A <> B \/ A' <> B' ->  Cong_3 A C D A' C' D'.
Proof.
    intros.
    apply def_to_cong3.
      apply FSC_cong_13 with B D B' D'. assumption.
      apply FSC_cong_14 with B C B' C'. assumption.
      apply FSC_cong_34 with A B A' B'. assumption.
    assumption.
Qed.

Lemma FSC_cong3_234 : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' -> A <> B \/ A' <> B' ->  Cong_3 B C D B' C' D'.
Proof.
    intros.
    apply def_to_cong3.
      apply FSC_cong_23 with A D A' D'. assumption.
      apply FSC_cong_24 with A C A' C'. assumption.
      apply FSC_cong_34 with A B A' B'. assumption.
    assumption.
Qed.


Lemma FSC_cong3_all : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' -> A <> B \/ A' <> B' ->  
  Cong_3 A B C A' B' C' /\ Cong_3 A B D A' B' D' /\
  Cong_3 A C D A' C' D' /\ Cong_3 B C D B' C' D'.
Proof.
    intros.
    split.
      apply FSC_cong3_123 with D D'. assumption.
    split.
      apply FSC_cong3_124 with C C'. assumption.
    split.
      apply FSC_cong3_134 with B B'; assumption.
      apply FSC_cong3_234 with A A'; assumption.
Qed.

Lemma FSC_cong_all : forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' -> A <> B \/ A' <> B'
 -> Cong A B A' B' /\
    Cong A C A' C' /\
    Cong A D A' D' /\
    Cong B C B' C' /\
    Cong B D B' D' /\ 
    Cong C D C' D'.
Proof.
    intros.
    assert(Cong C D C' D').
      apply FSC_cong_34 with A B A' B'; assumption.
    apply FSC_to_def in H. spliter.
    apply cong3_to_def in H2. spliter.
    repeat split; assumption.
Qed.


End T4_4.

Print All.