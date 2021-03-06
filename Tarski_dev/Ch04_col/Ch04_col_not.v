Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col_transitivity.


Section T4_2.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma not_col_231 : forall (A B C : Tpoint), 
  ~ Col A B C -> ~ Col B C A.
Proof.
    intros.
    intro.
    apply H.
    apply col_312.
    assumption.
Qed.

Lemma not_col_312 : forall (A B C : Tpoint), 
  ~ Col A B C -> ~ Col C A B.
Proof.
    intros.
    intro.
    apply H.
    apply col_231.
    assumption.
Qed.

Lemma not_col_321 : forall (A B C : Tpoint), 
  ~ Col A B C -> ~ Col C B A.
Proof.
    intros.
    intro.
    apply H.
    apply col_321.
    assumption.
Qed.

Lemma not_col_213 : forall (A B C : Tpoint), 
  ~ Col A B C -> ~ Col B A C.
Proof.
    intros.
    intro.
    apply H.
    apply col_213.
    assumption.
Qed.

Lemma not_col_132 : forall (A B C : Tpoint), 
  ~ Col A B C -> ~ Col A C B.
Proof.
    intros.
    intro.
    apply H.
    apply col_132.
    assumption.
Qed.

End T4_2.



Section T4_4.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma not_col_cases : forall A B C,
 ~ Col A B C \/ ~ Col A C B \/ ~ Col B A C \/
 ~ Col B C A \/ ~ Col C A B \/ ~ Col C B A 
-> ~ Col A B C.
Proof.
    intros.
    induction H. assumption.
    induction H. apply not_col_132. assumption.
    induction H. apply not_col_213. assumption.
    induction H. apply not_col_312. assumption.
    induction H. apply not_col_231. assumption.
    apply not_col_321. assumption.
Qed.

Lemma not_col_perm : forall A B C,
 ~ Col A B C ->
 ~ Col A B C /\ ~ Col A C B /\ ~ Col B A C /\
 ~ Col B C A /\ ~ Col C A B /\ ~ Col C B A.
Proof.
    intros.
    repeat split.
    assumption.
    apply not_col_132. assumption.
    apply not_col_213. assumption.
    apply not_col_231. assumption.
    apply not_col_312. assumption.
    apply not_col_321. assumption.
Qed.

Lemma not_bet_not_col : forall A B C,
  ~ Bet A B C -> ~ Bet B C A -> ~ Bet C A B -> ~ Col A B C.
Proof.
    intros.
    intro.
    induction H2.
      apply H; assumption.
    induction H2.
      apply H0. apply between_symmetry. assumption.
      apply H1. apply between_symmetry. assumption.
Qed.

Lemma not_col_not_bet : forall A B C,
  ~ Col A B C -> ~ Bet A B C /\ ~ Bet B C A /\ ~ Bet C A B.
Proof.
    intros.
    repeat split.
    intro.
    apply H.
    apply bet_col_123; assumption.
    intro.
    apply H.
    apply bet_col_231; assumption.
    intro.
    apply H.
    apply bet_col_312; assumption.
Qed.

Lemma not_col_trans : forall A B C Q,
  A <> Q -> ~ Col A B C -> Col A B Q -> ~ Col A C Q.
Proof.
    intros.
    intro.
    apply H0.
    apply col_transitivity_1 with Q.
    assumption.
    apply col_132. assumption.
    apply col_132. assumption.
Qed.

Lemma not_col_trans_2 : forall A B C Q,
  B <> Q -> ~ Col A B C -> Col B C Q -> ~ Col A Q B.
Proof.
    intros.
    intro.
    apply H0.
    apply col_312.
    apply col_transitivity_2 with Q.
    apply not_eq_sym. assumption.
    apply col_312. assumption.
    apply col_231. assumption.
Qed.

End T4_4.

Print All.

