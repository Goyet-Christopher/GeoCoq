Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_eq.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_IFSC.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_exists.

Section T3.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cong3_bet_eq : forall  A B C X,
  Bet A B C -> Cong_3 A B C A X C -> B = X.
Proof.
    intros.
    assert (IFSC A B C B A B C X).
      apply cong3_swap_132 in H0.
      apply IFSC_axial_sym; assumption.
    apply IFSC_eq with A C.
    assumption.
Qed.

Lemma bet_cong1213_cong3 : forall  A B C A' B' C',
  Bet A B C -> Bet A' B' C'
  -> Cong A B A' B' -> Cong A C A' C'
  -> Cong_3 A B C A' B' C'.
Proof.
    intros.
    repeat split.
    assumption.
    assumption.
    apply l4_3_1 with A A'; assumption.
Qed.

Lemma bet_cong1223_cong3 : forall  A B C A' B' C',
  Bet A B C -> Bet A' B' C'
  -> Cong A B A' B' -> Cong B C B' C'
  -> Cong_3 A B C A' B' C'.
Proof.
    intros.
    repeat split.
    assumption.
    apply l2_11 with B B'; assumption.
    assumption.
Qed.

Lemma bet_cong1323_cong3 : forall  A B C A' B' C',
  Bet A B C -> Bet A' B' C'
  -> Cong A C A' C' -> Cong B C B' C'
  -> Cong_3 A B C A' B' C'.
Proof.
    intros.
    repeat split.
    apply l4_3 with C C'; assumption.
    assumption.
    assumption.
Qed.


Lemma l4_6 : forall A B C A' B' C', 
  Bet A B C -> Cong_3 A B C A' B' C' -> Bet A' B' C'.
Proof.
    intros.
    assert (exists B'', Bet A' B'' C' /\ Cong_3 A B C A' B'' C').
      apply cong3_13 in H0.
      apply l4_5_b; assumption.
      exists_and H1 x.
    assert ( x = B').
      apply IFSC_eq with A' C'.
      apply def_to_IFSC_with_cong3.
      assumption. assumption.
      apply cong_1212.
      apply cong3_swap_132.
      apply cong3_transitivity_12_13_23 with A B C;
      assumption.
    subst.
    assumption.
Qed.

Definition l4_6_bet_123 A B C A' B' C' :=
    l4_6 A B C A' B' C'.

End T3.

Section T3_cases.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l4_6_cong3_cases : forall A B C A' B' C', 
  Bet A B C 
  -> Cong_3 A B C A' B' C' \/ Cong_3 A C B A' C' B'
\/ Cong_3 B A C B' A' C' \/ Cong_3 B C A B' C' A'
\/ Cong_3 C A B C' A' B' \/ Cong_3 C B A C' B' A'
  -> Bet A' B' C'.
Proof.
    intros.
    apply l4_6 with A B C.
    assumption.
    apply Cong3_cases.
    assumption.
Qed.

Lemma l4_6_bet_132 : forall A B C A' B' C', 
  Bet A C B -> Cong_3 A B C A' B' C' -> Bet A' C' B'.
Proof.
    intros.
    apply l4_6 with A C B.
    assumption.
    apply Cong3_perm in H0.
    apply H0.
Qed.

Lemma l4_6_bet_213 : forall A B C A' B' C', 
  Bet B A C -> Cong_3 A B C A' B' C' -> Bet B' A' C'.
Proof.
    intros.
    apply l4_6 with B A C.
    assumption.
    apply Cong3_perm in H0.
    apply H0.
Qed.

Lemma l4_6_bet_231 : forall A B C A' B' C', 
  Bet B C A -> Cong_3 A B C A' B' C' -> Bet B' C' A'.
Proof.
    intros.
    apply l4_6 with B C A.
    assumption.
    apply Cong3_perm in H0.
    apply H0.
Qed.

Lemma l4_6_bet_312 : forall A B C A' B' C', 
  Bet C A B -> Cong_3 A B C A' B' C' -> Bet C' A' B'.
Proof.
    intros.
    apply l4_6 with C A B.
    assumption.
    apply Cong3_perm in H0.
    apply H0.
Qed.

Lemma l4_6_bet_321 : forall A B C A' B' C', 
  Bet C B A -> Cong_3 A B C A' B' C' -> Bet C' B' A'.
Proof.
    intros.
    apply l4_6 with C B A.
    assumption.
    apply Cong3_perm in H0.
    apply H0.
Qed.

End T3_cases.

Print All.