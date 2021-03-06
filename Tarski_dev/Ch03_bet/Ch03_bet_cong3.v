Require Export GeoCoq.Tarski_dev.Ch03_bet.bet4.Ch03_bet4.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_IFSC.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_l2_11.


Section T3.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

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
    exact l2_11_cong3.
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

Lemma bet_cong1213_cong3_reverse : forall  A B C A' B' C',
  Bet A B C -> Bet A' B' C'
  -> Cong A B B' C' -> Cong A C A' C'
  -> Cong_3 A B C C' B' A'.
Proof.
    intros.
    apply def_to_cong3_reverse.
    assumption.
    assumption.
    apply cong_1243.
    apply l4_3_1 with A C'.
      assumption.
      apply between_symmetry. assumption.
      apply cong_1243. assumption.
      apply cong_1243. assumption.
Qed.

Lemma bet_cong1223_cong3_reverse : forall  A B C A' B' C',
  Bet A B C -> Bet A' B' C'
  -> Cong A B B' C' -> Cong B C A' B'
  -> Cong_3 A B C C' B' A'.
Proof.
    exact l2_11_cong3_reverse.
Qed.

Lemma bet_cong1323_cong3_reverse : forall  A B C A' B' C',
  Bet A B C -> Bet A' B' C'
  -> Cong A C A' C' -> Cong B C A' B'
  -> Cong_3 A B C C' B' A'.
Proof.
    intros.
    repeat split.
    apply l4_3 with C A'.
      assumption.
      apply between_symmetry. assumption.
      apply cong_1243. assumption.
      apply cong_1243. assumption.
    apply cong_1243. assumption.
    apply cong_1243. assumption.
Qed.

Lemma cong3_degenerate_a : forall A B C A',
 Bet A B C -> Bet A' B C -> Cong A C A' C -> Cong_3 A B C A' B C.
Proof.
    intros.
    apply bet_cong1323_cong3; try assumption.
      apply cong_1212.
Qed.

Lemma cong3_degenerate_a2 : forall A B C A',
 Bet A B C -> Bet A' B C -> Cong A B A' B -> Cong_3 A B C A' B C.
Proof.
    intros.
    assert(Cong A C A' C).
      apply l2_11 with B B; try assumption.
      apply cong_1212.
    apply cong3_degenerate_a; assumption.
Qed.

Lemma cong3_degenerate_b : forall A B C B',
 Bet A B C -> Bet A B' C -> Cong A B A B' -> Cong_3 A B C A B' C.
Proof.
    intros.
    apply bet_cong1213_cong3; try assumption.
      apply cong_1212.
Qed.

Lemma cong3_degenerate_b2 : forall A B C B',
 Bet A B C -> Bet A B' C -> Cong B C B' C -> Cong_3 A B C A B' C.
Proof.
    intros.
    assert(Cong A B A B').
      apply l4_3 with C C; try assumption.
      apply cong_1212.
    apply cong3_degenerate_b; assumption.
Qed.

Lemma cong3_degenerate_c : forall A B C C',
 Bet A B C -> Bet A B C' -> Cong A C A C' -> Cong_3 A B C A B C'.
Proof.
    intros.
    apply bet_cong1213_cong3; try assumption.
      apply cong_1212.
Qed.

Lemma cong3_degenerate_c2 : forall A B C C',
 Bet A B C -> Bet A B C' -> Cong B C B C' -> Cong_3 A B C A B C'.
Proof.
    intros.
    assert(Cong A C A C').
      apply l2_11 with B B; try assumption.
      apply cong_1212.
    apply cong3_degenerate_c; assumption.
Qed.

Lemma l4_6 : forall A B C A' B' C', 
  Bet A B C -> Cong_3 A B C A' B' C' -> Bet A' B' C'.
Proof.
    intros.
    assert (exists B'', Bet A' B'' C' /\ Cong_3 A B C A' B'' C').
      apply cong3_1346 in H0.
      apply l4_5_b; assumption.
      exists_and H1 x.
    assert ( x = B').
      apply IFSC_eq with A' C'.
        apply IFSC_same_base_cong3.
          assumption.
          apply cong3_swap_132.
            apply cong3_transitivity_X1_X2 with A B C;
            assumption.
    subst.
    assumption.
Qed.

Definition l4_6_bet_123 A B C A' B' C' :=
    l4_6 A B C A' B' C'.

End T3.

Section T3_cases.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l4_6_bet_cases : forall A B C A' B' C',
  Bet A B C \/ Bet A' B' C' -> Cong_3 A B C A' B' C' -> Bet A B C /\ Bet A' B' C'.
Proof.
    intros.
    induction H.
      split.
        assumption. apply l4_6 with A B C; assumption.
      split.
        apply l4_6 with A' B' C'. assumption.
          apply cong3_symmetry. assumption.
        assumption.
Qed.

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
    apply cong3_cases.
    assumption.
Qed.

Lemma l4_6_bet_132 : forall A B C A' B' C', 
  Bet A C B -> Cong_3 A B C A' B' C' -> Bet A' C' B'.
Proof.
    intros.
    apply l4_6 with A C B.
    assumption.
    apply cong3_perm in H0.
    apply H0.
Qed.

Lemma l4_6_bet_213 : forall A B C A' B' C', 
  Bet B A C -> Cong_3 A B C A' B' C' -> Bet B' A' C'.
Proof.
    intros.
    apply l4_6 with B A C.
    assumption.
    apply cong3_perm in H0.
    apply H0.
Qed.

Lemma l4_6_bet_231 : forall A B C A' B' C', 
  Bet B C A -> Cong_3 A B C A' B' C' -> Bet B' C' A'.
Proof.
    intros.
    apply l4_6 with B C A.
    assumption.
    apply cong3_perm in H0.
    apply H0.
Qed.

Lemma l4_6_bet_312 : forall A B C A' B' C', 
  Bet C A B -> Cong_3 A B C A' B' C' -> Bet C' A' B'.
Proof.
    intros.
    apply l4_6 with C A B.
    assumption.
    apply cong3_perm in H0.
    apply H0.
Qed.

Lemma l4_6_bet_321 : forall A B C A' B' C', 
  Bet C B A -> Cong_3 A B C A' B' C' -> Bet C' B' A'.
Proof.
    intros.
    apply l4_6 with C B A.
    assumption.
    apply cong3_perm in H0.
    apply H0.
Qed.


Lemma OFSC_central_sym_with_cong3 : forall A B C A' B' C',
  Bet A B C ->
  Cong_3 A B C C' B' A' ->
  Cong B C' B' A ->
  OFSC A B C B' C' B' A' B.
Proof.
    intros.
    apply def_to_OFSC_with_cong3.
    assumption.
    apply l4_6_cong3_cases with A B C.
      assumption.
      left. assumption.
    apply def_to_cong3.
      apply H0.
      apply cong_4321; assumption.
      apply cong_1221.
    apply H0.
Qed.

Lemma OFSC_isosceles_cong3 : forall A B C B' C',
    Bet B A B' \/ Bet C A C' -> Cong_3 B A B' C A C'
 -> Cong_3 A B C' A C B'.
Proof.
    intros.
    assert(Bet B A B' /\ Bet C A C').
      apply l4_6_bet_cases; assumption.
    spliter.
    assert(Cong A B A C).
      apply cong3_2154 with B' C'. assumption.
    assert(Cong A B' A C').
      apply cong3_2356 with B C. assumption.
    assert(Cong A C' A B').
      apply cong_3412. assumption.
    apply def_to_cong3; try assumption.
      apply OFSC_isosceles with A; assumption.
Qed.


End T3_cases.



Print All.
