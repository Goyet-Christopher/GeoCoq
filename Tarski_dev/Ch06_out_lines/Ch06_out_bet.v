Require Export GeoCoq.Tarski_dev.Ch06_out_lines.Ch06_not_bet.

Section Out_bet.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma l6_2_sym : forall A B C P,
  P<>A -> P<>B -> P<>C 
-> Bet C P A -> Out P A B -> Bet C P B.
Proof.
    intros.
      apply out_to_def in H3.
      spliter.
      induction H5.
      apply between_outer_transitivity_3 with A; assumption.
      apply between_exchange_4 with A; assumption.
Qed.

Lemma l6_2 : forall A B C P,
  P<>A -> P<>B -> P<>C 
-> Bet A P C -> Out P A B -> Bet B P C.
Proof.
    intros.
    apply between_symmetry.
    apply l6_2_sym with A;
      try assumption.
      apply between_symmetry. assumption.
Qed.

Lemma bet_out_bet : forall A B C P,
  Bet A P C -> Out P A B -> Bet B P C.
Proof.
    intros.
    induction (eq_dec_points C P).
      subst. apply between_trivial_122.
    apply l6_2 with A; try assumption.
    apply H0.
    apply H0.
    apply diff_symmetry; assumption.
Qed.

Lemma bet_out_out_bet : forall A B C A' C',
 Bet A B C -> Out B A A' -> Out B C C' -> Bet A' B C'.
Proof.
    intros.
    apply out_to_def in H0.
    apply out_to_def in H1.
    spliter.
    assert(A<>B).
      apply diff_symmetry; assumption.
    assert(A'<>B).
      apply diff_symmetry; assumption.
    apply betsym_left_right in H5.
    induction H5; induction H3.
      assert(Bet A' B C).
        apply between_outer_transitivity_2 with A;
          assumption.
      apply between_outer_transitivity_3 with C; assumption.
      assert(Bet A' B C).
        apply between_outer_transitivity_2 with A; assumption.
      apply between_exchange_4 with C; assumption.
      assert(Bet A' B C).
        apply between_exchange_1 with A; assumption.
      apply between_outer_transitivity_3 with C; assumption.
      assert(Bet A' B C).
        apply between_exchange_1 with A; assumption.
      apply between_exchange_4 with C; assumption.
Qed.

Lemma out2_bet : forall A B C, 
  Out A B C -> Out C A B -> Bet A B C.
Proof.
    intros.
    apply l6_4_1 in H0.
    apply out_to_def in H.
    spliter.
    induction H3.
      assumption.
      assert(False). (* exfalso *)
        apply H1.
        assumption.
        elim H4.
Qed.


End Out_bet.

Print All.

