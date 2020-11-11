
Lemma l6_2_sym : forall A B C P,
  P<>A -> P<>B -> P<>C -> Bet C P A
-> (Bet C P B <-> Out P A B).
Proof.
    intros.
    split.
      intros.
      repeat split; try assumption.
      apply l5_2 with C.
        apply diff_symmetry; assumption.
        assumption. assumption.
    intro.
      apply out_to_def in H3.
      spliter.
      induction H5.
      apply between_outer_transitivity_3 with A; assumption.
      apply between_exchange_4 with A; assumption.
Qed.

Lemma l6_2 : forall A B C P,
  P<>A -> P<>B -> P<>C -> Bet A P C 
-> (Bet B P C <-> Out P A B).
Proof.
    intros.
    apply between_symmetry in H2.
    split.
      intros.
      apply between_symmetry in H3.
      apply l6_2_sym with C; try assumption.
    intro.
      apply between_symmetry.
      eapply l6_2_sym with A; try assumption.
Qed.