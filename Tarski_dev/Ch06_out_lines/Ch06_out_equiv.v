Require Export GeoCoq.Tarski_dev.Ch06_out_lines.Ch06_out_bet.

Section Out_equiv.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.



Lemma l6_2_sym_equiv : forall A B C P,
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
      apply l6_2_sym with A; assumption.
Qed.

Lemma l6_2_equiv : forall A B C P,
  P<>A -> P<>B -> P<>C -> Bet A P C 
-> (Bet B P C <-> Out P A B).
Proof.
    intros.
    split.
      intros.
      apply between_symmetry in H2.
      apply between_symmetry in H3.
      apply l6_2_sym_equiv with C; assumption.
    intro.
      apply l6_2 with A; assumption.
Qed.

End Out_equiv.

Print All.


