Require Export GeoCoq.Tarski_dev.Ch06_out_lines.Ch06_out.

Section Out_cong.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cong_preserves_bet : forall A B C A' B' C',
  Bet A B C -> Cong A B A' B' -> Cong A C A' C'
  -> Out A' B' C' -> Bet A' B' C'.
Proof.
    intros.
    apply out_to_def in H2.
    spliter.
    induction H4.
      assumption.
    assert(B' = C').
      apply (bet_cong_eq2 A B C A' B' C');
        assumption.
    subst C'.
    apply between_trivial_122.
Qed.

Lemma out_cong_cong : forall A B C A' B' C',
 Out A B C -> Out A' B' C' ->
 Cong A B A' B' -> Cong A C A' C' ->
 Cong B C B' C'.
Proof.
    intros.
    apply out_to_def in H.
    spliter.
    induction H4.
      assert (Bet A' B' C').
        apply cong_preserves_bet with A B C; assumption.
      apply l4_3_1 with A A'; assumption.
    assert (Bet A' C' B').
      apply out_symmetry in H0.
      apply cong_preserves_bet with A C B; assumption.
    apply cong_2143.
    apply l4_3_1 with A A'; assumption.
Qed.

End Out_cong.

Print All.

