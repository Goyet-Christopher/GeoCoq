Require Export GeoCoq.Tarski_dev.Ch06_out_lines.Ch06_out.

Section Out_eq.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma l6_11_uniqueness : forall A B C R X Y,
  R<>A -> B<>C ->
  Out A X R -> Cong A X B C ->
  Out A Y R -> Cong A Y B C ->
  X=Y.
Proof.
    unfold Out.
    intros.
    spliter.
    assert (Cong A X A Y).
      apply cong_1234_5634 with B C; assumption.
    induction H8; induction H6.
      apply l4_19 with A R; try assumption.
        apply cong_2143.
        apply l4_3_1 with A A; try assumption.
        apply cong_1212.
      assert (Bet A X Y).
        apply between_exchange_3 with R; assumption.
      apply between_cong with A; assumption.
      assert (Bet A Y X).
        apply between_exchange_3 with R; assumption.
      apply sym_equal. apply between_cong with A.
        assumption. apply cong_3412. assumption.
      assert (Bet A X Y \/ Bet A Y X).
        apply l5_1 with R; assumption.
    induction H10.
      apply between_cong with A; assumption.
      apply sym_equal.
        apply between_cong with A.
          assumption.
          apply cong_3412; assumption.
Qed.


End Out_eq.

Print All.



