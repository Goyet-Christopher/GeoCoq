Require Export GeoCoq.Tarski_dev.Ch06_out_lines.Ch06_out_bet.

Section Col_cases.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma col_out2_col  : forall A B C AA CC,
  Col A B C -> Out B A AA -> Out B C CC -> Col AA B CC.
Proof.
    intros.
    induction H.
      assert (Bet AA B CC).
        apply bet_out_out_bet with A C;
          assumption.
      apply bet_col_123.
        assumption.
    induction H.
      assert(Out B AA CC).
        apply out_transitivity_2 with A.
        apply out_symmetry.
          assumption.
        apply out_symmetry.
        apply out_transitivity_1 with C.
          assumption.
          apply bet_out.
          apply H1.
          apply between_symmetry; assumption.
      apply col_213.
        apply out_col.
        assumption.
    assert(Out B AA CC).
      apply out_transitivity_2 with A.
        apply out_symmetry; assumption.
        apply out_symmetry.
          apply out_transitivity_2 with C.
            apply out_symmetry. assumption.
            apply out_symmetry.
              apply bet_out.
                apply H0.
                assumption.
    apply col_213.
      apply out_col.
      assumption.
Qed.

(*
Lemma or_bet_out : forall A B C,
  Bet A B C \/ Out B A C \/ ~Col A B C.
Proof.
    intros.
    destruct (Col_dec A B C); auto.
    destruct (out_dec B A C); auto.
    left; apply not_out_bet; trivial.
Qed.

Lemma not_bet_out : forall A B C,
 Col A B C -> ~Bet A B C -> Out B A C.
Proof.
    intros.
    destruct (or_bet_out A B C) as [HBet|[HOut|HNCol]]; trivial; contradiction.
Qed.



Lemma out_to_bet :
 forall A B C A' B' C',
  Col A' B' C' -> (Out B A C <-> Out B' A' C')
  -> Bet A B C ->
  Bet A' B' C'.
Proof.
    intros.
    induction(out_dec B A C).
      unfold Out in H2.
      spliter.
      induction H4.
        assert( A = B).
          eapply between_equality.
            apply H1.
          assumption.
        contradiction.
      assert(C = B).
        apply(between_symmetry) in H4.
        eapply between_equality.
          apply between_symmetry.
          apply H1.
        apply between_symmetry.
        assumption.
      contradiction.
    destruct H0.
    assert (~Out B' A' C').
      intro.
      apply H2.
      apply H3.
      assumption.
    apply not_out_bet.
      assumption.
    assumption.
Qed.
*)

End Col_cases.

Print All.

