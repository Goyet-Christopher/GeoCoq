Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col_not.
Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col_transitivity.

Section dec.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma Col_dec : forall A B C, 
  Col A B C \/ ~ Col A B C.
Proof.
    intros.
    induction (bet_dec A B C).
    (* Bet A B C *)
      left.
      apply bet_col_123; assumption.
    (* ~ Bet A B C *)
      induction(bet_dec B C A). 
      (* Bet B C A *)
        left.
        apply bet_col_231; assumption.
      (* ~ Bet B C A *)
        induction(bet_dec C A B).
        (* Bet C A B *)
          left.
          apply bet_col_312; assumption.
        (* ~ Bet A B C /\ ~ Bet B C A /\ ~ Bet C A B *)
          right.
          apply not_bet_not_col; assumption.
Qed.

(* This is l6_25 of Tarski *)
Lemma not_col_exists : forall A B,
 A<>B -> exists C, ~ Col A B C.
Proof.
    intros.
    assert (T:=lower_dim).
    induction T.
    induction H0.
    induction H0.
    assert (~(Col x x0 x1)).
      intro. apply H0.
        apply col_to_def in H1.
          induction H1. left. assumption.
          right. apply betsym_left_right. assumption.
    induction (Col_dec A B x).
      induction(Col_dec A B x0).
        induction(Col_dec A B x1).
          induction (eq_dec_points A x).
            subst x. exists x0.
              assert(Col A x0 x1).
                apply col_transitivity_1 with B; assumption.
              contradiction.
            assert (Col A x x0).
              apply col_transitivity_1 with B; assumption.
            assert (Col A x x1).
              apply col_transitivity_1 with B; assumption.
            assert (Col A x0 x1).
              apply col_transitivity_1 with B; assumption.
            assert (Col x x0 x1).
              apply col_transitivity_1 with A.
                apply diff_symmetry. assumption.
                apply col_213. assumption.
                apply col_213. assumption.
            contradiction.
        exists x1. assumption.
      exists x0. assumption.
    exists x. assumption.
Qed.

End dec.

Print All.
