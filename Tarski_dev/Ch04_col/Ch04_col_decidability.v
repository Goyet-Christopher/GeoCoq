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


End dec.

Print All.