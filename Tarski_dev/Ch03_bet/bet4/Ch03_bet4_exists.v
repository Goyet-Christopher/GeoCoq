Require Export GeoCoq.Tarski_dev.Ch03_bet.bet4.Ch03_bet4.

Section Bet4_prolong.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma segment_construction4 : forall A B C D E,
  Bet A B C -> exists X, Bet_4 A B C X /\ Cong D E C X.
Proof.
    intros.
    prolong A C X D E.
    exists X.
    split.
    apply def_to_bet4.
    assumption.
    apply between_exchange_1 with A; assumption.
    assumption.
    apply between_exchange_3 with C; assumption.
    assumption.
Qed.

End Bet4_prolong.

Ltac prolong4 A B C x D E :=
  assert(sg := segment_construction4 A B C D E);
  destruct sg as (x, sg);[unfold Bet_5 in *;
                          unfold Bet_4 in *;
                          spliter; bet_assumption |idtac];
  induction sg.



Print All.