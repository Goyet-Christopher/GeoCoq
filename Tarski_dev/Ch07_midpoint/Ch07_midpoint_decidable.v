Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_not.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma midpoint_dec :
 forall I A B, Midpoint I A B \/ ~ Midpoint I A B.
Proof.
    intros.
    induction(bet_dec A I B).
      induction(cong_dec A I I B).
        left. apply def_to_midpoint; assumption.
        right. apply not_midpoint_cases. right. assumption.
        right. apply not_midpoint_cases. left. assumption.
Qed.

End T7_1.

Print All.