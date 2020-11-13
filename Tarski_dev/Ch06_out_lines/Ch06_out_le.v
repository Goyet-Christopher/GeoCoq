Require Export GeoCoq.Tarski_dev.Ch06_out_lines.Ch06_out_eq.

Section Out_Le.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma l6_13_1 : forall P A B,
  Out P A B -> Le P A P B -> Bet P A B.
Proof.
    intros.
    apply out_to_def in H.
    spliter.
    induction H2.
      assumption.
    apply le_to_def in H0.
    exists_and H0 Y.
    assert(Bet P Y A).
      apply between_exchange_3 with B; assumption.
    assert(Y = A).
      apply between_cong with P.
        assumption.
        apply cong_3412; assumption.
    subst Y; assumption.
Qed.

Lemma l6_13_2 : forall P A B,
  Out P A B -> Bet P A B -> Le P A P B.
Proof.
    intros.
    unfold Le.
    exists A.
    split.
      assumption.
      apply cong_1212.
Qed.

End Out_Le.

Print All.

