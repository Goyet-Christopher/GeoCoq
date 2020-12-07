Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per.

Section Per_exists.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma exists_per_3: forall A B C,
  (exists C', Midpoint B C C' /\ Cong A C A C') -> Per A B C.
Proof.
    intros.
    assumption.
Qed.

Lemma per_exists_3: forall A B C,
  Per A B C -> exists C', Midpoint B C C' /\ Cong A C A C'.
Proof.
    exact per_to_def.
Qed.

Lemma exists_per_1: forall A B C,
  (exists A', Midpoint B A A' /\ Cong C A C A') -> Per A B C.
Proof.
    intros.
    exists_and H A'.
    apply mid_cong_per_1 with A'; assumption.
Qed.

Lemma per_exists_1: forall A B C,
  Per A B C -> exists A', Midpoint B A A' /\ Cong C A C A'.
Proof.
    intros.
    apply per_symmetry in H.
    apply per_exists_3 in H.
    exists_and H A'.
    exists A'.
    split; assumption.
Qed.

End Per_exists.

Print All.
