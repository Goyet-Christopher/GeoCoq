Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_final.

Section Per_def.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma def_to_per: forall A B C,
  (exists C', Midpoint B C C' /\ Cong A C A C') -> Per A B C.
Proof.
    intros.
    assumption.
Qed.

Lemma per_to_def: forall A B C,
  Per A B C -> exists C', Midpoint B C C' /\ Cong A C A C'.
Proof.
    intros.
    assumption.
Qed.

Lemma per_def_cong : forall A B C C',
  Per A B C -> Midpoint B C C' -> Cong A C A C'.
Proof.
    intros.
    exists_and H C''.
    assert (C' = C'').
      apply symmetric_point_uniqueness with B C; assumption.
    subst C''.
    assumption.
Qed.

End Per_def.


Section Per_properties.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma per_symmetry : forall A B C, Per A B C -> Per C B A.
Proof.
    intros.
    exists_and H C'.
    assert (exists A', Midpoint B A A').
      apply symmetric_point_construction.
    exists_and H1 A'.
    exists A'.
    assert(QEqui A C A' C').
      apply mid2_qequi with B; assumption.
    apply qequi_to_all in H1. spliter.
    split.
      assumption.
      apply cong_2134. assumption.
Qed.

Lemma per_cases : forall A B C,
 Per A B C \/ Per C B A -> Per A B C.
Proof.
    intros.
    induction H.
      assumption.
      apply per_symmetry. assumption.
Qed.

Lemma per_perm : forall A B C,
 Per A B C -> Per A B C /\ Per C B A.
Proof.
    intros.
    split.
      assumption.
      apply per_symmetry. assumption.
Qed.

Lemma per_trivial_122 : forall A B,
 Per A B B.
Proof.
    intros.
    exists B.
    split.
      apply midpoint_trivial.
      apply cong_1212.
Qed.

Lemma per_trivial_112 : forall A B,
 Per A A B.
Proof.
    intros.
    apply per_symmetry.
    apply per_trivial_122.
Qed.

End Per_properties.

Print All.
