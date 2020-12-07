Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_final.

Section Per_def.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma mid_cong_per_3: forall A B C C',
  Midpoint B C C' -> Cong A C A C' -> Per A B C.
Proof.
    intros.
    exists C'.
    split; assumption.
Qed.

Lemma per_to_def: forall A B C,
  Per A B C -> exists C', Midpoint B C C' /\ Cong A C A C'.
Proof.
    intros.
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

Lemma mid_cong_per_1: forall A B C A',
  Midpoint B A A' -> Cong C A C A' -> Per A B C.
Proof.
    intros.
    apply per_symmetry.
    apply mid_cong_per_3 with A'; assumption.
Qed.

Lemma per_supplementary_3 : forall A B C C',
 Per A B C -> Midpoint B C C' -> Per A B C'.
Proof.
    intros.
    apply per_to_def in H.
    exists_and H C''.
    apply mid_cong_per_3 with C.
      apply midpoint_symmetry. assumption.
    assert (C' = C'').
      apply symmetric_point_uniqueness with B C; assumption.
    subst C''.
      apply cong_3412. assumption.
Qed.

Lemma per_supplementary_1 : forall A B C A',
 Per A B C -> Midpoint B A A' -> Per A' B C.
Proof.
    intros.
    apply per_symmetry.
    apply per_supplementary_3 with A.
      apply per_symmetry. assumption.
      assumption.
Qed.

Lemma per_opposite : forall A B C A' C',
 Per A B C -> Midpoint B A A' -> Midpoint B C C' -> Per A' B C'.
Proof.
    intros.
    apply per_supplementary_1 with A.
      apply per_supplementary_3 with C; assumption.
      assumption.
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
