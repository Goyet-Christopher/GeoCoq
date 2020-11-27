Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_col.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_exists.

Section Per_eq.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma per_equality_1 : forall A B C A',
 Per A B C -> Per A' B C -> Bet A C A' -> B=C.
Proof.
    intros.
    exists_and H C'.
    exists_and H0 C''.
    assert (C'=C'').
      apply symmetric_point_uniqueness with B C; assumption.
    subst C''.
    assert (C = C').
      apply l4_19 with A A'; assumption.
    subst C'.
    apply midpoint_identity_122.
      assumption.
Qed.


Lemma per_equality_2 : forall A B C,
 Per A B C -> Per A C B -> B=C.
Proof.
    intros.
    assert(exists C', Midpoint B C C' /\ Cong A C A C').
      apply per_to_def. assumption.
      exists_and H1 C'.
    induction (eq_dec_points B C).
      assumption.
    assert (Per A C C').
      apply per_col_3 with B.
        apply diff_symmetry. assumption.
        assumption.
        apply midpoint_col_213. assumption.
    apply per_exists_1 in H4.
    exists_and H4 A'.
    assert(QEqui C' A C A').
      apply qequi_3adj.
        assumption.
        apply cong_4312. assumption.
        apply midpoint_cong_2113. assumption.
    assert (Per A' B C).
      exists C'.
      split. assumption.
        apply cong_4321.
        apply qequi_cong_1434 with A. assumption.
    apply per_equality_1 with A A'; try assumption.
      apply midpoint_bet1. assumption.
Qed.

Lemma per_equality_3 : forall A B C B',
 B <> C -> B' <> C -> Col B C B' -> Per A B C
 -> Per A B' C -> B=B'.
Proof.
    intros.
    assert(Per A B B').
      apply per_col_3 with C; assumption.
    assert(Per A B' B).
      apply per_col_3 with C; try assumption.
        apply col_321. assumption.
    apply per_equality_2 with A; assumption.
Qed.

Lemma per_equality_3_bis : forall A B C B',
 A <> B -> A <> B' -> Col A B B' -> Per A B C
 -> Per A B' C -> B=B'.
Proof.
    intros.
    assert(Per B' B C).
      apply per_col_1 with A; try assumption.
        apply col_213. assumption.
    assert(Per B B' C).
      apply per_col_1 with A; try assumption.
        apply col_312. assumption.
    apply per_equality_2 with C.
      apply per_symmetry. assumption.
      apply per_symmetry. assumption.
Qed.

Lemma per_equality_4 : forall A B C C' F,
  A<>C -> B<>C' -> Col A C C' -> Col B C C'
 -> Per A C F -> Per B C' F -> C=C'.
Proof.
    intros.
    apply per_equality_2 with F.
      apply per_col_3 with A.
        apply diff_symmetry. assumption.
        apply per_symmetry. assumption.
        apply col_213. assumption.
      apply per_col_3 with B.
        apply diff_symmetry. assumption.
        apply per_symmetry. assumption.
        apply col_312. assumption.
Qed.

Lemma per_identity : forall A B,
  Per A B A -> A=B.
Proof.
    intros.
    apply per_equality_2 with A.
      apply per_trivial_112.
    assumption.
Qed.

Lemma per_identity_2 : forall A B C,
  Per A B C -> Col A B C -> A=B \/ B=C.
Proof.
    intros.
    induction (eq_dec_points A B).
      left. assumption.
    right.
    apply per_equality_2 with C.
      apply per_col_1 with A; try assumption.
        apply col_213. assumption.
        apply per_trivial_112.
Qed.

End Per_eq.

Print All.

