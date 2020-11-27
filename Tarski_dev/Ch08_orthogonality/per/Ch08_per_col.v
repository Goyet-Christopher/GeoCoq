Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per.

Section Per_col.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma per_col_1 : forall A B C A',
 Per A B C -> A<>B -> Col B A A' -> Per A' B C.
Proof.
    intros.
    exists_and H C'.
    exists C'.
    split.
      assumption.
      apply l4_17 with A B.
        assumption.
        apply col_213. assumption.
        assumption.
        apply midpoint_cong_1213. assumption.
Qed.

Lemma per_col_3 : forall A B C C',
 B <> C -> Per A B C -> Col B C C' -> Per A B C'.
Proof.
    intros.
    apply per_symmetry.
    apply per_col_1 with C.
      apply per_symmetry. assumption.
      apply diff_symmetry. assumption.
      assumption.
Qed.

Lemma col_col_per_per : forall A B C A' C',
 A<>B -> B<>C -> Col A' A B -> Col C' C B
 -> Per A B C -> Per A' B C'.
Proof.
    intros.
    assert (Per A' B C).
      apply (per_col_1 A B C A'); try assumption.
        apply col_321. assumption.
    apply per_col_3 with C; try assumption.
      apply col_321. assumption.
Qed.

End Per_col.

Print All.

