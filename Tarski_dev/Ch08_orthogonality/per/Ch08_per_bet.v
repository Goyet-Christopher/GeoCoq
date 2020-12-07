Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_cong.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_col.

Section Per_bet.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma per_cong_bet : forall A B C A',
 A <> B -> Per A B C -> Bet B A A' -> Cong C A C A' -> A = A'.
Proof.
    intros.
    assert(Per A' B C).
      apply per_col_1 with A; try assumption.
        apply bet_col_123. assumption.
    assert(Cong B A B A').
      apply per_per_cong with C; assumption.
    apply between_cong with B; assumption.
Qed.

Lemma per_cong_col_diff_or : forall A B C A',
  A <> B -> A'<>B -> Per A B C -> Cong C A C A' -> Col B A A'
 -> A=A' \/ Bet A B A'.
Proof.
    intros.
    assert(Per A' B C).
      apply per_col_1 with A; assumption.
    induction H3.
      left. apply per_cong_bet with B C; assumption.
    induction H3.
      left. apply eq_sym.
        apply per_cong_bet with B C; try assumption.
        apply cong_3412. assumption.
    right. assumption.
Qed.

Lemma per_cong_col_diff : forall A B C A',
  A <> A' -> A <> B -> A'<>B 
 -> Per A B C -> Cong C A C A' -> Col B A A'
 -> Bet A B A'.
Proof.
    intros.
    assert(A=A' \/ Bet A B A').
      apply per_cong_col_diff_or with C; assumption.
    induction H5.
      contradiction.
      assumption.
Qed.

Lemma per_cong_col_or : forall A B C A',
 Per A B C -> Cong C A C A' -> Col B A A'
 -> A=A' \/ Bet A B A'.
Proof.
    intros.
    induction(eq_dec_points A B).
      subst. right. apply between_trivial_112.
    induction(eq_dec_points A' B).
      subst. right. apply between_trivial_122.
    apply per_cong_col_diff_or with C; assumption.
Qed.

Lemma per_cong_col : forall A B C A',
 A<>A' -> Per A B C -> Cong C A C A' -> Col B A A'
 -> Bet A B A'.
Proof.
    intros.
    assert(A=A' \/ Bet A B A').
      apply per_cong_col_or with C; assumption.
    induction H3.
      contradiction.
      assumption.
Qed.

End Per_bet.

Print All.
