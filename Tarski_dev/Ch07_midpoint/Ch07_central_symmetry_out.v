Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_eq.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma symmetry_preserves_diff : forall Z A A' B B',
  A <> B -> Midpoint Z A A' -> Midpoint Z B B' -> A' <> B'.
Proof.
    intros.
    intro.
    subst.
    apply H.
    apply symmetric_point_uniqueness_sym with Z B'; assumption.
Qed.

Lemma symmetry_preserves_out : forall A B C A' B' C' M,
  Out A B C -> Midpoint M A A' -> Midpoint M B B'
 -> Midpoint M C C' -> Out A' B' C'.
Proof.
    intros.
    apply out_to_def in H.
    spliter.
    repeat split.
      apply symmetry_preserves_diff with M A B; assumption.
      apply symmetry_preserves_diff with M A C; assumption.
    induction H4.
      left. apply (symmetry_preserves_bet A B C A' B' C' M) ; assumption.
      right. apply (symmetry_preserves_bet A C B A' C' B' M); assumption.
Qed.

End T7_1.

Print All.