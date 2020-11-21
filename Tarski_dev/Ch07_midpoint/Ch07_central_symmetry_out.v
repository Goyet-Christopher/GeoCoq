Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_eq.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma symmetry_preserves_out : forall A B C A' B' C' M,
  Out A B C -> Midpoint M A A' -> Midpoint M B B'
 -> Midpoint M C C' -> Out A' B' C'.
Proof.
    intros.
    apply out_to_def in H.
    spliter.
    apply midpoint_symmetry in H0.
    apply midpoint_symmetry in H1.
    apply midpoint_symmetry in H2.
    repeat split.
      intro.
      subst B'.
      assert (A = B).
        apply symmetric_point_uniqueness with A' M; assumption.
      subst B.
      contradiction.
      intro.
      subst C'.
      assert (A = C).
        apply symmetric_point_uniqueness with A' M; assumption.
      subst.  contradiction.
    apply midpoint_symmetry in H0.
    apply midpoint_symmetry in H1.
    apply midpoint_symmetry in H2.
    induction H4.
      left. apply (symmetry_preserves_bet A B C A' B' C' M) ; assumption.
      right. apply (symmetry_preserves_bet A C B A' C' B' M); assumption.
Qed.

End T7_1.

Print All.
