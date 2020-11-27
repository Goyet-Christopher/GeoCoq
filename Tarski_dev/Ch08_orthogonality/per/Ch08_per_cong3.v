Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per.

Section Per_cong3.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cong3_preserves_per : forall A B C A' B' C',
  Per A B C -> Cong_3 A B C A' B' C' -> Per A' B' C'.
Proof.
    intros.
    exists_and H D.
    symmetric D' B' C'.
    exists D'.
    split.
      assumption.
    induction (eq_dec_points C B).
    (* C = B *)
      subst. assert(B' = C'). 
        apply cong_reverse_identity with B. apply H0.
      subst. assert(C' = D').
        apply midpoint_identity_112. assumption.
      subst. apply cong_1212.
    (* C <> B *)
    assert(OFSC C B D A C' B' D' A').
      apply mid2_cong3_OFSC; assumption.
    assert (Cong D A D' A').
      apply OFSC_cong_34 with C B C' B'.
        assumption.
        left. assumption.
    apply cong_XY12_XY34 with A C.
      apply cong3_1346 with B B'. assumption.
    apply cong_12XY_YX43 with A D; assumption.
Qed.

Lemma symmetry_preserves_per : forall Z A B C A' B' C',
  Per A B C -> Midpoint Z A A' -> Midpoint Z B B'
 -> Midpoint Z C C' -> Per A' B' C'.
Proof.
    intros.
    assert(Cong_3 A B C A' B' C').
      apply symmetry_preserves_length_cong3 with Z; assumption.
    apply cong3_preserves_per with A B C; assumption.
Qed.

End Per_cong3.

Print All.


