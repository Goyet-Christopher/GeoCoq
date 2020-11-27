Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_col.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_exists.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_cong3.

Section Per_midpoint.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l8_4 : forall A B C C',
 Per A B C -> Midpoint B C C' -> Per A B C'.
Proof.
    intros.
    exists_and H C''.
    exists C.
    split.
      apply midpoint_symmetry. assumption.
    assert (C' = C'').
      apply symmetric_point_uniqueness with B C; assumption.
    subst C''.
      apply cong_3412. assumption.
Qed.

Lemma per_cong_mid : forall A B C H,
 B <> C -> Bet A B C -> Cong A H C H -> Per H B C ->
 Midpoint B A C.
Proof.
    intros.
    induction (eq_dec_points H B).
      subst H.
      split.
        assumption.
        apply cong_1243. assumption.
    assert (Per H B A).
      apply per_col_3 with C; try assumption.
        apply bet_col_312. assumption.
    apply per_exists_1 in H3.
    exists_and H3 H'.
    apply per_exists_1 in H5.
    exists_and H5 H''.
    assert (H' = H'').
      apply construction_uniqueness with H B H B.
        assumption.
        apply midpoint_bet1. assumption.
        apply midpoint_cong_1321. assumption.
        apply midpoint_bet1. assumption.
        apply midpoint_cong_1321. assumption.
    subst H''.
    assert(IFSC H B H' A H B H' C).
      apply IFSC_same_base.
        apply midpoint_bet1. assumption.
        apply cong_2143. assumption.
        apply cong_XY21_XY34 with A H.
          assumption.
          apply cong_12XY_XY43 with C H; assumption.
    assert(Cong B A B C).
      apply IFSC_cong_24 with H H' H H'. assumption.
    split.
      assumption.
      apply cong_2134. assumption.
Qed.

Lemma l8_20_1 : forall A B C C' D P,
  Per A B C -> Midpoint A C C' -> Midpoint B C D
  -> Midpoint P C' D -> Per B A P.
Proof.
    intros.
    symmetric B' A B.
    symmetric D' A D.
    symmetric P' A P.
    induction (eq_dec_points A B).
      subst B. apply per_trivial_112.
    assert (Per B' B C).
      apply per_col_1 with A.
        assumption. assumption.
        apply midpoint_col_213. assumption.
    assert (Per B B' C').
      apply symmetry_preserves_per with A B' B C; try assumption.
      apply midpoint_symmetry. assumption.
    (* Mq D'P'CB est le symétrique de C'PDB par rapport à BAB' *)
    assert(Midpoint B' C' D').
      apply symmetry_preserves_midpoint with C B D A; assumption.
    assert(Cong B C' B D').
      apply per_def_cong with B'; assumption.
    assert (Cong C' D C D').
      apply symmetry_preserves_length with A.
        apply midpoint_symmetry. assumption.
        assumption.
    assert(Midpoint P' C D').
      apply symmetry_preserves_midpoint with C' P D A; try assumption.
        apply midpoint_symmetry. assumption.
    assert (Cong P D P' C).
      apply cong_12XY_YX34 with P' D'.
        apply symmetry_preserves_length with A; assumption.
        apply midpoint_cong_3112. assumption.
    assert (IFSC C' P D B D' P' C B).
      apply def_to_IFSC.
        apply midpoint_bet1. assumption.
        apply midpoint_bet2. assumption.
        apply cong_1243. assumption.
        assumption.
        apply cong_2143. assumption.
        apply midpoint_cong_3121. assumption.
    assert (Cong P B P' B).
      apply IFSC_cong_24 with C' D D' C. assumption.
    apply exists_per_3.
    exists P'.
    split.
      assumption.
      apply cong_2143. assumption.
Qed.


End Per_midpoint.

Print All.


