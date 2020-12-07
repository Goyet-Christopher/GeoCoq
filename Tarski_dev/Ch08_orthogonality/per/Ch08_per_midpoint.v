Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_col.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_exists.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_preserved.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_cong.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_bet.

Section Per_midpoint.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma per_cong_mid_bet_1 : forall A B C A',
 A <> B -> Bet A B A' -> Cong C A C A' -> Per A B C ->
 Midpoint B A A'.
Proof.
    intros.
    induction (eq_dec_points B C).
      subst C.
      apply def_to_midpoint.
        assumption.
        apply cong_2134. assumption.
    assert (Per A' B C).
      apply per_col_1 with A; try assumption.
        apply bet_col_213. assumption.
    assert(Cong B A B A').
      apply per_per_cong with C; assumption.
    apply def_to_midpoint.
      assumption.
      apply cong_2134. assumption.
Qed.

Lemma per_cong_mid_bet_3 : forall A B C C',
 C<>B -> Bet C B C' -> Cong A C A C' -> Per A B C ->
 Midpoint B C C'.
Proof.
    intros.
    apply per_symmetry in H2.
    apply per_cong_mid_bet_1 with A; assumption.
Qed.

Lemma per_cong_mid_1 : forall A B C A',
 A<>A'-> A<>B -> Col B A A' -> Cong C A C A' -> Per A B C ->
 Midpoint B A A'.
Proof.
    intros.
    assert(Bet A B A').
      apply per_cong_col with C; assumption.
    apply per_cong_mid_bet_1 with C; assumption.
Qed.

Lemma per_cong_mid_3 : forall A B C C',
 C<>C' -> C<>B -> Col B C C' -> Cong A C A C' -> Per A B C ->
 Midpoint B C C'.
Proof.
    intros.
    assert(Bet C B C').
      apply per_cong_col with A; try assumption.
        apply per_symmetry. assumption.
    apply per_cong_mid_bet_3 with A; assumption.
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
      apply per_mid_cong_3 with B'; assumption.
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
    apply mid_cong_per_3 with P'.
      assumption. apply cong_2143. assumption.
Qed.


End Per_midpoint.

Print All.


