Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_eq.
Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_exists.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l7_22_aux : forall A1 A2 B1 B2 C M1 M2,
   Bet A1 C A2 -> Bet B1 C B2 ->
   Cong C A1 C B1 -> Cong C A2 C B2 ->
   Midpoint M1 A1 B1 -> Midpoint M2 A2 B2 ->
   Le C A1 C A2 ->
   Bet M1 C M2.
Proof.
    intros.
    induction (eq_dec_points A2 C).
      subst C. apply le_zero in H5.
      subst A2.
      apply cong_reverse_identity in H1.
      subst B1.
      apply cong_reverse_identity in H2.
      subst B2.
      apply midpoint_identity_122 in H4.
      subst A1.
      apply between_trivial_122.
    (* A2 <> C *)
    assert (exists A, Midpoint C A2 A).
      apply symmetric_point_construction.
    exists_and H7 A2'.
    assert (exists B, Midpoint C B2 B).
      apply symmetric_point_construction.
    exists_and H7 B2'.
    assert (exists M, Midpoint C M2 M).
      apply symmetric_point_construction.
    exists_and H7 M2'.
    assert(Midpoint M2' A2' B2').
      assert(H4' := H4).
        apply midpoint_to_def in H4'.
      spliter.
      split.
        apply symmetry_preserves_bet with A2 M2 B2 C; assumption.
        apply symmetry_preserves_cong with A2 M2 M2 B2 C; assumption.
    assert (Le C A1 C A2').
      eapply l5_6 with C A1 C A2.
        assumption. apply cong_1212.
        apply midpoint_cong_1213. assumption.
    assert (Bet C A1 A2').
      induction (eq_dec_points C A1).
        subst A1.
        apply between_trivial_112.
      apply l6_13_1.
        repeat split.
          assumption.
          apply le_diff with C A1; assumption.
          apply l5_2 with A2.
            assumption.
            apply between_symmetry. assumption.
            apply midpoint_bet1. assumption.
        assumption.
    assert(Cong C A2' C B2').
        apply cong_XY12_XY34 with A2 C.
          apply midpoint_cong_2113. assumption.
          apply cong_21XY_YX34 with C B2.
            assumption.
            apply midpoint_cong_2113. assumption.
    assert (Le C B1 C B2').
      apply l5_6 with C A1 C A2'; assumption.
    assert (Bet C B1 B2').
      induction (eq_dec_points C B1).
        subst B1. apply between_trivial_112.
        apply l6_13_1.
          repeat split.
            assumption.
            apply le_diff with C B1; assumption.
            eapply l5_2 with B2.
              apply cong_diff_21_43 with C A2; assumption.
              apply between_symmetry. assumption.
              apply midpoint_bet1. assumption.
          assumption.
    assert (exists Q, Bet M2' Q C /\ Bet A1 Q B1).
      apply l3_17 with A2' B2'.
        apply between_symmetry. assumption.
        apply between_symmetry. assumption.
        apply midpoint_bet1. assumption.
    exists_and H16 Q.
    assert (IFSC A2' A1 C M2' B2' B1 C M2').
      apply def_to_IFSC.
        apply between_symmetry. assumption.
        apply between_symmetry. assumption.
        apply cong_2143. assumption.
        apply cong_2143. assumption.
        apply midpoint_cong_2131. assumption.
        apply cong_1212.
    assert (Cong A1 M2' B1 M2').
      apply IFSC_cong_24 with A2' C B2' C.
        assumption.
    assert (Cong Q A1 Q B1).
      apply l4_17_IFSC with M2' C; try assumption.
        apply cong_2143. assumption.
    assert (Midpoint Q A1 B1).
      apply def_to_midpoint.
        assumption.
        apply cong_2134. assumption.
    assert (Q=M1).
      apply symmetry_same_center with A1 B1; assumption.
    subst Q.
    apply between_exchange_1 with M2'.
      assumption.
      apply midpoint_bet2. assumption.
Qed.

(** This is Krippen lemma , proved by Gupta in its PhD in 1965 as Theorem 3.45 *)

Lemma l7_22 : forall A1 A2 B1 B2 C M1 M2,
   Bet A1 C A2 -> Bet B1 C B2 ->
   Cong C A1 C B1 -> Cong C A2 C B2 ->
   Midpoint M1 A1 B1 -> Midpoint M2 A2 B2 ->
   Bet M1 C M2.
Proof.
    intros.
    assert (Le C A1 C A2 \/ Le C A2 C A1).
      apply le_cases.
    induction H5.
      apply l7_22_aux with A1 A2 B1 B2; assumption.
      apply between_symmetry.
        apply l7_22_aux with A2 A1 B2 B1; try assumption.
          apply between_symmetry. assumption.
          apply between_symmetry. assumption.
Qed.

End T7_1.

Print All.
