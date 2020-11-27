Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_IFSC.

Section T5.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma flat_QEqui_mid : forall Q A B A' B',
  Bet Q A B' -> Bet Q B A' -> QEqui A B A' B'
  -> exists E, IFSC A E A' B A E A' B' /\ IFSC B E B' A B E B' A'
            /\ IFSC A E A' B A' E A B /\ IFSC A E A' B' A' E A B'
            /\ IFSC B E B' A B' E B A /\ IFSC B E B' A' B' E B A'.
(*  -> exists E, Bet A E A' /\ Bet B E B' /\ Cong A E E A'/\ Cong B' E E B. *)
Proof.
    intros.
    apply qequi_to_all in H1.
    spliter.
    inner_pasch_ex B' A A' B E Q. (* Bet A C D' -> Bet A D C' -> E *)
    exists E.
    assert(IFSC A E A' B A E A' B').
      apply IFSC_same_base; try assumption.
        apply cong_2134; assumption.
    assert(IFSC B E B' A B E B' A').
      apply IFSC_same_base; try assumption.
          apply cong_2134. assumption.
          apply cong_2143. assumption.
    assert (Cong B E E B').
      apply cong_2134.
      apply IFSC_cong_24 with A A' A A'; assumption.
    assert (Cong A E E A').
      apply cong_2134.
      apply IFSC_cong_24 with B B' B B'; assumption.
    split. assumption.
    split. assumption.
    split.
      apply IFSC_axial_sym; try assumption.
        apply cong_1243. assumption.
    split.
      apply IFSC_axial_sym; try assumption.
    split.
      apply IFSC_axial_sym; try assumption.
        apply cong_2143. assumption.
      apply IFSC_axial_sym; try assumption.
        apply cong_1243. assumption.
Qed.


Lemma rotate_DCDE : forall D C D' E,
  C<>D' -> IFSC D E D' C D' E D C
-> exists P R Q, Bet D' C R /\ Bet E C P /\ OFSC D E D' C P R Q C /\ OFSC P R Q C Q R P C.
Proof.
    intros.
    spliter.
    prolong E C P C D'.
    prolong D' C R C E.
    prolong P R Q R P.
    exists P.
    exists R.
    exists Q.
    split. assumption.
    split. assumption.
    assert(Cong_3 D E C D' E C).
      apply IFSC_cong3_124 with D' D. assumption.
    assert(OFSC D' C R P P C E D' ).
      apply def_to_OFSC_reverse.
        assumption. assumption. 
        apply cong_2134; assumption.
        apply cong_3421; assumption.
        apply cong_1221.
        apply cong_3412; assumption.
    apply OFSC_cong3 in H8.
    spliter.
    assert(Cong_3 P R C D E C).
      apply cong3_transitivity_1X_2X with D' E C.
        apply cong3_swap_321; assumption.
        assumption.
    assert (Cong R Q E D').
      apply cong_XY12_XY34 with P R.
        apply cong_2134; assumption.
        apply cong3_3256 with D' P; assumption.
    assert(OFSC D E D' C P R Q C).
      apply def_to_OFSC_with_cong3.
        apply H0. assumption.
        apply cong3_symmetry; assumption.
        apply cong_3412; assumption.
    split.
    assumption.
      induction (eq_dec_points D' E).
      (* D' = E *)
        subst. 
        assert(R=Q). 
          apply cong_identity with E. assumption.
        subst.
        assert(Q=P).
          apply cong_identity with Q.
            assumption.
        subst.
        apply OFSC_reflexivity.
          apply between_trivial_111.
      (* D' <> E *)
      assert(D<>E).
        apply cong_diff_12_34 with D' E.
        assumption.
        apply cong_3412. apply IFSC_cong_12 with D' C D C. assumption.
      apply OFSC_transitivity with D E D' C.
        apply OFSC_symmetry. assumption. left. assumption.
        apply OFSC_symmetry_24.
        apply OFSC_transitivity with D E D' C.
        apply OFSC_symmetry. apply IFSC_to_OFSC. assumption. left. assumption.
        assumption.
        left. assumption.
      left. apply diff_symmetry; assumption.
Qed.

Lemma bet4_QEqui : forall B B' C C' D D',
  C<>C'-> Bet_4 B C D' B' -> Bet_4 B D C' B'
  -> QEqui C D C' D' -> Bet B C D.
Proof.
    intros.
    assert(Bet B C D') by apply H0.
    assert(Bet B D C') by apply H1.
    assert(H' := flat_QEqui_mid B C D C' D' H3 H4 H2).
    apply qequi_to_all in H2.
    exists_and H' E.
    assert(Cong C E E C').
      apply cong_1243. apply IFSC_cong_12 with C' D' C D'. assumption.
    assert(C<>D').
      apply (cong_diff_12 C C' D'); assumption.
    assert(exists P R Q, Bet D' C R /\ Bet E C P /\ OFSC D E D' C P R Q C /\ OFSC P R Q C Q R P C).
      apply rotate_DCDE; assumption.
    exists_and H18 P.
    exists_and H19 R.
    exists_and H18 Q.
(* C, D', B, B', C', P appartiennent a la mediatrice de [PQ] *)
    assert (Cong C P C Q).
      apply cong_2143.
      apply OFSC_cong_14 with R Q R P; assumption.
    assert(R<>C).
      assert(C<>E).
        apply (cong_diff_14 C E C'); assumption.
      apply cong_diff_12_34 with C E.
        assumption.
        apply cong_2134.
        apply OFSC_cong_24 with D D' P Q; assumption.
    assert (Cong D' P D' Q).
      apply l4_17_OFSC with R C; try assumption.
        apply between_symmetry; assumption.
        apply cong_2143.
        apply OFSC_cong_12 with Q C P C; assumption.
    assert (Cong B P B Q).
      apply l4_17_OFSC with D' C; try assumption.
        apply diff_symmetry; assumption.
        apply between_symmetry; apply H0.
    assert (Cong B' P B' Q).
      apply l4_17_OFSC with C D'; try assumption.
        apply H0. 
    assert (Cong C' P C' Q).
      apply l4_17_IFSC with B B'; try assumption.
        apply H1.
    assert (Cong P P P Q).
      apply l4_17_OFSC with C' C; try assumption.
      apply diff_symmetry; assumption.
      apply between_outer_transitivity_2 with E.
        apply between_symmetry; apply H5.
        assumption.
        apply diff_symmetry.
          apply (cong_diff_14 C E C'); assumption.
    assert(P=Q).
      apply cong_reverse_identity with P; assumption.
    subst P.
    assert(Q=R).
      apply between_identity.
      apply (OFSC_bet1 Q R Q C Q R Q C); assumption.
    subst Q.
    assert(D=E).
      apply cong_identity with R.
      apply (OFSC_cong_12 D E D' C R R R C); assumption.
    subst E.
    assert(D=D').
      apply cong_identity with R.
      apply (OFSC_cong_23 D D D' C R R R C); assumption.
    subst.
    apply H0.
Qed.

End T5.

Print All.

