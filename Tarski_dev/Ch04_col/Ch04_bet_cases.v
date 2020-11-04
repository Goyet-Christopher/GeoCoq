Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_FSC.

Section T5.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l5_1 : forall A B C D,
  A<>B -> Bet A B C -> Bet A B D -> Bet A C D \/ Bet A D C.
Proof.
    intros.
    prolong4 A B D C' C D.
    prolong4 A B C D' C D.
      assert(Cong C D' D C').
        apply cong_1234_1256 with C D; assumption.
    prolong4 A B C' B' B C.
    assert(Bet_4 A D C' B' /\ Bet_4 B D C' B').
      apply bet4_transitivity_21; assumption.
      spliter.
    prolong4 A C D' B'' B D.
    assert(Bet_4 A B D' B'' /\ Bet_4 B C D' B'').
      apply bet4_transitivity_31; assumption.
      spliter.
    assert (Cong B C' C B'').
      apply l2_11_reverse with D D'; try assumption.
        apply bet4_bet_234 with A; assumption.
        apply bet4_bet_234 with A; assumption.
    assert (Cong B B' B B'').
      apply l2_11_reverse with C' C; try assumption.
        apply bet4_bet_234 with A; assumption.
        apply bet4_bet_124 with D'; assumption.
    assert(B'=B'').
      apply construction_uniqueness with A B B B''.
      assumption.
      apply bet4_bet_124 with C'; assumption.
      assumption.
      apply bet4_bet_124 with D'; assumption.
      apply cong_1212.
    subst B''.
    assert (FSC B C D' C' B' C' D C).
      apply def_to_FSC.
      repeat split.
      apply bet_col_123;apply bet4_bet_123 with B'; assumption.
      apply cong_1243; assumption.
      apply l2_11 with C C'.
        apply bet4_bet_123 with B'; assumption.
        apply bet4_bet_432 with B; assumption.
      apply cong_1243; assumption.
      apply cong_1243; assumption.
      apply cong_1243; assumption.
      apply cong_1243; assumption. 
      apply cong_1221.
    induction (eq_dec_points B C).
    (* B = C -> Bet A C D *)
      subst C. left. assumption.
    (* B <> C *)
    inner_pasch_ex D' C C' D E A.
    assert (Cong C D C' D').
      apply cong_4321.
      apply l4_16 with B C B' C'; assumption.
    assert(Cong C D' C' D').
      apply cong_1234_1256 with C D; assumption.
    assert(Cong C' D C' D').
      apply cong_2134.
      apply cong_1234_1256 with C D; assumption.
(* C D C' D' est un losange *)
    assert (IFSC D E D' C D E D' C').
      apply IFSC_axial_sym2. assumption.
      apply cong_2134; assumption.
      apply cong_2143; assumption.
    assert (Cong E C E C').
      apply l4_2 with D D' D D'; assumption.
    assert (IFSC C E C' D C E C' D').
      apply IFSC_axial_sym2; assumption.
    assert (Cong E D E D').
      apply l4_2 with C C' C C'; assumption.
    induction (eq_dec_points C C').
    (* C = C' -> Bet A D C *)
      subst C'. right.
      apply bet4_bet_123 with B'; assumption.
    (* C <> C' *)
    assert(C<>D').
      intro. subst D'.
      assert(C' = C).
        apply cong_reverse_identity with C; assumption.
        match goal with
          | H : C<>C' |- _ => apply H;apply eq_sym
          | H : C'<>C |- _ => apply H
        end.
        assumption.
    assert(Bet C' E C).
      apply between_symmetry; assumption.
    prolong4 C' E C P C D'.
    apply bet4_symmetry in H31.
    prolong D' C R C E.
    prolong P R Q R P.
    assert (FSC D' C R P P C E D').
      apply def_to_FSC.
      repeat split.
      apply bet_col_123; assumption.
      apply cong_2143; assumption.
      apply l2_11 with C C; try assumption.
      apply bet4_bet_123 with C'. assumption.
      apply cong_2143; assumption.
      apply cong_3412; assumption.
      apply cong_3412; assumption.
      apply cong_1221. 
      apply cong_3412; assumption.
    assert (Cong R P E D').
      apply l4_16 with D' C P C.
      assumption.
      apply diff_symmetry. assumption.
    assert (Cong R Q E D').
      apply cong_1234_1256 with R P; assumption.
    assert (Cong R Q E D).
      apply cong_1234_5634 with E D'; assumption.
    assert (FSC D' E D C P R Q C).
      apply def_to_FSC.
      repeat split.
      apply bet_col_123. apply between_symmetry; assumption.
      apply cong_4321; assumption.
      apply l2_11 with E R.
        apply between_symmetry; assumption.
        assumption.
        apply cong_4321; assumption.
        apply cong_3412; assumption.
        apply cong_3412; assumption.
        apply cong_2143; assumption.
        apply cong_2143; assumption.
    assert (Cong D C Q C).
      induction (eq_dec_points D' E).
      (* D' = E *)
        subst. 
        assert(R=Q). apply cong_identity with E. assumption.
        subst.
        assert(E=D). apply cong_identity with E. assumption.
        subst.
        assert(Q=P). apply cong_identity with Q. assumption.
        subst.
        apply FSC_cong_12 with P P D D; assumption.
      (* D' <> E *)
      apply l4_16 with D' E P R; assumption.
    assert (Cong C P C Q).
      apply cong_transitivity with C D.
        apply cong_transitivity with C D'.
          apply cong_3412; assumption.
          apply cong_3412; assumption.
      apply cong_2143; assumption.
    assert(R<>C).
      intro. subst.
        assert(C=E). apply cong_identity with C; assumption.
        subst.
        assert(E=C'). apply cong_reverse_identity with E; assumption.
        subst.
        match goal with
          | H : C'<>C' |- _ => apply H
        end.
        apply eq_refl.
    assert (Cong D' P D' Q).
      apply l4_17 with R C; try assumption.
      apply bet_col_321. assumption.
    assert (Cong B P B Q).
      apply l4_17 with C D'; try assumption.
      apply bet_col_312.
      apply bet4_bet_234 with A. assumption.
    assert (Cong B' P B' Q).
      apply l4_17 with C D'; try assumption.
      apply bet_col_123.
      apply bet4_bet_234 with B. assumption.
    assert (Cong C' P C' Q).
      induction(eq_dec_points B B').
        (* B = B' *)
        subst B'.
        assert(B = C /\ C = D').
          apply bet4_equality_2; assumption.
        spliter.
        subst D'. subst C.
        assert(B = D /\ D = C').
          apply bet4_equality_2; assumption.
        spliter.
        subst C'. subst D.
        assumption.
        (* B <> B' *)
        apply l4_17 with B B'; try assumption.
        apply bet_col_132. 
        apply bet4_bet_234 with A; assumption.
    assert (Cong P P P Q).
      apply l4_17 with C C'; try assumption.
      apply bet_col_312. 
      apply bet4_bet_124 with E; assumption.
    assert(P=Q).
      apply cong_reverse_identity with P; assumption.
    subst.
    assert(Q=R).
      apply between_identity; assumption.
    subst.
    assert(E=D).
      apply cong_reverse_identity with R; assumption.
    subst.
    assert(D=D').
      apply cong_reverse_identity with R; assumption.
    subst.
    left. apply bet4_bet_134 with B; assumption.
Qed.

Lemma l5_2 : forall A B C D,
  A<>B -> Bet A B C -> Bet A B D -> Bet B C D \/ Bet B D C.
Proof.
    intros.
    assert (Bet A C D \/ Bet A D C).
      apply l5_1 with B; assumption.
    induction H2.
    left. apply between_exchange_1 with A; assumption.
    right. apply between_exchange_1 with A; assumption.
Qed.

Lemma segment_construction_2 : forall A Q B C,
  Q<>A -> exists X, (Bet Q A X \/ Bet Q X A) /\ Cong Q X B C.
Proof.
    intros.
    prolong A Q A' Q A.
    prolong A' Q X B C.
    exists X.
    assert(A' <> Q).
      apply cong_diff_12_43 with Q A; assumption.
    split.
    apply l5_2 with A'.
      assumption.
      apply between_symmetry; assumption.
      assumption.
    apply cong_3412; assumption.
Qed.

Lemma l5_3 : forall A B C D,
  Bet A B D -> Bet A C D -> Bet A B C \/ Bet A C B.
Proof.
    intros.
    assert (exists P, Bet D A P /\ A<>P).
      apply point_construction_different.
    exists_and H1 P.
    apply diff_symmetry in H2.
    assert (Bet P A B).
      apply between_exchange_4 with D.
      apply between_symmetry; assumption.
      assumption.
    assert (Bet P A C).
      apply between_exchange_4 with D.
      apply between_symmetry; assumption.
      assumption.
    apply l5_2 with P; assumption.
Qed.

Lemma between_cong_3 : forall A B D E, 
  A <> B -> Bet A B D -> Bet A B E -> Cong B D B E -> D = E.
Proof.
    intros.
    assert(Bet B D E \/ Bet B E D).
      apply l5_2 with A; assumption.
    apply between_cong with B.
      induction H3.
        assumption.
        assert(E=D).
          apply between_cong with B.
          assumption.
          apply cong_3412; assumption.
        subst.
        assumption.
    assumption.
Qed.

Lemma fourth_point : forall A B C P, 
  A <> B -> B <> C -> Col A B P -> Bet A B C ->
  Bet P A B \/ Bet A P B \/ Bet B P C \/ Bet B C P.
Proof.
    intros.
    induction H1.
      assert(Bet B C P \/ Bet B P C).
        apply l5_2 with A; assumption.
      right; right.
      induction H3.
        right; assumption.
      left; assumption.
    induction H1.
      right; left; assumption.
    left. apply between_symmetry. assumption.
Qed.

End T5.

Print All.
