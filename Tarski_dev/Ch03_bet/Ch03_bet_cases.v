Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet5.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet4_cong4.

Section T5.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Definition preRhombus A B A' B' := 
Cong A B B A' /\ Cong B A' A' B' /\ Cong A B' A' B' /\ Cong A B A B'
/\ Cong A B A' B' /\ Cong A B' B A'.

Lemma preRhombus_mid : forall Q A B A' B',
  Bet Q A B' -> Bet Q B A' -> preRhombus A B A' B' 
  -> exists E, Bet A E A' /\ Bet B' E B /\ Cong A E E A'/\ Cong B' E E B.
Proof.
    intros.
    unfold preRhombus in *.
    spliter.
    inner_pasch_ex B' A A' B E Q. (* Bet A C D' -> Bet A D C' -> E *)
    exists E.
    apply between_symmetry in H8.
    assert (IFSC A E A' B A E A' B').
      apply IFSC_axial_sym2; try assumption.
      apply cong_2134; assumption.
    assert (Cong B' E E B).
      apply cong_4312.
      apply l4_2 with A A' A A'; assumption.
    assert (IFSC B' E B A B' E B A').
      apply IFSC_axial_sym2; try assumption.
        apply cong_2143; assumption.
        apply cong_2134; assumption.
    assert (Cong A E E A').
      apply cong_2134.
      apply l4_2 with B' B B' B; assumption.
    repeat split; assumption.
Qed.

Lemma l5_1_preRhombus : forall A B C D,
  A<>B -> B<>C -> Bet A B C -> Bet A B D -> exists C' D' B',
  preRhombus C D C' D' /\ Bet_4 B C D' B' /\ Bet_4 B D C' B'.
Proof.
    intros.
    prolong4 A B D C' C D.
    exists C'.
    prolong4 A B C D' C D.
    exists D'.
      assert(Cong  C D' D C').
        apply cong_1234_1256 with C D; assumption.
    prolong4 A B C' B' B C.
    exists B'.
    assert(Bet_5 A B D C' B').
      apply bet5_bet4_35; assumption.
    prolong4 A C D' B'' B D.
    assert(Bet_5 A B C D' B'').
      apply bet5_bet4_25; assumption.
    assert(Cong_4 B C D' B'' B' C' D B).
      apply bet4_12_23_cases.
        apply bet5_bet4_2345 with A; assumption.
        apply bet4_symmetry.
        apply bet5_bet4_2345 with A; assumption.
        apply cong_1243; assumption.
        apply cong_1243; assumption.
        left. apply cong_3421; assumption.
    assert( B'' = B').
      apply construction_uniqueness_simple with A B.
        assumption.
        apply bet5_bet_125 with C D'; assumption.
        apply bet5_bet_125 with D C'; assumption.
        apply cong_1243. apply cong4_14 with C D' C' D.
          assumption.
    subst B''.
    assert (Cong C D C' D').
      assert (OFSC B C D' C' B' C' D C).
        apply OFSC_central_sym_with_cong3.
          apply bet5_bet_234 with A B'; assumption.
          apply cong4_cong3_123 with B' B; assumption.
          apply cong4_24 with B D' B' D; assumption.
      apply cong_4321.
      apply OFSC_cong_34 with B C B' C'.
        assumption.
        left; assumption.
    assert(Cong C D' C' D').
      apply cong_1234_1256 with C D; assumption.
    assert(Cong D C' C' D').
      apply cong_1234_1256 with C D; assumption.
    split.
    repeat split; try assumption.
    split.
      apply bet5_bet4_2345 with A; assumption.
      apply bet5_bet4_2345 with A; assumption.
Qed.

Lemma rotate_DCDE : forall D C D' E,
  C<>D' -> OFSC D E D' C D' E D C 
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
      apply OFSC_cong3_124 with D' D; assumption.
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
      apply cong3_transitivity_12_23_13 with D' E C.
      apply cong3_swap_321; assumption.
      apply cong3_symmetry; assumption.
    assert (Cong R Q E D').
      apply cong_1234_1256 with P R.
        apply cong_2134; assumption.
        apply cong_2134.
        apply cong3_23 with D' P; assumption.
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
        apply cong_3412; apply H0.
      assert(Cong D' C Q C).
        apply OFSC_cong_34 with D E P R.
          assumption.
          left; assumption.
      apply def_to_OFSC.
        assumption.
        apply between_symmetry; assumption.
        apply cong_2143; assumption.
        apply cong_3412; assumption.
        apply cong_1234_3456 with D' C.
          apply cong_4321; assumption.
          assumption.
        apply cong_1212.
      left. apply diff_symmetry; assumption.
Qed.

Lemma bet4_preRhombus : forall B B' C C' D D',
  C<>C'-> Bet_4 B C D' B' -> Bet_4 B D C' B'
  -> preRhombus C D C' D' -> Bet B C D.
Proof.
    intros.
    assert(exists E, Bet C E C' /\ Bet D' E D /\ Cong C E E C'/\ Cong D' E E D).
      apply preRhombus_mid with B.
        apply H0.
        apply H1.
        assumption.
    exists_and H3 E.
    unfold preRhombus in *.
    spliter.
    assert(C<>D').
      apply (cong_diff_12 C C' D'); assumption.
    assert(exists P R Q, Bet D' C R /\ Bet E C P /\ OFSC D E D' C P R Q C /\ OFSC P R Q C Q R P C).
      apply rotate_DCDE.
        assumption.
        apply def_to_OFSC; try assumption.
        apply between_symmetry; assumption.
        apply cong_4312; assumption.
        apply cong_2134; assumption.
        apply cong_2143; assumption.
        apply cong_1212.
    exists_and H13 P.
    exists_and H14 R.
    exists_and H13 Q.
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
      apply l4_17_OFSC with R C. assumption.
        apply between_symmetry; assumption.
        apply cong_2143.
        apply OFSC_cong_12 with Q C P C; assumption.
        assumption.
    assert (Cong B P B Q).
      apply l4_17_OFSC with D' C; try assumption.
        apply diff_symmetry; assumption.
        apply between_symmetry; apply H0.
    assert (Cong B' P B' Q).
      apply l4_17_OFSC with C D'; try assumption.
        apply H0. 
    assert (Cong C' P C' Q).
      induction(eq_dec_points B B').
        (* B = B' *)
        subst B'.
        assert(B = C /\ C = D').
          apply bet4_equality_2.
            assumption.
        spliter.
        subst D'. subst C.
        assert(B = D /\ D = C').
          apply bet4_equality_2.
            assumption.
        spliter.
        subst C'. subst D.
        assumption.
        (* B <> B' *)
        apply l4_17_IFSC with B B'; try assumption.
          apply H1.
    assert (Cong P P P Q).
      apply l4_17_OFSC with C' C; try assumption.
      apply diff_symmetry; assumption.
      apply between_outer_transitivity_2 with E.
        apply between_symmetry; assumption.
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

Lemma l5_1 : forall A B C D,
  A<>B -> Bet A B C -> Bet A B D -> Bet A C D \/ Bet A D C.
Proof.
    intros.
    induction (eq_dec_points B C).
    (* B = C -> Bet A C D *)
      subst. left. assumption.
    (* B <> C *)
    assert(exists C' D' B', preRhombus C D C' D' /\ Bet_4 B C D' B' /\ Bet_4 B D C' B').
      apply l5_1_preRhombus with A; assumption.
      exists_and H3 C'.
      exists_and H4 D'.
      exists_and H3 B'.
    induction (eq_dec_points C C').
    (* C = C' -> Bet A D C *)
      subst C'. right. 
      apply between_exchange_2 with B. 
        assumption.
        apply H5.
    (* C <> C' -> Bet A C D *)
    left.
    apply between_exchange_2 with B.
      assumption.
      eapply bet4_preRhombus with B' C' D'; assumption.
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

Lemma betsym_left : forall A1 B1 C1 A2 B2 C2,
   Bet A1 B1 C1 \/ Bet A2 B2 C2 -> Bet C1 B1 A1 \/ Bet A2 B2 C2.
Proof.
    intros.
    induction H.
      left. apply between_symmetry; assumption.
      right; assumption.
Qed.

Lemma betsym_right : forall A1 B1 C1 A2 B2 C2,
   Bet A1 B1 C1 \/ Bet A2 B2 C2 
-> Bet A1 B1 C1 \/ Bet C2 B2 A2.
Proof.
    intros.
    induction H.
      left. assumption. 
      right. apply between_symmetry; assumption.
Qed.

Lemma betsym_left_right : forall A1 B1 C1 A2 B2 C2,
   Bet A1 B1 C1 \/ Bet A2 B2 C2 
-> Bet C1 B1 A1 \/ Bet C2 B2 A2.
Proof.
    intros.
    apply betsym_left.
    apply betsym_right.
    assumption.
Qed.

Lemma disjunction_commutativity : forall A B : Prop,
    A \/ B -> B \/ A.
Proof.
    intros.
    induction H.
    right. assumption.
    left. assumption.
Qed.

Lemma disjunction_12 : forall A B C : Prop,
 A \/ B -> A \/ B \/ C.
Proof.
    intros.
    induction H.
      left. assumption.
      right. left. assumption.
Qed.

Lemma disjunction_13 : forall A B C : Prop,
 A \/ C -> A \/ B \/ C.
Proof.
    intros.
    induction H.
      left. assumption.
    right. right. assumption.
Qed.

Lemma disjunction_to_12 : forall A B C : Prop,
 A \/ B \/ C -> (A \/ B) \/ C.
Proof.
    intros.
    induction H.
      left. left. assumption.
    induction H.
      left. right. assumption.
      right. assumption.
Qed.

Lemma disjunction_to_13 : forall A B C : Prop,
 A \/ B \/ C -> (A \/ C) \/ B.
Proof.
    intros.
    induction H.
      left. left. assumption.
    induction H.
      right. assumption.
      left. right. assumption.
Qed.


End T5.

Print All.
