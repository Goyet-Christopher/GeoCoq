Require Export GeoCoq.Tarski_dev.Ch03_bet.bet5.Ch03_bet5_bet4.
Require Export GeoCoq.Tarski_dev.Ch03_bet.bet5.Ch03_bet5_bet.
Require Export GeoCoq.Tarski_dev.Ch03_bet.bet4.Ch03_bet4_exists.
Require Export GeoCoq.Tarski_dev.Ch03_bet.bet4.Ch03_bet4_cong4.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_QEqui.

Section T5.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma l5_1_QEqui : forall A B C D,
  A<>B -> B<>C -> Bet A B C -> Bet A B D -> exists C' D' B',
  QEqui C D C' D' /\ Bet_4 B C D' B' /\ Bet_4 B D C' B'.
Proof.
    intros.
    prolong4 A B D C' C D.
    exists C'.
    prolong4 A B C D' C D.
    exists D'.
    assert(Cong  C D' D C').
      apply cong_XY12_XY34 with C D; assumption.
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
      eapply construction_uniqueness with A B B' B.
        assumption.
        apply bet5_bet_125 with C D'. assumption.
        apply cong4_14 with C D' C' D. assumption.
        apply bet5_bet_125 with D C'; assumption.
        apply cong_1221.
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
    split.
      apply qequi_2adj_1op_3; assumption.
    split.
      apply bet5_bet4_2345 with A; assumption.
      apply bet5_bet4_2345 with A; assumption.
Qed.

Lemma l5_1 : forall A B C D,
  A<>B -> Bet A B C -> Bet A B D -> Bet A C D \/ Bet A D C.
Proof.
    intros.
    induction (eq_dec_points B C).
    (* B = C -> Bet A C D *)
      subst. left. assumption.
    (* B <> C *)
    assert(exists C' D' B', QEqui C D C' D' /\ Bet_4 B C D' B' /\ Bet_4 B D C' B').
      apply l5_1_QEqui with A; assumption.
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
      apply bet4_QEqui with B' C' D'; assumption.
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

Lemma l5_4 : forall A B C B0 C0,
 A<>B-> Bet A B C -> Bet A B B0 -> Bet A C0 C 
-> Bet A B0 C0 \/ Bet A C0 B0.
Proof.
    intros.
    assert(Bet A B C0 \/ Bet A C0 B).
      apply l5_3 with C; assumption.
    induction H3.
      apply l5_1 with B; assumption.
    right.
      apply between_exchange_3 with B; assumption.
Qed.

Lemma between_inner_2 : forall A B C D E,
 Bet A B E -> Bet A D E -> Bet B C D -> Bet A C E.
Proof.
    intros.
    assert (H2 := l5_3 A B D E H H0).
    induction H2.
    apply between_exchange_3 with D.
      apply between_exchange_2 with B; assumption.
      assumption.
    apply between_exchange_3 with B.
      apply between_exchange_2 with D.
        assumption.
        apply between_symmetry. assumption.
      assumption.
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
