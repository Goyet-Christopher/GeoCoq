Require Export GeoCoq.Tarski_dev.Ch05_bet_le.Ch05_le.

Section Bet_Le.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet_le_3231 : forall A B C,
  Bet A B C -> Le C B C A.
Proof.
    intros.
    apply def2_to_le.
    exists A.
    split.
    apply between_symmetry.
    assumption.
    apply cong_reflexivity.
Qed.

Lemma bet_le_2331 : forall A B C,
  Bet A B C -> Le B C C A.
Proof.
    intros.
    apply le_2134.
    apply bet_le_3231.
    assumption.
Qed.

Lemma bet_le_3213 : forall A B C,
  Bet A B C -> Le C B A C.
Proof.
    intros.
    apply le_1243.
    apply bet_le_3231.
    assumption.
Qed.

Lemma bet_le_2313 : forall A B C,
  Bet A B C -> Le B C A C.
Proof.
    intros.
    apply le_2143.
    apply bet_le_3231.
    assumption.
Qed.

Lemma bet_le_1213 : forall A B C,
  Bet A B C -> Le A B A C.
Proof.
    intros.
    apply bet_le_3231.
    apply between_symmetry.
    assumption.
Qed.

Lemma bet_le_2113 : forall A B C,
  Bet A B C -> Le B A A C.
Proof.
    intros.
    apply le_2134.
    apply bet_le_1213.
    assumption.
Qed.

Lemma bet_le_1231 : forall A B C,
  Bet A B C -> Le A B C A.
Proof.
    intros.
    apply le_1243.
    apply bet_le_1213.
    assumption.
Qed.

Lemma bet_le_2131 : forall A B C,
  Bet A B C -> Le B A C A.
Proof.
    intros.
    apply le_2143.
    apply bet_le_1213.
    assumption.
Qed.

Lemma l5_12_a : forall A B C, 
  Bet A B C -> Le A B A C /\ Le B C A C.
Proof.
    intros.
    split.
    apply bet_le_1213; assumption.
    apply bet_le_2313; assumption.
Qed.

Lemma bet4_le_12 : forall A B C D,
  Bet_4 A B C D -> Le A B A D.
Proof.
    intros.
    apply bet_le_1213.
    apply bet4_bet_124 with C.
    assumption.
Qed.

Lemma bet4_le_13 : forall A B C D,
  Bet_4 A B C D -> Le A C A D.
Proof.
    intros.
    apply bet_le_1213.
    apply bet4_bet_134 with B.
    assumption.
Qed.

Lemma bet4_le_23 : forall A B C D,
  Bet_4 A B C D -> Le B C A D.
Proof.
    intros.
    assert(Le A C A D).
      apply bet4_le_13 with B; assumption.
    assert(Le B C A C).
      apply bet_le_2313.
      apply bet4_bet_123 with D.
      assumption.
    apply le_transitivity with A C;
      assumption.
Qed.


Lemma bet_le_eq : forall A B C,
  Bet A B C -> Le A C B C -> A = B.
Proof.
    intros.
    assert(Le C B C A).
      apply bet_le_3231; assumption.
    assert(Cong A C B C).
      apply le_anti_symmetry.
        assumption.
      apply le_2143.
      assumption.
    apply between_cong_reverse with C;
    assumption.
Qed.

Lemma bet_le_eq_reverse : forall A B C,
  Bet A B C -> Le A C A B -> B = C.
Proof.
    intros.
      assert(Le A B A C).
        apply bet_le_1213; assumption.
      assert(Cong A B A C).
        apply le_anti_symmetry; assumption.
        apply between_cong with A; assumption.
Qed.

Lemma l5_12_b : forall A B C, 
  Col A B C -> Le A B A C -> Le B C A C -> Bet A B C.
Proof.
    intros.
    induction H.
    (* Bet A B C *)
      assumption.
    induction H.
    (* Bet A C B *)
      assert(C = B).
        apply bet_le_eq_reverse with A; assumption.
      subst B.
      apply between_trivial_122.
    (* Bet B A C *)
      assert(B = A).
        apply bet_le_eq with C; assumption.
      subst A.
      assumption.
Qed.

Lemma bet2_le2_le : forall O o A B a b,
  Bet a o b -> Bet A O B -> Le o a O A -> Le o b O B -> Le a b A B.
Proof.
    intros.
      exists_and H1 a'.
        apply between_symmetry in H1.
      exists_and H2 b'.
      assert(Bet_4 A a' b' B).
        apply bet4_sides2 with O; assumption.
      assert(Le a' b' A B).
        apply bet4_le_23; assumption.
      assert(Cong a b a' b').
        apply (l2_11 a o b a' O b').
          assumption.
          apply between_inner with A B; try assumption.
          apply cong_2143; assumption.
        assumption.
      apply(l5_6 a' b' A B a b A B).
        assumption.
        apply cong_3412; assumption.
        apply cong_1212.
Qed.

Lemma bet2_le2_le_13 : forall A B C A' B' C', 
  Bet A B C -> Bet A' B' C'
  -> Le A B A' B' -> Le B C B' C' 
  -> Le A C A' C'.
Proof.
    intros.
    apply bet2_le2_le with B' B; try assumption.
      apply le_2143; assumption.
Qed.

Lemma bet2_le2_le_23 : forall A B C A' B' C', 
  Bet A B C -> Bet A' B' C'
  -> Le A B A' B' -> Le A' C' A C
  -> Le B' C' B C.
Proof.
    intros.
    induction(eq_dec_points A B).
    (* A = B *)
      subst B.
      apply le_transitivity with A' C'.
        apply bet_le_2313. assumption.
        assumption.
    (* A <> B *)
    apply le_to_def2 in H1.
    exists_and H1 B0.
    apply le_to_def in H2.
    exists_and H2 C0.
    assert(Bet A B0 C0).
      assert (Bet A B0 C0 \/ Bet A C0 B0).
        apply l5_4 with B C; assumption.
      assert(Col A B0 C0).
        induction H6.
          apply bet_col_123. assumption.
          apply bet_col_132. assumption.
      assert(Le A' B' A' C').
        apply bet_le_1213. assumption.
      assert(Le A B0 A C0).
        apply l5_6 with A' B' A' C'.
          assumption.
          apply cong_3412. assumption.
          assumption.
      induction H6.
        assumption.
        assert(C0 = B0).
          apply bet_le_eq_reverse with A; assumption.
        subst C0. apply between_trivial_122.
    assert(Bet_5 A B B0 C0 C).
      apply bet5_bet_2; assumption.
    apply (l5_6 B0 C0 B C).
      apply le_transitivity with B C0.
        apply l5_12_a. apply bet5_bet_234 with A C. assumption.
        apply l5_12_a. apply bet5_bet_245 with A B0. assumption.
      apply l4_3_1 with A A'; try assumption.
        apply cong_3412; assumption.
      apply cong_1212.
Qed.


Lemma bet2_le2_le_12 : forall A B C A' B' C',
  Bet A B C -> Bet A' B' C'
  -> Le B C B' C' -> Le A' C' A C 
  -> Le A' B' A B.
Proof.
  intros.
  apply le_2143.
  apply bet2_le2_le_23 with C C'.
    apply between_symmetry; assumption.
    apply between_symmetry; assumption.
    apply le_2143; assumption.
    apply le_2143; assumption.
Qed.

End Bet_Le.

Print All.

