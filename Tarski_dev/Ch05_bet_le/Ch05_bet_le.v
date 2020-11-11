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
    induction(eq_dec_points A O).
    (* A = O *)
      subst O.
      assert (o=a).
        apply le_zero with A; assumption.
      subst o. assumption.
    (* A <> O *)
      induction(eq_dec_points B O).
      (* B = O *)
      subst O.
      assert (o=b). 
        apply le_zero with B; assumption.
      subst. apply le_2143; assumption.
      (* B <> O *)
      exists_and H1 a'.
        apply between_symmetry in H1.
        apply cong_2134 in H5.
      exists_and H2 b'.
      assert(Bet_4 A a' b' B).
        apply bet4_sides2 with O; assumption.
      assert(Le a' b' A B).
        apply bet4_le_23; assumption.
      assert(Cong a b a' b').
        apply (l2_11 a o b a' O b').
          assumption.
          apply between_inner with A B; try assumption.
          apply cong_1243; assumption.
        assumption.
      apply(l5_6 a' b' A B a b A B).
        assumption.
        apply cong_3412; assumption.
        apply cong_1212.
Qed.


End Bet_Le.

Print All.

