Require Export GeoCoq.Tarski_dev.Ch05_le_lt_ge_gt.Ch05_lt.
Require Export GeoCoq.Tarski_dev.Ch05_le_lt_ge_gt.Ch05_bet_cong_eq.

Section Bet_Lt.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma bet2_lt2__lt : forall O o A B a b : Tpoint,
  Bet a o b -> Bet A O B -> Lt o a O A -> Lt o b O B -> Lt a b A B.
Proof.
    intros.
    apply lt_to_def in H1.
    apply lt_to_def in H2.
    spliter.
    split.
    apply(bet2_le2_le O o A B a b); assumption.
    intro.
    exists_and H1 a'.
      apply between_symmetry in H1.
    exists_and H2 b'.
    assert(Bet_4 A a' b' B).
          apply bet4_sides2 with O; assumption.
    assert(Cong a b a' b').
      apply l2_11 with o O.
        assumption.
        apply between_inner with A B; assumption.
        apply cong_2143; assumption.
        assumption.
    assert(Cong a' b' A B).
      apply cong_transitivity with a b.
        apply cong_3412; assumption.
        assumption.
    induction(eq_dec_points A a').
    (* A = a' *)
      subst a'.
        assert(Bet A b' B).
          apply bet4_bet_234 with A; assumption.
        assert(b'=B).
          apply between_cong with A; assumption.
        subst b'.
        contradiction.
    (* A <> a' *)
      assert(A=a' /\ b'=B).
        apply bet_cong_eq.
          apply bet4_bet_123 with B. assumption.
          apply bet4_bet_134 with a'. assumption.
          assumption.
      spliter.
      contradiction.
Qed.

Lemma bet2_lt_le_lt : forall O o A B a b : Tpoint,
  Bet a o b -> Bet A O B -> Le o a O A -> Lt o b O B -> Lt a b A B.
Proof.
  intros.
  apply lt_to_def in H2.
  spliter.
  split.
    apply(bet2_le2_le O o A B a b); assumption.
  intro.
    exists_and H2 b'.
    exists_and H1 a'.
      apply between_symmetry in H1.
      apply cong_2143 in H6.
    assert(Bet_5 A a' O b' B).
      apply bet5_bet_1; assumption.
    assert(Cong a b a' b').
      apply l2_11 with o O; try assumption.
      apply bet5_bet_234 with A B; assumption.
    assert(Cong a' b' A B).
      apply cong_1234_1256 with a b; assumption.
    assert(A=a'/\b'=B).
      apply bet_cong_eq.
        apply bet5_bet_124 with O B. assumption.
        apply bet5_bet_145 with a' O. assumption.
        assumption.
    spliter.
    subst b'.
    apply H3.
    assumption.
Qed.

End Bet_Lt.

Print All.

