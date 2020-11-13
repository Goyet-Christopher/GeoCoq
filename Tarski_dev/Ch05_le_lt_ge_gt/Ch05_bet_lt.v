Require Export GeoCoq.Tarski_dev.Ch05_le_lt_ge_gt.Ch05_lt.
Require Export GeoCoq.Tarski_dev.Ch05_le_lt_ge_gt.Ch05_bet_cong_eq.

Section Bet_Lt.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma bet2_lt2_lt : forall O o A B a b : Tpoint,
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
        apply bet4_cong_eq; assumption.
      spliter.
      contradiction.
Qed.

Lemma bet2_le_lt_lt : forall O o A B a b : Tpoint,
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
      apply bet5_bet4_1245 in H7.
      apply bet4_cong_eq; assumption.
    spliter.
    subst b'.
    apply H3.
    assumption.
Qed.

Lemma bet2_lt_le_lt : forall O o A B a b : Tpoint,
  Bet a o b -> Bet A O B -> Lt o a O A -> Le o b O B -> Lt a b A B.
Proof.
    intros.
    apply lt_2143.
    apply bet2_le_lt_lt with O o.
      apply between_symmetry. assumption.
      apply between_symmetry. assumption.
      assumption.
      assumption.
Qed.

Lemma bet2_lt2_lt_13 : forall A B C A' B' C' : Tpoint,
  Bet A B C -> Bet A' B' C'
 -> Lt A B A' B' -> Lt B C B' C' -> Lt A C A' C'.
Proof.
    intros.
    apply bet2_lt2_lt with B' B.
      assumption.
      assumption.
      apply lt_2143. assumption.
      assumption.
Qed.

Lemma bet2_le_lt_lt_13 : forall A B C A' B' C' : Tpoint,
  Bet A B C -> Bet A' B' C'
 -> Le A B A' B' -> Lt B C B' C' -> Lt A C A' C'.
Proof.
    intros.
    apply bet2_le_lt_lt with B' B.
      assumption.
      assumption.
      apply le_2143. assumption.
      assumption.
Qed.

Lemma bet2_lt_le_lt_13 : forall A B C A' B' C' : Tpoint,
  Bet A B C -> Bet A' B' C'
 -> Lt A B A' B' -> Le B C B' C'
 -> Lt A C A' C'.
Proof.
    intros.
    apply bet2_lt_le_lt with B' B.
      assumption.
      assumption.
      apply lt_2143. assumption.
      assumption.
Qed.

Lemma bet2_lt2_lt_23 : forall A B C A' B' C' : Tpoint,
  Bet A B C -> Bet A' B' C'
 -> Lt A B A' B' -> Lt A' C' A C
 -> Lt B' C' B C.
Proof.
    intros.
    apply lt_to_def in H1.
    apply lt_to_def in H2.
    spliter.
    split.
    apply bet2_le2_le_23 with A A'; assumption.
    intro.
    induction(eq_dec_points A B).
    (* A = B *)
      subst B.
      assert(Le B' C' A' C').
        apply bet_le_2313. assumption.
      assert(Le A C A' C').
        apply l5_6 with B' C' A' C'; try assumption.
          apply cong_1212.
      apply H3.
        apply le_anti_symmetry; assumption.
    (* A <> B *)
    apply le_to_def2 in H1.
    exists_and H1 b.
    exists_and H2 c.
    assert(Bet A b c).
      assert (Bet A b c \/ Bet A c b).
        apply l5_4 with B C; assumption.
      assert(Col A b c).
        induction H9.
          apply bet_col_123. assumption.
          apply bet_col_132. assumption.
      assert(Le A' B' A' C').
        apply bet_le_1213. assumption.
      assert(Le A b A c).
        apply l5_6 with A' B' A' C'.
          assumption.
          apply cong_3412. assumption.
          assumption.
      induction H9.
        assumption.
        assert(c = b).
          apply bet_le_eq_reverse with A; assumption.
        subst c. apply between_trivial_122.
    assert(Bet_5 A B b c C).
      apply bet5_bet_2; assumption.
    assert(Cong B' C' b c).
      apply l4_3_1 with A' A; try assumption.
        apply cong_3412. assumption.
    assert(Cong B C b c).
      apply cong_1234_1256 with B' C'; assumption. 
    assert(B=b/\c=C).
      apply bet4_cong_eq.
        apply H10.
        apply cong_3412. assumption.
    spliter.
    subst.
    contradiction.
Qed.

Lemma bet2_le_lt_lt_23 : forall A B C A' B' C' : Tpoint,
  Bet A B C -> Bet A' B' C'
 -> Le A B A' B' -> Lt A' C' A C
 -> Lt B' C' B C.
Proof.
  intros.
  apply lt_to_def in H2.
  spliter.
  split.
    apply bet2_le2_le_23 with A A'; assumption.
  intro.
    induction(eq_dec_points A B).
    (* A = B *)
      subst B.
      assert(Le B' C' A' C').
        apply bet_le_2313. assumption.
      assert(Le A C A' C').
        apply l5_6 with B' C' A' C'; try assumption.
          apply cong_1212.
      apply H3.
        apply le_anti_symmetry; assumption.
   (* A <> B *)
    apply le_to_def2 in H1.
    exists_and H1 b.
    exists_and H2 c.
    assert(Bet A b c).
      assert (Bet A b c \/ Bet A c b).
        apply l5_4 with B C; assumption.
      assert(Col A b c).
        induction H8.
          apply bet_col_123. assumption.
          apply bet_col_132. assumption.
      assert(Le A' B' A' C').
        apply bet_le_1213. assumption.
      assert(Le A b A c).
        apply l5_6 with A' B' A' C'.
          assumption.
          apply cong_3412. assumption.
          assumption.
      induction H8.
        assumption.
        assert(c = b).
          apply bet_le_eq_reverse with A; assumption.
        subst c. apply between_trivial_122.
    assert(Bet_5 A B b c C).
      apply bet5_bet_2; assumption.
    assert(Cong B' C' b c).
      apply l4_3_1 with A' A; try assumption.
        apply cong_3412. assumption.
    assert(Cong B C b c).
      apply cong_1234_1256 with B' C'; assumption. 
    assert(B=b/\c=C).
      apply bet4_cong_eq.
        apply H9.
        apply cong_3412. assumption.
    spliter.
    subst.
    contradiction.
Qed.

Lemma bet2_lt_le_lt_23 : forall A B C A' B' C' : Tpoint,
  Bet A B C -> Bet A' B' C'
 -> Lt A B A' B' -> Le A' C' A C
 -> Lt B' C' B C.
Proof.
  intros.
  apply lt_to_def in H1.
  spliter.
  split.
    apply bet2_le2_le_23 with A A'; assumption.
  intro.
    induction(eq_dec_points A B).
    (* A = B *)
      subst B.
      assert(Le B' C' A' C').
        apply bet_le_2313. assumption.
      assert(Le A C A' C').
        apply l5_6 with B' C' A' C'; try assumption.
          apply cong_1212.
      assert(Cong A C A' C').
        apply le_anti_symmetry; assumption.
      assert(Cong A' C' B' C').
        apply cong_3412.
        apply cong_1234_3456 with A C; assumption.
      assert(A' = B').
        apply between_cong_reverse with C'; assumption.
      subst. apply H3. apply cong_1122.
   (* A <> B *)
    apply le_to_def2 in H1.
    exists_and H1 b.
    exists_and H2 c.
    assert(Bet A b c).
      assert (Bet A b c \/ Bet A c b).
        apply l5_4 with B C; assumption.
      assert(Col A b c).
        induction H8.
          apply bet_col_123. assumption.
          apply bet_col_132. assumption.
      assert(Le A' B' A' C').
        apply bet_le_1213. assumption.
      assert(Le A b A c).
        apply l5_6 with A' B' A' C'.
          assumption.
          apply cong_3412. assumption.
          assumption.
      induction H8.
        assumption.
        assert(c = b).
          apply bet_le_eq_reverse with A; assumption.
        subst c. apply between_trivial_122.
    assert(Bet_5 A B b c C).
      apply bet5_bet_2; assumption.
    assert(Cong B' C' b c).
      apply l4_3_1 with A' A; try assumption.
        apply cong_3412. assumption.
    assert(Cong B C b c).
      apply cong_1234_1256 with B' C'; assumption. 
    assert(B=b/\c=C).
      apply bet4_cong_eq.
        apply H9.
        apply cong_3412. assumption.
    spliter.
    subst.
    contradiction.
Qed.

Lemma bet2_lt2_lt_12 : forall A B C A' B' C',
  Bet A B C -> Bet A' B' C'
  -> Lt B C B' C' -> Lt A' C' A C 
  -> Lt A' B' A B.
Proof.
  intros.
  apply lt_2143.
  apply bet2_lt2_lt_23 with C C'.
    apply between_symmetry; assumption.
    apply between_symmetry; assumption.
    apply lt_2143; assumption.
    apply lt_2143; assumption.
Qed.


Lemma bet2_le_lt_lt_12 : forall A B C A' B' C' : Tpoint,
  Bet A B C -> Bet A' B' C'
 -> Le B C B' C' -> Lt A' C' A C
 -> Lt A' B' A B.
Proof.
  intros.
  apply lt_2143.
  apply bet2_le_lt_lt_23 with C C'.
    apply between_symmetry; assumption.
    apply between_symmetry; assumption.
    apply le_2143; assumption.
    apply lt_2143; assumption.
Qed.

Lemma bet2_lt_le_lt_12 : forall A B C A' B' C' : Tpoint,
  Bet A B C -> Bet A' B' C'
 -> Lt B C B' C' -> Le A' C' A C
 -> Lt A' B' A B.
Proof.
  intros.
  apply lt_2143.
  apply bet2_lt_le_lt_23 with C C'.
    apply between_symmetry; assumption.
    apply between_symmetry; assumption.
    apply lt_2143; assumption.
    apply le_2143; assumption.
Qed.

End Bet_Lt.

Print All.

