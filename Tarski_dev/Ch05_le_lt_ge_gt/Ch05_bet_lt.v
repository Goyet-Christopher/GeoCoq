Require Export GeoCoq.Tarski_dev.Ch05_le_lt_ge_gt.Ch05_lt.
Require Export GeoCoq.Tarski_dev.Ch05_le_lt_ge_gt.Ch05_bet_cong_eq.

Section Bet_Lt.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet2_lt_13: forall O o A B a b,
Bet a o b -> Bet A O B
 -> Le o a O A -> Le o b O B -> Cong a b A B
 -> Cong o b O B.
Proof.
    intros.
    assert(exists a' b', Bet_4 A a' b' B /\ Le a' b' A B /\ Cong a b a' b' /\ Cong o b O b').
      apply bet2_le_13_exists; assumption.
    exists_and H4 a'.
    exists_and H5 b'.
    assert(Cong a' b' A B).
      apply cong_transitivity with a b.
        apply cong_3412; assumption.
        assumption.
    assert(A=a'/\b'=B).
      apply bet4_cong_eq; assumption.
    spliter.
    subst b'.
    assumption.
Qed.

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
    assert(Cong o b O B).
      apply bet2_lt_13 with A a; assumption.
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
    assert(Cong o b O B).
    apply bet2_lt_13 with A a; assumption.
    contradiction.
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

Lemma bet2_lt_23 : forall A B C A' B' C',
  Bet A B C -> Bet A' B' C'
  -> Le A B A' B' -> Le A' C' A C -> Cong B' C' B C
  -> Cong A B A' B' /\ Cong A' C' A C.
Proof.
    intros.
    induction(eq_dec_points A B).
    (* A = B *)
      subst B.
      assert(Le A' C' B' C').
        eapply l5_6 with A' C' A C.
          assumption.
          apply cong_1212.
          apply cong_3412. assumption.
      assert(A'=B').
        apply bet_le_eq with C'; assumption.
      subst B'.
      split.
        apply cong_1122.
        assumption.
    (* A<>B *)
    assert(exists b c : Tpoint, Bet_5 A B b c C /\
       Cong A b A' B' /\ Cong A' C' A c).
      apply bet2_le_23_exists; assumption.
    exists_and H5 b.
    exists_and H6 c.
    assert(Cong B' C' b c).
      apply l4_3_1 with A' A; try assumption.
        apply H5.
        apply cong_3412. assumption.
    assert(Cong B C b c).
      apply cong_1234_1256 with B' C'; assumption. 
    assert(B=b/\c=C).
      apply bet4_cong_eq.
        apply H5.
        apply cong_3412. assumption.
    spliter.
    subst b. subst c.
    split; assumption.
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
    assert(Cong A B A' B').
      apply (bet2_lt_23 A B C A' B' C'); assumption.
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
    assert(Cong A' C' A C).
      apply (bet2_lt_23 A B C A' B' C'); assumption.
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
    assert(Cong A B A' B').
      apply (bet2_lt_23 A B C A' B' C'); assumption.
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

