Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_perpat.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_col.

Section Perp_perp.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perp_per : forall A B C D,
  Perp A B C D -> exists X, Per A X C.
Proof.
    intros.
    apply perp_to_def in H.
    exists_and H X.
    exists X.
    apply perpat_per_13 with B D.
      assumption.
Qed.

Lemma perp_per_14 : forall A B C,
  Perp A B C A -> Per B A C.
Proof.
    intros.
    assert (Perp_at A B A A C).
      apply perp_perpat_23.
      apply perp_2143.
      assumption.
    apply perpat_per_14 with A A.
    assumption.
Qed.

Lemma perp_per_13 : forall A B C,
 Perp A B A C -> Per B A C.
Proof.
    intros.
    apply perp_per_14.
    apply perp_1243.
      assumption.
Qed.

Lemma perp_per_23 : forall A B C,
 Perp B A A C -> Per B A C.
Proof.
    intros.
    apply perp_per_14.
    apply perp_2143. assumption.
Qed.

Lemma perp_per_24 : forall A B C,
 Perp B A C A -> Per B A C.
Proof.
    intros.
    apply perp_per_14.
    apply perp_2134. assumption.
Qed.

Lemma per_perp : forall A B C,
 A <> B -> B <> C -> Per A B C -> Perp A B B C.
Proof.
    intros.
      apply perpat_perp with B.
      apply per_perpat; assumption.
Qed.

Lemma col_per_perp_sym : forall A B C D,
 A <> B -> B <> C -> D <> B -> D <> C
 -> Col B C D -> Per A B C -> Perp C D A B.
Proof.
    intros.
    assert(Perp A B B C).
      apply per_perp; assumption.
    apply perp_symmetry.
    apply perp_col_34 with B C; try assumption.
      apply not_eq_sym. assumption.
      apply col_trivial_122.
Qed.

Lemma l8_16_1 : forall A B C U X,
  A<>B -> Col A B X -> Col A B U
 -> U<>X -> Perp A B C X
 -> ~ Col A B C /\ Per C X U.
Proof.
    intros.
    split.
      intro.
      assert (Perp_at X A B C X).
        eapply l8_15_1; assumption.
      assert (X = U).
        eapply l8_14_2_1b.
          apply H5.
          apply col_312. assumption.
        apply col_transitivity_3 with A B; assumption.
      apply not_eq_sym in H2.
      contradiction.
    apply l8_14_2_1b_bis with C X U X; try apply col_trivial_121; try apply col_trivial_112.
    apply perp_3412.
    eapply perp_col_12 with A B; assumption.
Qed.

Lemma l8_16_2 : forall A B C U X,
  A<>B -> Col A B X -> Col A B U 
-> U<>X -> ~ Col A B C -> Per C X U -> Perp A B C X.
Proof.
    intros.
    assert (C <> X).
      apply not_eq_sym.
    apply col_not_col_diff with A B; assumption.
    apply perpat_perp with X.
    apply l8_13_2 with U C; try assumption.
      apply col_312. assumption.
      apply col_trivial_121.
      apply col_312. assumption.
      apply col_trivial_112.
      apply per_symmetry. assumption.
Qed.

Lemma l8_16_equiv : forall A B C U X,
  A<>B -> Col A B X -> Col A B U 
-> U<>X -> (~ Col A B C /\ Per C X U <-> Perp A B C X).
Proof.
    intros.
    split.
      intro.
      spliter.
      apply l8_16_2 with U; assumption.
    intro.
    apply l8_16_1; assumption.
Qed.

End Perp_perp.

Print All.