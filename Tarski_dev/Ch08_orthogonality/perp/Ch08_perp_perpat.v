Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp.

Section Perp_perpat.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perpat_perp : forall A B C D X,
 Perp_at X A B C D -> Perp A B C D.
Proof.
    intros.
    exists X.
    assumption.
Qed.

Lemma l8_14_2_1b_bis : forall A B C D X,
 Perp A B C D -> Col X A B -> Col X C D
 -> Perp_at X A B C D.
Proof.
    intros.
    exists_and H Y.
    assert (Y = X).
      apply l8_14_2_1b with A B C D; assumption.
    subst Y.
    assumption.
Qed.

Lemma l8_15_1 : forall A B C X,
 A<>B -> Col A B X -> Perp A B C X -> Perp_at X A B C X.
Proof.
    intros.
    apply l8_14_2_1b_bis.
      assumption.
      apply col_312. assumption.
      apply col_trivial_121.
Qed.

Lemma l8_15_2 : forall A B C X,
 A<>B -> Col A B X ->  Perp_at X A B C X -> Perp A B C X.
Proof.
    intros.
    apply perpat_perp with X.
    assumption.
Qed.


Lemma perp_perpat_14 : forall X B C,
  Perp X B C X -> Perp_at X X B C X.
Proof.
    intros.
    apply l8_15_1.
      exists_and H A.
        apply perpat_diff_12 with A C X.
        assumption.
      apply col_trivial_121.
      assumption.
Qed.

Lemma perp_perpat_13 : forall X B D,
  Perp X B X D -> Perp_at X X B X D.
Proof.
    intros.
    apply perpat_1243.
    apply perp_perpat_14.
    apply perp_1243.
      assumption.
Qed.

Lemma perp_perpat_23 : forall X A D,
  Perp A X X D -> Perp_at X A X X D.
Proof.
    intros.
    apply perpat_2134.
    apply perp_perpat_13.
    apply perp_2134.
      assumption.
Qed.

Lemma perp_perpat_24 : forall X A C,
  Perp A X C X -> Perp_at X A X C X.
Proof.
    intros.
    apply perpat_2143.
    apply perp_perpat_13.
    apply perp_2143.
      assumption.
Qed.


Lemma l8_14_2_2 : forall X A B C D,
 Perp A B C D -> (forall Y, Col Y A B -> Col Y C D -> X=Y)
 ->  Perp_at X A B C D.
Proof.
    intros.
    assert(H' := H).
      apply perp_to_def in H'.
      exists_and H' Y.
    assert(Col Y A B /\ Col Y C D).
      apply perpat_col. assumption.
      spliter.
    assert(X=Y).
      apply H0; assumption.
    subst Y.
    apply l8_14_2_1b_bis; assumption.
Qed.


Lemma perpat_perp_bis : forall A B C D X,
 Perp_at X A B C D -> Perp X B C D \/ Perp A X C D.
Proof.
    intros.
    induction (eq_dec_points X A).
      subst X.
      left. apply perpat_perp with A. assumption.
    right.
    apply perpat_perp with X.
    apply perpat_inter_2 with B.
      assumption.
      apply not_eq_sym. assumption.
Qed.

End Perp_perpat.

Print All.
