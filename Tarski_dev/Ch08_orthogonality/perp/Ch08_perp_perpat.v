Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_diff.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_eq.

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


Lemma perp_perpat : forall A B C,
  Perp A B C A -> Perp_at A A B C A.
Proof.
    intros.
    apply l8_15_1.
      apply perp_not_eq_1 with C A. assumption.
      apply col_trivial_121.
      assumption.
Qed.


Lemma l8_14_2_2 : forall X A B C D,
 Perp A B C D -> (forall Y, Col Y A B -> Col Y C D -> X=Y)
 ->  Perp_at X A B C D.
Proof.
    intros.
    assert(H' := H).
      exists_and H Y.
      apply perpat_to_def in H1.
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
    exists X.
    unfold Perp_at in *.
    spliter.
    repeat split; try assumption.
      apply diff_symmetry. assumption.
      apply col_trivial_121.
    intros.
    apply H4.
      apply col_213.
      apply col_transitivity_2 with X; try assumption.
        apply col_321. assumption.
    assumption.
Qed.

End Perp_perpat.

Print All.
