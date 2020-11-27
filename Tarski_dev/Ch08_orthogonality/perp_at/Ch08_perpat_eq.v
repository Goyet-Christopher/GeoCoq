Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per_eq.

Section Perpat_equalities.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l8_14_2_1b : forall X A B C D Y,
  Perp_at X A B C D -> Col Y A B -> Col Y C D -> X=Y.
Proof.
    intros.
    assert(forall U V, Col U A B -> Col V C D -> Per U X V).
      apply perpat_forall. assumption.
    apply eq_sym, per_identity.
    apply H2; assumption.
Qed.

Lemma l8_14_3 : forall A B C D X Y,
 Perp_at X A B C D -> Perp_at Y A B C D -> X=Y.
Proof.
    intros.
    assert( Col Y A B /\ Col Y C D).
      apply perpat_col. assumption.
      spliter.
    apply l8_14_2_1b with A B C D; assumption.
Qed.

Lemma perpat_identity : forall A B C X,
  Perp_at X A B C A -> X = A.
Proof.
    intros.
    spliter.
    assert(forall U V, Col U A B -> Col V C A -> Per U X V).
      apply perpat_forall. assumption.
    assert( Col X A B /\ Col X C A).
      apply perpat_col. assumption.
    spliter.
    apply per_equality_2 with A.
      apply H0.
      apply col_trivial_112.
      apply col_trivial_121.
    apply per_trivial_112.
Qed.

End Perpat_equalities.

Print All.
