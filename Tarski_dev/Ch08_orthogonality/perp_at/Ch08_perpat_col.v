Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat.

Section Perpat_col.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perpat_col_perpat_4 : forall A B C D X P,
  C <> X -> Col C D X -> Perp_at P A B C D
 -> Perp_at P A B C X.
Proof.
    intros.
    apply perpat_to_def in H1.
    spliter.
    repeat split; try assumption.
      apply col_213.
      apply col_transitivity_1 with D; try assumption.
        apply col_231. assumption.
    intros.
    apply H5.
      assumption.
      apply col_312.
      apply col_transitivity_1 with X.
        assumption.
        apply col_132. assumption.
        apply col_231. assumption.
Qed.

Lemma perpat_col_perpat_3 : forall A B C D X P,
  D <> X -> Col C D X -> Perp_at P A B C D
 -> Perp_at P A B X D.
Proof.
    intros.
    apply perpat_1243.
    apply perpat_col_perpat_4 with C.
      assumption.
      apply col_213. assumption.
      apply perpat_1243. assumption.
Qed.

Lemma perpat_col_perpat_34 : forall A B C D X Y P,
  X <> Y -> Col C D X -> Col C D Y
-> Perp_at P A B C D -> Perp_at P A B X Y.
Proof.
    intros.
    assert(A <> B /\ C <> D).
      apply perpat_diff_1234 with P. assumption.
    assert(Col P A B /\ Col P C D).
      apply perpat_col. assumption.
    spliter.
    assert(Col P X Y).
      apply col_transitivity_3 with C D; try assumption.
        apply col_231. assumption.
    assert(forall U V, Col U A B -> Col V C D -> Per U P V).
      apply perpat_forall. assumption.
    apply def_to_perpat; try assumption.
    intros.
    apply H8.
      assumption.
      apply col_transitivity_3 with X Y.
        assumption.
        apply col_231. assumption.
        apply col_231. apply col_transitivity_1 with D; assumption.
        apply col_231. apply col_transitivity_1 with C.
          apply not_eq_sym. assumption.
          apply col_213. assumption.
          apply col_213. assumption.
Qed.

Lemma perpat_col_perpat_1 : forall A B C D X P,
  B <> X -> Col A B X -> Perp_at P A B C D
 -> Perp_at P X B C D.
Proof.
    intros.
    apply perpat_3412.
    apply perpat_col_perpat_3 with A.
      assumption. assumption.
      apply perpat_3412. assumption.
Qed.

Lemma perpat_col_perpat_2 : forall A B C D X P,
  A <> X -> Col A B X -> Perp_at P A B C D
 -> Perp_at P A X C D.
Proof.
    intros.
    apply perpat_3412.
    apply perpat_col_perpat_4 with B.
      assumption. assumption.
      apply perpat_3412. assumption.
Qed.

Lemma perpat_col_perpat_12 : forall A B C D X Y P,
  X <> Y  -> Col A B X -> Col A B Y
 -> Perp_at P A B C D -> Perp_at P X Y C D.
Proof.
    intros.
    apply perpat_3412.
    apply perpat_col_perpat_34 with A B; try assumption.
      apply perpat_3412. assumption.
Qed.

Lemma perpat_col_perpat_1234 : forall A B C D U V X Y P,
  U <> V -> X <> Y
 -> Col A B U -> Col A B V -> Col C D X -> Col C D Y
 -> Perp_at P A B C D -> Perp_at P U V X Y.
Proof.
    intros.
    apply perpat_col_perpat_12 with A B; try assumption.
    apply perpat_col_perpat_34 with C D; assumption.
Qed.

Lemma perpat_or_col : forall A B C D X,
  A<>B -> Col A B X -> Perp_at X A X C D \/ Perp_at X X B C D
 -> Perp_at X A B C D.
Proof.
    intros.
    induction H1.
      apply perpat_col_perpat_2 with X; try assumption.
        apply col_132. assumption.
      apply perpat_col_perpat_1 with X.
        apply not_eq_sym. assumption.
        apply col_321. assumption.
        assumption.
Qed.

Lemma perpat_inter_1 : forall X A B C D,
  Perp_at X A B C D -> B <> X -> Perp_at X X B C D.
Proof.
    intros.
    assert(Col X A B /\ Col X C D).
      apply perpat_col. assumption. spliter.
    apply perpat_col_perpat_1 with A; try assumption.
      apply col_231. assumption.
Qed.

Lemma perpat_inter_2 : forall X A B C D,
  Perp_at X A B C D -> A <> X -> Perp_at X A X C D.
Proof.
    intros.
    assert(Col X A B /\ Col X C D).
      apply perpat_col. assumption. spliter.
    apply perpat_col_perpat_2 with B; try assumption.
      apply col_231. assumption.
Qed.

Lemma perpat_inter_3 : forall X A B C D,
  Perp_at X A B C D -> D <> X -> Perp_at X A B X D.
Proof.
    intros.
    assert(Col X A B /\ Col X C D).
      apply perpat_col. assumption. spliter.
    apply perpat_col_perpat_3 with C; try assumption.
      apply col_231. assumption.
Qed.

Lemma perpat_inter_4 : forall X A B C D,
  Perp_at X A B C D -> C <> X -> Perp_at X A B C X.
Proof.
    intros.
    assert(Col X A B /\ Col X C D).
      apply perpat_col. assumption. spliter.
    apply perpat_col_perpat_4 with D; try assumption.
      apply col_231. assumption.
Qed.

Lemma l8_13_2_exists : forall A B C D X,
   A <> B -> C <> D -> Col X A B -> Col X C D ->
  (exists U, exists V :Tpoint, Col U A B /\ Col V C D /\ U<>X /\ V<>X /\ Per U X V) ->
  Perp_at X A B C D.
Proof.
    intros.
    exists_and H3 U.
    exists_and H4 V.
    apply def_to_perpat; try assumption.
    intros.
    assert(Col U0 U X).
      apply col_transitivity_3 with A B;
        try apply col_231; assumption.
    assert(Col V0 V X).
      apply col_transitivity_3 with C D;
        try apply col_231; assumption.
    apply per_col_13 with U V; try assumption.
      apply not_eq_sym. assumption.
Qed.

Lemma l8_13_2 : forall A B C D X U V,
   A <> B -> C <> D -> Col X A B -> Col X C D ->
  Col U A B -> Col V C D -> U<>X -> V<>X -> Per U X V ->
  Perp_at X A B C D.
Proof.
    intros.
    apply l8_13_2_exists; try assumption.
    exists U.
    exists V.
    repeat split; assumption.
Qed.


End Perpat_col.

Print All.
