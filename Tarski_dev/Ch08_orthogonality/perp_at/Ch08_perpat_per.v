Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_col.

Section Perpat_per.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(*
Lemma perpat_per : forall A B C,
 Perp_at B A B B C-> Per A B C.
Proof.
    intros.
    apply perpat_to_def in H.
    spliter.
    apply H3.
      apply col_trivial_112.
      apply col_trivial_121.
Qed.
*)

Lemma perpat_per_13 : forall A B C D X,
 Perp_at X A B C D-> Per A X C.
Proof.
    intros.
    apply perpat_to_def in H.
    spliter.
    apply H3.
      apply col_trivial_112.
      apply col_trivial_112.
Qed.

Lemma perpat_per_14 : forall A B C D X,
 Perp_at X A B C D-> Per A X D.
Proof.
    intros.
    apply perpat_to_def in H.
    spliter.
    apply H3.
      apply col_trivial_112.
      apply col_trivial_121.
Qed.

Lemma perpat_per_23 : forall A B C D X,
 Perp_at X A B C D-> Per B X C.
Proof.
    intros.
    apply perpat_to_def in H.
    spliter.
    apply H3.
      apply col_trivial_121.
      apply col_trivial_112.
Qed.

Lemma perpat_per_24 : forall A B C D X,
 Perp_at X A B C D-> Per B X D.
Proof.
    intros.
    apply perpat_to_def in H.
    spliter.
    apply H3.
      apply col_trivial_121.
      apply col_trivial_121.
Qed.

Lemma not_per_not_perpat_13 : forall A B C D X,
 ~ Per A X C -> ~ Perp_at X A B C D.
Proof.
    intros.
    intro.
    apply H.
    apply perpat_per_13 with B D.
    assumption.
Qed.

Lemma not_per_not_perpat_14 : forall A B C D X,
 ~ Per A X D -> ~ Perp_at X A B C D.
Proof.
    intros.
    intro.
    apply H.
    apply perpat_per_14 with B C.
    assumption.
Qed.

Lemma not_per_not_perpat_23 : forall A B C D X,
 ~ Per B X C -> ~ Perp_at X A B C D.
Proof.
    intros.
    intro.
    apply H.
    apply perpat_per_23 with A D.
    assumption.
Qed.

Lemma not_per_not_perpat_24 : forall A B C D X,
 ~ Per B X D -> ~ Perp_at X A B C D.
Proof.
    intros.
    intro.
    apply H.
    apply perpat_per_24 with A C.
    assumption.
Qed.

Lemma per_perpat : forall A B C,
 A <> B -> B <> C -> Per A B C -> Perp_at B A B B C.
Proof.
    intros.
    apply def_to_perpat; try assumption.
      apply col_trivial_121.
      apply col_trivial_112.
    intros.
    apply per_col_13 with A C; try assumption.
      apply col_132. assumption.
Qed.

Lemma l8_13 : forall A B C D X,
  A <> B -> A <> X -> C <> D -> C <> X
  -> Col X A B -> Col X C D -> Per A X C -> Perp_at X A B C D.
Proof.
    intros.
    apply l8_13_2 with A C; try assumption.
      apply col_trivial_112.
      apply col_trivial_112.
Qed.

End Perpat_per.

Print All.