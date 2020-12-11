Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_diff.

Section Perp_col.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perp_col_4 : forall A B C D X,
 C <> X -> Perp A B C D -> Col C D X -> Perp A B C X.
Proof.
    intros.
    assert (T:=perp_distinct A B C D H0).
    spliter.
    exists_and H0 P.
    exists P.
    apply perpat_col_perpat_4 with D; assumption.
Qed.

Lemma perp_col_2 : forall A B C D X,
 A<>X -> Perp A B C D -> Col A B X -> Perp A X C D.
Proof.
    intros.
    apply perp_symmetry.
    apply perp_col_4 with B; try assumption.
    apply perp_symmetry. assumption.
Qed.

Lemma perp_col_3 : forall A B C D X,
 D <> X -> Perp A B C D -> Col C D X -> Perp A B X D.
Proof.
    intros.
    assert (T:=perp_distinct A B C D H0).
    spliter.
    exists_and H0 P.
    exists P.
    apply perpat_col_perpat_3 with C; assumption.
Qed.

Lemma perp_col_1 : forall A B C D X,
 B<>X -> Perp A B C D -> Col A B X -> Perp X B C D.
Proof.
    intros.
    apply perp_symmetry.
    apply perp_col_3 with A; try assumption.
    apply perp_symmetry. assumption.
Qed.

Lemma perp_col_12 : forall A B C D X Y,
 Perp A B C D -> X <> Y -> Col A B X -> Col A B Y
 -> Perp X Y C D.
Proof.
    intros.
    exists_and H P.
    exists P.
    apply perpat_col_perpat_12 with A B; assumption.
Qed.

Lemma perp_col_34 : forall A B C D X Y,
 Perp A B C D -> X <> Y -> Col C D X -> Col C D Y
 -> Perp A B X Y.
Proof.
    intros.
    apply perp_symmetry.
    apply perp_col_12 with C D; try assumption.
    apply perp_symmetry. assumption.
Qed.

Lemma perp_col_1234 : forall A B C D U V X Y,
 Perp A B C D -> U <> V -> Col A B U -> Col A B V
 -> X <> Y -> Col C D X -> Col C D Y
 -> Perp U V X Y.
Proof.
    intros.
    apply perp_col_12 with A B; try assumption.
    apply perp_col_34 with C D; assumption.
Qed.


End Perp_col.

Print All.


