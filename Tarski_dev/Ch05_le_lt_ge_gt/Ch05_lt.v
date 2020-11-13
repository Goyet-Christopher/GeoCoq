Require Export GeoCoq.Tarski_dev.Ch05_le_lt_ge_gt.Ch05_le.
Require Export GeoCoq.Tarski_dev.Ch05_le_lt_ge_gt.Ch05_bet_le.

Section Lt_prop.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma lt_to_def : forall A B C D,
  Lt A B C D ->  Le A B C D /\ ~ Cong A B C D.
Proof.
    intros.
    assumption.
Qed.

Lemma def_to_lt : forall A B C D,
  Le A B C D /\ ~ Cong A B C D -> Lt A B C D.
Proof.
    intros.
    assumption.
Qed.

Lemma lt_le : forall A B C D,
  Lt A B C D -> Le A B C D.
Proof.
    intros.
    apply H.
Qed.

Lemma lt_ncong : forall A B C D,
  Lt A B C D -> ~ Cong A B C D.
Proof.
    intros.
    apply H.
Qed.

Lemma lt_diff : forall A B C D,
  Lt A B C D -> C <> D.
Proof.
    intros.
    intro.
    subst D.
    assert (A = B).
      apply le_zero with C.
      apply lt_le; assumption.
    subst B.
    apply H.
    apply cong_1122.
Qed.

Lemma lt_1123 : forall A B C,
  B<>C -> Lt A A B C.
Proof.
    intros.
    split.
    apply le_trivial.
    intro.
    assert(B=C).
      apply cong_reverse_identity with A; assumption.
    subst.
    apply H.
    apply eq_refl.
Qed.


Lemma lt_right_comm : forall A B C D,
  Lt A B C D -> Lt A B D C.
Proof.
    intros.
    split.
      apply le_1243.
      apply lt_le; assumption.
    intro.
    apply H.
    apply cong_right_commutativity.
    assumption.
Qed.

Definition lt_1243 A B C D := 
  lt_right_comm A B C D.


Lemma lt_left_comm : forall A B C D,
  Lt A B C D -> Lt B A C D.
Proof.
    intros.
    split.
      apply le_2134.
      apply lt_le; assumption.
    intro.
    apply H.
    apply cong_left_commutativity.
    assumption.
Qed.

Definition lt_2134 A B C D := 
  lt_right_comm A B C D.

Lemma lt_comm : forall A B  C D,
  Lt A B C D -> Lt B A D C.
Proof.
    intros.
    apply lt_left_comm.
    apply lt_right_comm.
    assumption.
Qed.

Definition lt_2143 A B C D :=
  lt_comm A B C D.

Lemma cong2_lt__lt : forall A B C D A' B' C' D',
  Lt A B C D -> Cong A B A' B' -> Cong C D C' D' -> Lt A' B' C' D'.
Proof.
    intros.
    destruct H.
    split.
    apply (l5_6 A B C D); assumption.
    intro.
    apply H2.
    apply cong_transitivity with A' B'.
      assumption.
      apply cong_transitivity with C' D'.
      assumption.
      apply cong_3412; assumption.
Qed.

Lemma bet_lt_1213 : forall A B C, 
  B <> C -> Bet A B C -> Lt A B A C.
Proof.
    intros.
    split.
      apply bet_le_1213.
        assumption.
    intro.
    apply H.
    apply between_cong with A; assumption.
Qed.

Lemma bet_lt_2313 : forall A B C, 
  A <> B -> Bet A B C -> Lt B C A C.
Proof.
    intros.
    apply lt_2143.
    apply bet_lt_1213.
    apply diff_symmetry; assumption.
    apply between_symmetry; assumption.
Qed.

Lemma le1234_lt__lt : forall A B C D E F,
  Le A B C D -> Lt C D E F -> Lt A B E F.
Proof.
    intros.
    split.
      apply le_transitivity with C D.
        assumption.
        apply lt_le; assumption.
    intro.
    apply H0.
    apply le_anti_symmetry.
      apply lt_le; assumption.
    apply (l5_6 A B C D).
      assumption. assumption. 
      apply cong_1212.
Qed.

Lemma le3456_lt__lt : forall A B C D E F,
  Lt A B C D -> Le C D E F -> Lt A B E F.
Proof.
    intros.
    split.
      apply le_transitivity with C D.
        apply lt_le; assumption.
        assumption.
    intro.
    apply H.
    apply le_anti_symmetry.
      apply lt_le; assumption.
      apply (l5_6 C D E F).
        assumption.
        apply cong_1212.
        apply cong_3412; assumption.
Qed.

Lemma lt_transitivity : forall A B C D E F,
  Lt A B C D -> Lt C D E F -> Lt A B E F.
Proof.
    intros.
    apply le1234_lt__lt with C D.
      apply lt_le; assumption.
      assumption.
Qed.


End Lt_prop.

Print All.
