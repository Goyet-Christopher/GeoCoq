Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong.

Section T1_3.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma diff_symmetry : forall A B : Tpoint, 
  A<>B -> B<>A.
Proof.
    intros.
    intro.
    apply H.
    symmetry.
    assumption.
Qed.

Lemma cong_diff_12_34 : forall A B C D : Tpoint,
 A <> B -> Cong A B C D -> C <> D.
Proof.
    intros.
    intro.
    subst.
    apply H.
    apply (cong_identity A B D).
    assumption.
Qed.

Lemma cong_diff_21_34 : forall A B C D ,
 B <> A -> Cong A B C D -> C <> D.
Proof.
    intros.
    apply (cong_diff_12_34 A B C D).
    apply diff_symmetry.
    assumption.
    assumption.
Qed.

Lemma cong_diff_12_43 : forall A B C D : Tpoint,
 A <> B -> Cong A B C D -> D <> C.
Proof.
    intros.
    apply diff_symmetry.
    apply cong_diff_12_34 with A B;
    assumption.
Qed.

Lemma cong_diff_21_43 : forall A B C D ,
 B <> A -> Cong A B C D -> D <> C.
Proof.
    intros.
    apply diff_symmetry.
    apply cong_diff_21_34 with A B;
    assumption.
Qed.

Lemma cong_diff_34_12 : forall A B C D ,
 C <> D -> Cong A B C D -> A <> B.
Proof.
    intros.
    apply cong_diff_12_34 with C D.
    assumption.
    apply cong_symmetry.
    assumption.
Qed.

Lemma cong_diff_43_12 : forall A B C D ,
 D <> C -> Cong A B C D -> A <> B.
Proof.
    intros.
    apply cong_diff_34_12 with C D.
    apply diff_symmetry.
    assumption.
    assumption.
Qed.

Lemma cong_diff_34_21 : forall A B C D ,
 C <> D -> Cong A B C D -> B <> A.
Proof.
    intros.
    apply cong_diff_34_12 with C D.
    assumption.
    apply cong_2134.
    assumption.
Qed.

Lemma cong_diff_43_21 : forall A B C D ,
 D <> C -> Cong A B C D -> B <> A.
Proof.
    intros.
    apply cong_diff_43_12 with C D.
    assumption.
    apply cong_2134.
    assumption.
Qed.

Lemma cong_diff_23 : forall A B C,
  B<>C -> Cong A B A C -> A<>B /\ A<>C.
Proof.
  intros.
    split.
    intro.
      subst.
      apply H.
      apply cong_identity with B.
      apply cong_3412.
      assumption.
    intro.
      subst.
      apply H.
      apply cong_identity with C.
      apply cong_2134.
      assumption.
Qed.

Lemma cong_diff_12 : forall A B C,
  A<>B -> Cong A C B C -> A<>C /\ B<>C.
Proof.
    intros.
    split.
      intro.
      subst.
      apply H.
      apply cong_identity with C.
      apply cong_4312; assumption.
    intro.
      subst.
      apply H.
      apply cong_identity with C.
      assumption.
Qed.

Lemma cong_diff_14 : forall A B C,
  A<>C -> Cong A B B C -> A<>B /\ B<>C.
Proof.
    intros.
    split.
      apply cong_diff_12 with C.
        apply diff_symmetry; assumption.
        apply cong_4312; assumption.
      apply cong_diff_23 with A.
        assumption.
        apply cong_2134; assumption.
Qed.

End T1_3.

Print All.