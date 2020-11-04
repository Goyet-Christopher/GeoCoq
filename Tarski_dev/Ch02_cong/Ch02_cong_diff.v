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

End T1_3.

Print All.