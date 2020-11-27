Require Export GeoCoq.Tarski_dev.Ch02_cong.cong3.Ch02_cong3.

Section Cong3_transitivity.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong3_transitivity_1X_X2 : forall A1 B1 C1 X Y Z A2 B2 C2,
 Cong_3 A1 B1 C1 X Y Z -> Cong_3 X Y Z A2 B2 C2 -> Cong_3 A1 B1 C1 A2 B2 C2.
Proof.
    intros.
    apply cong3_to_def in H.
    apply cong3_to_def in H0.
    spliter.
    repeat split.
    apply cong_12XY_XY34 with X Y; assumption.
    apply cong_12XY_XY34 with X Z; assumption.
    apply cong_12XY_XY34 with Y Z; assumption.
Qed.

Lemma cong3_transitivity_X1_X2 : forall A1 B1 C1 X Y Z A2 B2 C2,
 Cong_3 X Y Z A1 B1 C1 -> Cong_3 X Y Z A2 B2 C2 -> Cong_3 A1 B1 C1 A2 B2 C2.
Proof.
    intros.
    apply cong3_symmetry in H.
    apply cong3_transitivity_1X_X2 with X Y Z;
    assumption.
Qed.

Lemma cong3_transitivity_1X_2X : forall A1 B1 C1 X Y Z A2 B2 C2,
 Cong_3 A1 B1 C1 X Y Z -> Cong_3 A2 B2 C2 X Y Z -> Cong_3 A1 B1 C1 A2 B2 C2.
Proof.
    intros.
    apply cong3_symmetry in H0.
    apply cong3_transitivity_1X_X2 with X Y Z;
    assumption.
Qed.

Lemma cong3_transitivity_X1_2X : forall A1 B1 C1 X Y Z A2 B2 C2,
 Cong_3 X Y Z A1 B1 C1 -> Cong_3 A2 B2 C2 X Y Z -> Cong_3 A1 B1 C1 A2 B2 C2.
Proof.
    intros.
    apply cong3_symmetry in H0.
    apply cong3_transitivity_X1_X2 with X Y Z;
    assumption.
Qed.

End Cong3_transitivity.

Print All.

