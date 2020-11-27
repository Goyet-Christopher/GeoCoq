Require Export GeoCoq.Tarski_dev.Ch02_cong.cong3.Ch02_cong3.
Require Export GeoCoq.Tarski_dev.Ch02_cong.cong3.Ch02_cong3_cong.

Section Cong3_eq.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong3_identity_12 : forall A B C A' C',
Cong_3 A B C A' A' C' -> A=B.
Proof.
    intros.
    apply cong_identity with A'.
    apply cong3_1245 with C C'.
    assumption.
Qed.

Lemma cong3_identity_13 : forall A B C A' B',
Cong_3 A B C A' B' A' -> A=C.
Proof.
    intros.
    apply cong3_identity_12 with B A' B'.
    apply cong3_swap_132.
    assumption.
Qed.

Lemma cong3_identity_23 : forall A B C A' B',
Cong_3 A B C A' B' B' -> B=C.
Proof.
    intros.
    apply cong_identity with B'.
    apply cong3_2356 with A A'.
    assumption.
Qed.

End Cong3_eq.

Print All.