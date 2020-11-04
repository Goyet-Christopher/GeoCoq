Require Export GeoCoq.Tarski_dev.Ch05_bet_le.Ch05_ge.

Section Gt_prop.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma gt_left_comm : forall A B C D, Gt A B C D -> Gt B A C D.
Proof.
    intros.
    unfold Gt in *.
    apply lt_right_comm.
    assumption.
Qed.

Lemma gt_right_comm : forall A B C D, Gt A B C D -> Gt A B D C.
Proof.
    intros.
    unfold Gt in *.
    apply lt_left_comm.
    assumption.
Qed.

Lemma gt_comm : forall A B C D, Gt A B C D -> Gt B A D C.
Proof.
    intros.
    apply gt_left_comm.
    apply gt_right_comm.
    assumption.
Qed.

End Gt_prop.