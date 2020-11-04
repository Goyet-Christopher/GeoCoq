Require Export GeoCoq.Tarski_dev.Ch05_bet_le.Ch05_le.

Section Ge_prop.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma ge_left_comm : forall A B C D, Ge A B C D -> Ge B A C D.
Proof.
    intros.
    unfold Ge in *.
    apply le_right_comm.
    assumption.
Qed.

Lemma ge_right_comm : forall A B C D, Ge A B C D -> Ge A B D C.
Proof.
    intros.
    unfold Ge in *.
    apply le_left_comm.
    assumption.
Qed.

Lemma ge_comm :  forall A B C D, Ge A B C D -> Ge B A D C.
Proof.
    intros.
    apply ge_left_comm.
    apply ge_right_comm.
    assumption.
Qed.


End Ge_prop.