Require Export GeoCoq.Tarski_dev.Ch05_le_lt_ge_gt.Ch05_le.

Section Ge_prop.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma ge_to_def : forall A B C D,
  Ge A B C D -> Le C D A B.
Proof.
    intros.
    assumption.
Qed.

Lemma def_to_ge : forall A B C D,
  Le C D A B -> Ge A B C D.
Proof.
    intros.
    assumption.
Qed.


Lemma ge_left_comm : forall A B C D,
  Ge A B C D -> Ge B A C D.
Proof.
    intros.
    apply def_to_ge.
    apply le_1243.
    assumption.
Qed.

Definition ge_2134 A B C D := ge_left_comm A B C D.

Lemma ge_right_comm : forall A B C D,
  Ge A B C D -> Ge A B D C.
Proof.
    intros.
    apply def_to_ge.
    apply le_2134.
    assumption.
Qed.

Definition ge_1243 A B C D := ge_right_comm A B C D.

Lemma ge_comm :  forall A B C D, Ge A B C D -> Ge B A D C.
Proof.
    intros.
    apply ge_left_comm.
    apply ge_right_comm.
    assumption.
Qed.

Definition ge_2143 A B C D := ge_comm A B C D.


End Ge_prop.

Print All.

