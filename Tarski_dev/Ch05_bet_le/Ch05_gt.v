Require Export GeoCoq.Tarski_dev.Ch05_bet_le.Ch05_ge.
Require Export GeoCoq.Tarski_dev.Ch05_bet_le.Ch05_lt.

Section Gt_prop.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma gt_to_def : forall A B C D,
  Gt A B C D -> Lt C D A B.
Proof.
    intros.
    assumption.
Qed.

Lemma def_to_gt : forall A B C D,
  Lt C D A B -> Gt A B C D.
Proof.
    intros.
    assumption.
Qed.

Lemma gt_left_comm : forall A B C D,
  Gt A B C D -> Gt B A C D.
Proof.
    intros.
    apply def_to_gt.
    apply lt_right_comm.
    assumption.
Qed.

Definition gt_2134 A B C D := gt_left_comm A B C D.

Lemma gt_right_comm : forall A B C D,
  Gt A B C D -> Gt A B D C.
Proof.
    intros.
    apply def_to_gt.
    apply lt_left_comm.
    assumption.
Qed.

Definition gt_1243 A B C D := gt_right_comm A B C D.

Lemma gt_comm : forall A B C D,
  Gt A B C D -> Gt B A D C.
Proof.
    intros.
    apply gt_left_comm.
    apply gt_right_comm.
    assumption.
Qed.

Definition gt_2143 A B C D := gt_comm A B C D.

End Gt_prop.

Print All.


