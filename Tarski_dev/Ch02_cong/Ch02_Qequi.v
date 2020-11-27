Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong_transitivity.

Section Cong_Rhb.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma def_to_qequi : forall A B C D,
 Cong A B B C -> Cong A B A D ->  Cong B C C D
-> QEqui A B C D.
Proof.
    intros.
    repeat split; assumption.
Qed.

Lemma qequi_to_def : forall A B C D,
  QEqui A B C D-> Cong A B B C /\ Cong A B A D /\  Cong B C C D.
Proof.
    intros.
    assumption.
Qed.

Lemma qequi_to_all : forall A B C D,
  QEqui A B C D-> Cong A B B C /\ Cong A B A D /\
                    Cong A D C D /\ Cong B C C D /\
                    Cong A B C D /\ Cong A D B C.
Proof.
    intros.
    apply qequi_to_def in H.
    spliter.
    assert(Cong A B C D).
      apply cong_12XY_XY34 with B C; assumption.
    repeat split; try assumption.
    apply cong_XY12_XY34 with A B; assumption.
    apply cong_XY12_XY34 with A B; assumption.
Qed.

Lemma qequi_reverse : forall A B C D,
  QEqui A B C D -> QEqui A D C B.
Proof.
    intros.
    apply qequi_to_all in H.
    spliter.
    repeat split.
      apply cong_1243. assumption.
      apply cong_3412. assumption.
      apply cong_4321. assumption.
Qed.

Lemma qequi_rot_1 : forall A B C D,
  QEqui A B C D -> QEqui B C D A.
Proof.
    intros.
    apply qequi_to_all in H.
    spliter.
    repeat split.
      assumption.
      apply cong_3421. assumption.
      apply cong_3421. assumption.
Qed.

Lemma qequi_rot_2 : forall A B C D,
  QEqui A B C D -> QEqui C D A B.
Proof.
    intros.
    apply qequi_rot_1.
    apply qequi_rot_1.
    assumption.
Qed.

Lemma qequi_rot_3 : forall A B C D,
  QEqui A B C D -> QEqui D A B C.
Proof.
    intros.
    apply qequi_rot_1.
    apply qequi_rot_1.
    apply qequi_rot_1.
    assumption.
Qed.

Lemma qequi_rrot_1 : forall A B C D,
  QEqui A B C D -> QEqui D C B A.
Proof.
    intros.
    apply qequi_rot_1.
    apply qequi_reverse.
    assumption.
Qed.

Lemma qequi_rrot_2 : forall A B C D,
  QEqui A B C D -> QEqui C B A D.
Proof.
    intros.
    apply qequi_rot_1.
    apply qequi_rrot_1.
    assumption.
Qed.

Lemma qequi_rrot_3 : forall A B C D,
  QEqui A B C D -> QEqui B A D C.
Proof.
    intros.
    apply qequi_reverse.
    apply qequi_rot_1.
    assumption.
Qed.

Lemma qequi_2op_1adj_B : forall A B C D,
  Cong A B C D -> Cong A D B C -> Cong A B B C
-> QEqui A B C D.
Proof.
    intros.
    repeat split; try assumption.
      apply cong_12XY_34XY with B C; assumption.
      apply cong_XY12_XY34 with A B; assumption.
Qed.

Lemma qequi_2op_1adj_A : forall A B C D,
  Cong A B C D -> Cong A D B C -> Cong A B A D
-> QEqui A B C D.
Proof.
    intros.
    apply qequi_rot_1.
    apply qequi_2op_1adj_B.
        apply cong_2134. assumption.
        apply cong_4312. assumption.
        apply cong_4312. assumption.
Qed.

Lemma qequi_2op_1adj_D : forall A B C D,
  Cong A B C D -> Cong A D B C -> Cong A D C D
-> QEqui A B C D.
Proof.
    intros.
    apply qequi_reverse.
      apply qequi_2op_1adj_B.
        apply cong_1243. assumption.
        apply cong_1243. assumption.
        apply cong_1243. assumption.
Qed.

Lemma qequi_2op_1adj_C : forall A B C D,
  Cong A B C D -> Cong A D B C -> Cong B C C D
-> QEqui A B C D.
Proof.
    intros.
    apply qequi_rot_2.
      apply qequi_2op_1adj_A.
        apply cong_3412. assumption.
        apply cong_4321. assumption.
        apply cong_3421. assumption.
Qed.

Lemma qequi_2adj_1op_1 : forall A B C D,
  Cong A B A D -> Cong B C C D -> Cong A B C D
-> QEqui A B C D.
Proof.
    intros.
    repeat split; try assumption.
      apply cong_12XY_34XY with C D; assumption.
Qed.

Lemma qequi_2adj_1op_2 : forall A B C D,
  Cong A B A D -> Cong B C C D -> Cong A D B C
-> QEqui A B C D.
Proof.
    intros.
    repeat split; try assumption.
      apply cong_12XY_XY34 with A D; assumption.
Qed.

Lemma qequi_2adj_1op_3 : forall A B C D,
  Cong A B A D -> Cong A B B C -> Cong A B C D
-> QEqui A B C D.
Proof.
    intros.
    repeat split; try assumption.
      apply cong_XY12_XY34 with A B; assumption.
Qed.

Lemma qequi_3adj : forall A B C D,
  Cong A B A D -> Cong A B B C -> Cong B C C D
-> QEqui A B C D.
Proof.
    intros.
    repeat split; assumption.
Qed.

End Cong_Rhb.

Section To_Cong.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma qequi_cong_1214 : forall A B C D, 
  QEqui A B C D -> Cong A B A D.
Proof.
    intros.
    apply qequi_to_all in H.
    spliter.
    assumption.
Qed.

Lemma qequi_cong_1223 : forall A B C D, 
  QEqui A B C D -> Cong A B B C.
Proof.
    intros.
    apply qequi_to_all in H.
    spliter.
    assumption.
Qed.

Lemma qequi_cong_1234 : forall A B C D, 
  QEqui A B C D -> Cong A B C D.
Proof.
    intros.
    apply qequi_to_all in H.
    spliter.
    assumption.
Qed.

Lemma qequi_cong_1423 : forall A B C D, 
  QEqui A B C D -> Cong A D B C.
Proof.
    intros.
    apply qequi_to_all in H.
    spliter.
    assumption.
Qed.

Lemma qequi_cong_1434 : forall A B C D, 
  QEqui A B C D -> Cong A D C D.
Proof.
    intros.
    apply qequi_to_all in H.
    spliter.
    assumption.
Qed.

Lemma qequi_cong_2334 : forall A B C D, 
  QEqui A B C D -> Cong B C C D.
Proof.
    intros.
    apply qequi_to_all in H.
    spliter.
    assumption.
Qed.

End To_Cong.

Print All.

