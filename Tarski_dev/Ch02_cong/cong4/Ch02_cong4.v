Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong3.

Section Cong4_def.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma def_to_cong4 : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong P1 P2 Q1 Q2 ->
  Cong P1 P3 Q1 Q3 ->
  Cong P1 P4 Q1 Q4 ->
  Cong P2 P3 Q2 Q3 ->
  Cong P2 P4 Q2 Q4 ->
  Cong P3 P4 Q3 Q4 -> Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4.
Proof.
    intros.
    repeat split; assumption.
Qed.

Lemma def_to_cong4_with_cong3 : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_3 P1 P2 P3 Q1 Q2 Q3 ->
  Cong_3 P1 P2 P4 Q1 Q2 Q4 ->
  Cong_3 P1 P3 P4 Q1 Q3 Q4 ->
  Cong_3 P2 P3 P4 Q2 Q3 Q4 -> Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4.
Proof.
    unfold Cong_3.
    intros.
    spliter.
    repeat split; assumption.
Qed.

Lemma def_to_cong4_reverse : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong P1 P2 Q2 Q1 ->
  Cong P1 P3 Q3 Q1 ->
  Cong P1 P4 Q4 Q1 ->
  Cong P2 P3 Q3 Q2 ->
  Cong P2 P4 Q4 Q2 ->
  Cong P3 P4 Q4 Q3 -> Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4.
Proof.
    intros.
    repeat split; apply cong_1243; assumption.
Qed.

Lemma cong4_to_def : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 ->
  Cong P1 P2 Q1 Q2 /\
  Cong P1 P3 Q1 Q3 /\
  Cong P1 P4 Q1 Q4 /\
  Cong P2 P3 Q2 Q3 /\
  Cong P2 P4 Q2 Q4 /\
  Cong P3 P4 Q3 Q4.
Proof.
    intros.
    assumption.
Qed.

Lemma cong4_to_def_reverse : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 ->
  Cong P1 P2 Q2 Q1 /\
  Cong P1 P3 Q3 Q1 /\
  Cong P1 P4 Q4 Q1 /\
  Cong P2 P3 Q3 Q2 /\
  Cong P2 P4 Q4 Q2 /\
  Cong P3 P4 Q4 Q3.
Proof.
    intros.
    apply cong4_to_def in H.
    spliter.
    repeat split; apply cong_1243; assumption.
Qed.

Lemma cong4_to_def_with_cong3 : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 ->
  Cong_3 P1 P2 P3 Q1 Q2 Q3 /\
  Cong_3 P1 P2 P4 Q1 Q2 Q4 /\
  Cong_3 P1 P3 P4 Q1 Q3 Q4 /\
  Cong_3 P2 P3 P4 Q2 Q3 Q4 .
Proof.
    unfold Cong_4.
    unfold Cong_3.
    intros.
    spliter.
    repeat split; assumption.
Qed.

Lemma cong4_cong3_123 : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 -> Cong_3 P1 P2 P3 Q1 Q2 Q3.
Proof.
    intros.
    apply cong4_to_def_with_cong3 in H.
    apply H.
Qed.

Lemma cong4_cong3_124 : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 -> Cong_3 P1 P2 P4 Q1 Q2 Q4.
Proof.
    intros.
    apply cong4_to_def_with_cong3 in H.
    apply H.
Qed.

Lemma cong4_cong3_134 : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 -> Cong_3 P1 P3 P4 Q1 Q3 Q4.
Proof.
    intros.
    apply cong4_to_def_with_cong3 in H.
    apply H.
Qed.

Lemma cong4_cong3_234 : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 -> Cong_3 P2 P3 P4 Q2 Q3 Q4.
Proof.
    intros.
    apply cong4_to_def_with_cong3 in H.
    apply H.
Qed.

Lemma cong4_12 : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 -> Cong P1 P2 Q1 Q2.
Proof.
    intros.
    apply H.
Qed.

Lemma cong4_13 : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 -> Cong P1 P3 Q1 Q3.
Proof.
    intros.
    apply H.
Qed.

Lemma cong4_14 : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 -> Cong P1 P4 Q1 Q4.
Proof.
    intros.
    apply H.
Qed.

Lemma cong4_23 : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 -> Cong P2 P3 Q2 Q3.
Proof.
    intros.
    apply H.
Qed.

Lemma cong4_24 : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 -> Cong P2 P4 Q2 Q4.
Proof.
    intros.
    apply H.
Qed.

Lemma cong4_34 : forall P1 P2 P3 P4 Q1 Q2 Q3 Q4, 
  Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 -> Cong P3 P4 Q3 Q4.
Proof.
    intros.
    apply H.
Qed.

End Cong4_def.

Section Cong4_prop.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong4_reflexivity : forall A B C D,
  Cong_4 A B C D A B C D.
Proof.
    intros.
    apply def_to_cong4;
    apply cong_reflexivity.
Qed.

Lemma cong4_symmetry : forall A B C D A' B' C' D',
 Cong_4 A B C D A' B' C' D' -> Cong_4 A' B' C' D' A B C D.
Proof.
    intros.
    apply cong4_to_def in H.
    spliter.
    repeat split; apply cong_3412; assumption.
Qed.

End Cong4_prop.

Print All.
