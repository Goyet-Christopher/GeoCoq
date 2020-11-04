Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong.

Section T1_2.
(* Lemmes negatifs de cong *)

Context `{Tn:Tarski_neutral_dimensionless}.

(* We pre-compute some trivial lemmas to have more efficient automatic proofs. *)

Lemma not_cong_1243 : forall A B C D, 
  ~ Cong A B C D -> ~ Cong A B D C.
Proof.
    unfold not.
    intros.
    apply H.
    apply cong_right_commutativity.
    assumption.
Qed.

Lemma not_cong_2134 : forall A B C D, 
  ~ Cong A B C D -> ~ Cong B A C D.
Proof.
    unfold not.
    intros.
    apply H.
    apply cong_left_commutativity.
    assumption.
Qed.

Lemma not_cong_2143 : forall A B C D, 
  ~ Cong A B C D -> ~ Cong B A D C.
Proof.
    unfold not.
    intros.
    apply H.
    apply cong_2143.
    assumption.
Qed.

Lemma not_cong_3412 : forall A B C D, 
  ~ Cong A B C D -> ~ Cong C D A B.
Proof.
    unfold not.
    intros.
    apply H.
    apply cong_3412.
    assumption.
Qed.

Lemma not_cong_3421 : forall A B C D, 
  ~ Cong A B C D -> ~ Cong C D B A.
Proof.
    unfold not.
    intros.
    apply H.
    apply cong_4312.
    assumption.
Qed.

Lemma not_cong_4312 : forall A B C D, 
  ~ Cong A B C D -> ~ Cong D C A B.
Proof.
    unfold not.
    intros.
    apply H.
    apply cong_3421.
    assumption.
Qed.

Lemma not_cong_4321 : forall A B C D, 
  ~ Cong A B C D -> ~ Cong D C B A.
Proof.
    unfold not.
    intros.
    apply H.
    apply cong_4321.
    assumption.
Qed.

End T1_2.



Print All.
