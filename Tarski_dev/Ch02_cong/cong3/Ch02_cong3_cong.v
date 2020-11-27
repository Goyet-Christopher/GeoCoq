Require Export GeoCoq.Tarski_dev.Ch02_cong.cong3.Ch02_cong3.

Section Cong3_to_cong.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong3_1245 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong A B A' B'.
Proof.
    intros.
    apply H.
Qed.

Lemma cong3_1254: forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong A B B' A'.
Proof.
    intros.
    apply cong_1243.
    apply H.
Qed.

Lemma cong3_1346 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong A C A' C'.
Proof.
    intros.
    apply H.
Qed.

Lemma cong3_1364 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong A C C' A'.
Proof.
    intros.
    apply cong_1243.
    apply H.
Qed.

Lemma cong3_2145 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong B A A' B'.
Proof.
    intros.
    apply cong_2134.
    apply H.
Qed.

Lemma cong3_2154 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong B A B' A'.
Proof.
    intros.
    apply cong_2143.
    apply H.
Qed.

Lemma cong3_2356 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong B C B' C'.
Proof.
    intros.
    apply H.
Qed.

Lemma cong3_2365 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong B C C' B'.
Proof.
    intros.
    apply cong_1243.
    apply H.
Qed.

Lemma cong3_3146 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong C A A' C'.
Proof.
    intros.
    apply cong_2134.
    apply H.
Qed.

Lemma cong3_3164 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong C A C' A'.
Proof.
    intros.
    apply cong_2143.
    apply H.
Qed.

Lemma cong3_3256 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong C B B' C'.
Proof.
    intros.
    apply cong_2134.
    apply H.
Qed.

Lemma cong3_3265 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong C B C' B'.
Proof.
    intros.
    apply cong_2143.
    apply H.
Qed.

Lemma cong3_4512 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong A' B' A B.
Proof.
    intros.
    apply cong_3412.
    apply H.
Qed.

Lemma cong3_4521 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong A' B' B A.
Proof.
    intros.
    apply cong_3421.
    apply H.
Qed.

Lemma cong3_4613 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong A' C' A C.
Proof.
    intros.
    apply cong_3412.
    apply H.
Qed.

Lemma cong3_4631 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong A' C' C A.
Proof.
    intros.
    apply cong_3421.
    apply H.
Qed.

Lemma cong3_5412 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong B' A' A B.
Proof.
    intros.
    apply cong_4312.
    apply H.
Qed.

Lemma cong3_5421 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong B' A' B A.
Proof.
    intros.
    apply cong_4321.
    apply H.
Qed.

Lemma cong3_5623 : forall A B C A' B' C',
  Cong_3 A B C A' B' C' -> Cong B' C' B C.
Proof.
    intros.
    apply cong_3412.
    apply H.
Qed.

Lemma cong3_5632 : forall A B C A' B' C',
  Cong_3 A B C A' B' C' -> Cong B' C' C B.
Proof.
    intros.
    apply cong_3421.
    apply H.
Qed.

Lemma cong3_6413 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong C' A' A C.
Proof.
    intros.
    apply cong_4312.
    apply H.
Qed.

Lemma cong3_6431 : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' -> Cong C' A' C A.
Proof.
    intros.
    apply cong_4321.
    apply H.
Qed.

Lemma cong3_6523 : forall A B C A' B' C',
  Cong_3 A B C A' B' C' -> Cong C' B' B C.
Proof.
    intros.
    apply cong_4312.
    apply H.
Qed.

Lemma cong3_6532 : forall A B C A' B' C',
  Cong_3 A B C A' B' C' -> Cong C' B' C B.
Proof.
    intros.
    apply cong_4321.
    apply H.
Qed.

End Cong3_to_cong.

Print All.
