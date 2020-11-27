Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong.
Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong_transitivity.

Section Cong3_def.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma def_to_cong3 : forall A B C A' B' C', 
  Cong A B A' B' -> Cong A C A' C' -> Cong B C B' C' 
-> Cong_3 A B C A' B' C'.
Proof.
    intros.
    repeat split; assumption.
Qed.

Lemma def_to_cong3_reverse : forall A B C A' B' C', 
  Cong A B B' C' -> Cong A C A' C' -> Cong B C A' B' 
-> Cong_3 A B C C' B' A'.
Proof.
    intros.
    repeat split; apply cong_1243; assumption.
Qed.

Lemma cong3_to_def : forall A B C A' B' C', 
  Cong_3 A B C A' B' C' ->
  Cong A B A' B' /\ Cong A C A' C' /\ Cong B C B' C'.
Proof.
    unfold Cong_3.
    intros.
    assumption.
Qed.

Lemma cong3_to_def_reverse : forall A B C A' B' C', 
  Cong_3 A B C C' B' A' ->
  Cong A B B' C' /\ Cong A C A' C' /\ Cong B C A' B'.
Proof.
    unfold Cong_3.
    intros.
    spliter.
    repeat split; apply cong_1243; assumption.
Qed.

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

End Cong3_def.

Section Cong3_prop.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong3_reflexivity : forall A B C,
  Cong_3 A B C A B C.
Proof.
    intros.
    apply def_to_cong3;
    apply cong_reflexivity.
Qed.

Lemma cong3_symmetry : forall A B C A' B' C',
 Cong_3 A B C A' B' C' -> Cong_3 A' B' C' A B C.
Proof.
    unfold Cong_3.
    intros.
    induction H.
    induction H0.
    repeat split; apply cong_3412; assumption.
Qed.

Lemma cong3_swap_132 : forall A B C A' B' C',
 Cong_3 A B C A' B' C' -> Cong_3 A C B A' C' B'.
Proof.
    unfold Cong_3.
    intros.
    repeat match goal with
   | H:(?X1 /\ ?X2) |- _ => induction H end.
    apply cong_2143 in H1.
    repeat split; assumption.
Qed.

Lemma cong3_swap_213 : forall A B C A' B' C',
  Cong_3 A B C A' B' C' -> Cong_3 B A C B' A' C'.
Proof.
    unfold Cong_3.
    intros.
    spliter.
    apply cong_2143 in H.
    repeat split; assumption.
Qed.

Lemma cong3_swap_231 : forall A B C A' B' C',
  Cong_3 A B C A' B' C' -> Cong_3 B C A B' C' A'.
Proof.
    intros.
    apply cong3_swap_132.
    apply cong3_swap_213.
    assumption.
Qed.

Lemma cong3_swap_312 : forall A B C A' B' C',
  Cong_3 A B C A' B' C' -> Cong_3 C A B C' A' B'.
Proof.
    intros.
    apply cong3_swap_213.
    apply cong3_swap_132.
    assumption.
Qed.

Lemma cong3_swap_321 : forall A B C A' B' C',
  Cong_3 A B C A' B' C' -> Cong_3 C B A C' B' A'.
Proof.
    intros.
    apply cong3_swap_231.
    apply cong3_swap_132.
    assumption.
Qed.

Lemma cong3_transitivity_12_23_13 : forall A0 B0 C0 A1 B1 C1 A2 B2 C2,
 Cong_3 A0 B0 C0 A1 B1 C1 -> Cong_3 A1 B1 C1 A2 B2 C2 -> Cong_3 A0 B0 C0 A2 B2 C2.
Proof.
    unfold Cong_3.
    intros.
    spliter.
    repeat split.
    apply cong_transitivity with A1 B1; assumption.
    apply cong_transitivity with A1 C1; assumption.
    apply cong_transitivity with B1 C1; assumption.
Qed.

Lemma cong3_transitivity_12_13_23 : forall A0 B0 C0 A1 B1 C1 A2 B2 C2,
 Cong_3 A0 B0 C0 A1 B1 C1 -> Cong_3 A0 B0 C0 A2 B2 C2 -> Cong_3 A1 B1 C1 A2 B2 C2.
Proof.
    intros.
    apply cong3_symmetry in H.
    apply cong3_transitivity_12_23_13 with A0 B0 C0;
    assumption.
Qed.

Lemma cong3_transitivity_12_31_13 : forall A0 B0 C0 A1 B1 C1 A2 B2 C2,
 Cong_3 A0 B0 C0 A1 B1 C1 -> Cong_3 A2 B2 C2 A1 B1 C1 -> Cong_3 A0 B0 C0 A2 B2 C2.
Proof.
    intros.
    apply cong3_symmetry in H0.
    apply cong3_transitivity_12_23_13 with A1 B1 C1;
    assumption.
Qed.

Lemma cong3_cases : forall A B C A' B' C',
  Cong_3 A B C A' B' C' \/ Cong_3 A C B A' C' B'
  \/ Cong_3 B A C B' A' C' \/ Cong_3 B C A B' C' A'
  \/ Cong_3 C A B C' A' B' \/ Cong_3 C B A C' B' A'
-> Cong_3 A B C A' B' C'.
Proof.
    intros.
    induction H. assumption.
    induction H. apply cong3_swap_132; assumption.
    induction H. apply cong3_swap_213; assumption.
    induction H. apply cong3_swap_312; assumption.
    induction H. apply cong3_swap_231; assumption.
    apply cong3_swap_321; assumption.
Qed.

Lemma cong3_perm : forall A B C A' B' C',
  Cong_3 A B C A' B' C'
  -> Cong_3 A B C A' B' C' /\ Cong_3 A C B A' C' B'
  /\ Cong_3 B A C B' A' C' /\ Cong_3 B C A B' C' A'
  /\ Cong_3 C A B C' A' B' /\ Cong_3 C B A C' B' A'.
Proof.
    intros.
    split. assumption.
    split. apply cong3_swap_132; assumption.
    split. apply cong3_swap_213; assumption.
    split. apply cong3_swap_231; assumption.
    split. apply cong3_swap_312; assumption.
    apply cong3_swap_321; assumption.
Qed.


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

End Cong3_prop.

Print All.
