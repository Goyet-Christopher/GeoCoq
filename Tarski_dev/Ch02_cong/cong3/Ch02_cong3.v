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


End Cong3_prop.

Print All.
