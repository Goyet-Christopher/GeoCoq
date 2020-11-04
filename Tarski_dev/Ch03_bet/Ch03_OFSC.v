Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet.

Section OFSC_def.
Context `{TnEQD:Tarski_neutral_dimensionless}.

Lemma def_to_OFSC : forall A B C D A' B' C' D', 
  Bet A B C ->
  Bet A' B' C' ->
  Cong A B A' B' ->
  Cong B C B' C' ->
  Cong A D A' D' ->
  Cong B D B' D'-> 
  OFSC A B C D A' B' C' D'.
Proof.
    intros.
    repeat split; assumption.
Qed.

Lemma def_to_OFSC_with_cong3 : forall A B C D A' B' C' D', 
  Bet A B C ->
  Bet A' B' C' ->
  Cong_3 A B D A' B' D' ->
  Cong B C B' C' ->
  OFSC A B C D A' B' C' D'.
Proof.
    intros.
    apply cong3_to_def in H1.
    spliter.
    apply def_to_OFSC; assumption.
Qed.

Lemma OFSC_to_def : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Bet A B C /\
  Bet A' B' C' /\
  Cong A B A' B' /\
  Cong B C B' C' /\
  Cong A D A' D' /\
  Cong B D B' D'.
Proof.
    intros.
    assumption.
Qed.

Lemma OFSC_to_def_with_cong3 : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Bet A B C /\
  Bet A' B' C' /\
  Cong B C B' C' /\
  Cong_3 A B D A' B' D'.
Proof.
    intros.
    apply OFSC_to_def in H.
    spliter.
    repeat split; assumption.
Qed.

Lemma OFSC_bet1 : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Bet A B C.
Proof.
    intros.
    apply H.
Qed.

Lemma OFSC_bet1_sym : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Bet C B A.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.

Lemma OFSC_bet2 : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Bet A' B' C'.
Proof.
    intros.
    apply H.
Qed.

Lemma OFSC_bet2_sym : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Bet C' B' A'.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.


Lemma OFSC_cong_12 : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Cong A B A' B'.
Proof.
    intros.
    apply H.
Qed.

Lemma OFSC_cong_14 : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Cong A D A' D'.
Proof.
    intros.
    apply H.
Qed.

Lemma OFSC_cong_23 : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Cong B C B' C'.
Proof.
    intros.
    apply H.
Qed.

Lemma OFSC_cong_24 : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Cong B D B' D'.
Proof.
    intros.
    apply H.
Qed.

Lemma OFSC_cong3_124 : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Cong_3 A B D A' B' D'.
Proof.
    intros.
    apply OFSC_to_def_with_cong3 in H.
    apply H.
Qed.

End OFSC_def.

Section T1_3.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma five_segment_with_OFSC : forall A B C D A' B' C' D',
 OFSC A B C D A' B' C' D' -> A<>B -> Cong C D C' D'.
Proof.
    intros.
    apply OFSC_to_def in H.
    spliter.
    apply (five_segment A A' B B'); assumption.
Qed.

Definition OFSC_cong_34 A B C D A' B' C' D' :=
five_segment_with_OFSC A B C D A' B' C' D'.


Lemma OFSC_cong3_234 : forall A B C D A' B' C' D',
 OFSC A B C D A' B' C' D' -> A<>B 
-> Cong_3 B C D B' C' D'.
Proof.
    intros.
    apply def_to_cong3.
    apply H.
    apply H.
    apply OFSC_cong_34 with A B A' B';
    assumption.
Qed.

Lemma l2_11_neq_with_OFSC : forall A B C D A' B' C' D',
 OFSC A B C D A' B' C' D' -> A<>B -> Cong A C A' C'.
Proof.
    intros.
    apply OFSC_to_def in H.
    spliter.
    apply l2_11_neq with B B'; assumption.
Qed.

Lemma OFSC_cong3_134 : forall A B C D A' B' C' D',
 OFSC A B C D A' B' C' D' -> A<>B 
-> Cong_3 A C D A' C' D'.
Proof.
    intros.
    apply def_to_cong3.
    apply l2_11_neq_with_OFSC with B D B' D'; assumption.
    apply H.
    apply OFSC_cong3_234 with A B A' B'; assumption.
Qed.

Lemma l2_11_eq_with_OFSC : forall A B C D A' B' C' D',
 OFSC A B C D A' B' C' D' -> A=B -> Cong A C A' C'.
Proof.
    intros.
    apply OFSC_to_def in H.
    spliter.
    apply l2_11_eq with B B'; assumption.
Qed.

End T1_3.

Section OFSC_prop.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma OFSC_cong_13 : forall A B C D A' B' C' D',
 OFSC A B C D A' B' C' D' -> Cong A C A' C'.
Proof.
    intros.
    apply OFSC_to_def in H.
    spliter.
    apply l2_11 with B B'; assumption.
Qed.

Lemma OFSC_cong3_123 : forall A B C D A' B' C' D', 
  OFSC A B C D A' B' C' D'
  -> Cong_3 A B C A' B' C'.
Proof.
    intros.
    apply def_to_cong3.
    apply OFSC_cong_12 with C D C' D'; assumption.
    apply OFSC_cong_13 with B D B' D'; assumption.
    apply OFSC_cong_23 with A D A' D'; assumption.
Qed.

Lemma OFSC_cong3 : forall A B C D A' B' C' D',
  OFSC A B C D A' B' C' D' -> A<>B
  -> Bet A B C /\ Bet A' B' C' /\
     Cong_3 A B C A' B' C' /\
     Cong_3 A B D A' B' D' /\
     Cong_3 B C D B' C' D' /\
     Cong_3 A C D A' C' D'.
Proof.
    intros.
    split. apply H.
    split. apply H.
    split. apply OFSC_cong3_123 with D D'; assumption.
    split. apply OFSC_cong3_124 with C C'; assumption.
    split.
    apply OFSC_cong3_234 with A A'; assumption.
    apply OFSC_cong3_134 with B B'; assumption.
Qed.

(* necessite des 2 Bet ??? *)
Lemma cong3_OFSC : forall A B C D A' B' C' D',
  Bet A B C -> Bet A' B' C'
  -> Cong_3 A B D A' B' D' 
  -> Cong_3 A B C A' B' C' \/ Cong_3 B C D B' C' D'
  -> OFSC A B C D A' B' C' D'.
Proof.
    intros.
    assert(Cong B C B' C').
      induction H2.
      apply cong3_23 with A A'; assumption.
      apply cong3_12 with D D'; assumption.
    apply def_to_OFSC_with_cong3; assumption.
Qed.

Lemma OFSC_symmetry : forall A B C D A' B' C' D',
  OFSC A B C D A' B' C' D' -> A<>B
  -> OFSC C B A D C' B' A' D'.
Proof.
    intros.
    apply OFSC_cong3 in H.
    spliter.
    apply cong3_OFSC.
    apply between_symmetry; assumption.
    apply between_symmetry; assumption.
    apply cong3_swap_213; assumption.
    right. apply cong3_swap_213; assumption.
    assumption.
Qed.

Lemma OFSC_axial_sym : forall A B C D D',
  Bet A B C -> Cong_3 A B D A B D'
  -> OFSC A B C D A B C D'.
Proof.
      repeat split.
      assumption. assumption.
      apply H0.
      apply cong_1212.
      apply H0.
      apply H0.
Qed.

Lemma OFSC_axial_sym2 : forall A B C D D',
  Bet A B C -> Cong A D A D' -> Cong B D B D'
  -> OFSC A B C D A B C D'.
Proof.
      repeat split.
      assumption. assumption.
      apply cong_1212.
      apply cong_1212.
      assumption.
      assumption.
Qed.

Lemma OFSC_to_IFSC : forall A B C D A' B' C' D',
  OFSC A B C D A' B' C' D' -> A <> B
  -> IFSC A B C D A' B' C' D'.
Proof.
    intros.
    assert(Cong A C A' C').
      apply (OFSC_cong_13 A B C D A' B' C' D').
      assumption.
    assert(Cong C D C' D').
      apply (OFSC_cong_34 A B C D A' B' C' D');
      assumption.
    apply OFSC_to_def in H.
    spliter.
    repeat split;assumption.
Qed.



End OFSC_prop.

Print All.