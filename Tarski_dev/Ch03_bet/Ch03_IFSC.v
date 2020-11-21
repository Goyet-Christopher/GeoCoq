Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_OFSC.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_exists.

Section IFSC_def.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma def_to_IFSC : forall A B C D A' B' C' D', 
  Bet A B C ->
  Bet A' B' C' ->
  Cong A C A' C' ->
  Cong B C B' C' ->
  Cong A D A' D' ->
  Cong C D C' D' ->
  IFSC A B C D A' B' C' D'.
Proof.
    intros.
    repeat split; assumption.
Qed.

Lemma def_to_IFSC_with_cong3 : forall A B C D A' B' C' D', 
  Bet A B C ->
  Bet A' B' C' ->
  Cong B C B' C' ->
  Cong_3 A C D A' C' D' ->
  IFSC A B C D A' B' C' D'.
Proof.
    intros.
    apply cong3_to_def in H2.
    spliter.
    apply def_to_IFSC; assumption.
Qed.

Lemma IFSC_to_def : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
 ->Bet A B C /\
   Bet A' B' C' /\
   Cong A C A' C' /\
   Cong B C B' C' /\
   Cong A D A' D' /\
   Cong C D C' D'.
Proof.
    intros.
    assumption.
Qed.

Lemma IFSC_to_def_with_cong3 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Bet A B C /\
    Bet A' B' C' /\
    Cong B C B' C' /\
    Cong_3 A C D A' C' D'.
Proof.
    intros.
    apply IFSC_to_def in H.
    spliter. 
    repeat split; assumption.
Qed.

Lemma IFSC_bet1 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Bet A B C.
Proof.
    intros.
    apply H.
Qed.

Lemma IFSC_bet1_sym : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Bet C B A.
Proof.
    intros.
    apply between_symmetry.
    apply (IFSC_bet1 A B C D A' B' C' D').
    assumption.
Qed.


Lemma IFSC_bet2 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Bet A' B' C'.
Proof.
    intros.
    apply H.
Qed.

Lemma IFSC_bet2_sym : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Bet C' B' A'.
Proof.
    intros.
    apply between_symmetry.
    apply (IFSC_bet2 A B C D A' B' C' D').
    assumption.
Qed.


Lemma IFSC_cong_13 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Cong A C A' C'.
Proof.
    intros.
    apply H.
Qed.

Lemma IFSC_cong_14 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Cong A D A' D'.
Proof.
    intros.
    apply H.
Qed.

Lemma IFSC_cong_23 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Cong B C B' C'.
Proof.
    intros.
    apply H.
Qed.

Lemma IFSC_cong_34 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Cong C D C' D'.
Proof.
    intros.
    apply H.
Qed.

Lemma IFSC_cong3_134 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Cong_3 A C D A' C' D'.
Proof.
    intros.
    apply IFSC_to_def_with_cong3 in H.
    apply H.
Qed.

End IFSC_def.

Section IFSC_prop.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma IFSC_reflexivity : forall A B C D,
  Bet A B C-> IFSC A B C D A B C D.
Proof.
    intros.
    apply def_to_IFSC_with_cong3.
      assumption.
      assumption.
      apply cong_reflexivity.
      apply cong3_reflexivity.
Qed.

Lemma IFSC_axial_sym : forall A B C D D',
  Bet A B C -> Cong A D A D' -> Cong C D C D'
  -> IFSC A B C D A B C D'.
Proof.
    repeat split.
    assumption. assumption.
    apply cong_1212.
    apply cong_1212.
    assumption.
    assumption.
Qed.

Lemma IFSC_axial_sym_cong3 : forall A B C D D',
  Bet A B C -> Cong_3 A C D A C D'
  -> IFSC A B C D A B C D'.
Proof.
    intros.
    apply cong3_to_def in H0.
    spliter.
    repeat split.
    assumption. assumption.
    apply cong_1212.
    apply cong_1212.
    assumption.
    assumption.
Qed.

Lemma IFSC_axial_sym2 : forall A B C D,
  Bet A B C -> Cong A B B C -> Cong A D C D
  -> IFSC A B C D C B A D.
Proof.
    repeat split.
    assumption.
    apply between_symmetry. assumption.
    apply cong_1221.
    apply cong_3421. assumption.
    assumption.
    apply cong_3412. assumption.
Qed.

Lemma IFSC_IFSC_Bet : forall A B C D E A' B' C' D' E',
  IFSC A B C D A' B' C' D' -> IFSC B C E D B' C' E' D'
  -> B<>C \/ B'<>C'
  -> Bet A B E /\ Bet A' B' E' /\ Bet A C E /\ Bet A' C' E' .
Proof.
    intros.
    apply IFSC_to_def in H.
    apply IFSC_to_def in H0.
    spliter.
    assert(B <> C).
      induction H1.
        assumption.
      apply cong_diff_12_34 with B' C'.
        assumption.
        apply cong_3412; assumption.
    assert(B' <> C').
      induction H1.
        apply cong_diff_12_34 with B C; assumption.
        assumption.
    assert(Bet A B E).
      apply between_outer_transitivity_3 with C;
      assumption.
    assert(Bet A' B' E').
      apply between_outer_transitivity_3 with C';
      assumption.
    repeat split.
    assumption.
    assumption.
    apply between_exchange_2 with B; assumption.
    apply between_exchange_2 with B'; assumption.
Qed.

Lemma IFSC_transitivity_1 : forall A B C D E A' B' C' D' E',
  IFSC A B C D A' B' C' D' -> IFSC B C E D B' C' E' D'
  -> B<>C \/ B'<>C'
  -> IFSC A B E D A' B' E' D'.
Proof.
    intros.
    assert(Bet A B E /\ Bet A' B' E' /\ Bet A C E /\ Bet A' C' E').
      apply IFSC_IFSC_Bet with D D'; assumption.
    apply IFSC_to_def in H.
    apply IFSC_to_def in H0.
    spliter.
    assert(Cong A E A' E').
      apply l2_11 with C C'; assumption.
    apply def_to_IFSC; assumption.
Qed.

Lemma IFSC_transitivity_2 : forall A B C D E A' B' C' D' E',
  IFSC A B C D A' B' C' D' -> IFSC B C E D B' C' E' D'
  -> B<>C \/ B'<>C'
  -> IFSC A C E D A' C' E' D'.
Proof.
    intros.
    assert(IFSC A B E D A' B' E' D').
      apply IFSC_transitivity_1 with C C'; assumption.
    assert(Bet A B E /\ Bet A' B' E' /\ Bet A C E /\ Bet A' C' E').
      apply IFSC_IFSC_Bet with D D'; assumption.
    apply IFSC_to_def in H.
    apply IFSC_to_def in H0.
    apply IFSC_to_def in H2.
    spliter.
    repeat split; assumption.
Qed.

(*
Lemma IFSC_transitivity_3 : forall A B C D E A' B' C' D' E', 
  IFSC A B C D A' B' C' D' -> IFSC A C E D A' C' E' D'
  -> IFSC B C E D B' C' E' D'.
*)

End IFSC_prop.

Section IFSC_extend.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma IFSC_prolong_to_OFSC : forall A B C D E A' B' C' D' E',
  IFSC A B C D A' B' C' D' -> Bet A C E -> Bet A' C' E'
  -> Cong C E C' E'
  -> OFSC A C E D A' C' E' D'.
Proof.
    intros.
    apply IFSC_to_def in H.
    spliter. 
    repeat split; try assumption.
Qed.

Lemma IFSC_prolong_to_IFSC : forall A B C D E A' B' C' D' E',
  IFSC A B C D A' B' C' D' -> Bet A C E -> Bet A' C' E'
  -> Cong C E C' E' -> A<>B \/ A<>C
  -> IFSC A C E D A' C' E' D'.
Proof.
    intros.
    apply OFSC_to_IFSC.
    apply IFSC_prolong_to_OFSC with B B';
      assumption.
    left.
    induction H3.
      apply IFSC_bet1 in H.
      apply bet_neq12__neq with B; assumption.
    assumption.
Qed.

Lemma IFSC_IFSC_swap_OFSC : forall A B C D E A' B' C' D' E', 
  IFSC A B C D A' B' C' D' -> IFSC A C E D A' C' E' D'
  -> OFSC E C B D E' C' B' D'.
Proof.
    intros.
    apply IFSC_to_def in H.
    apply IFSC_to_def in H0.
    spliter.
    repeat split.
    apply between_symmetry.
    apply between_exchange_1 with A; assumption.
    apply between_symmetry.
    apply between_exchange_1 with A'; assumption.
    apply cong_2143; assumption.
    apply cong_2143; assumption.
    assumption.
    assumption.
Qed.

End IFSC_extend.

Section T3.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l4_2_neq : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D' -> A<>C -> Cong B D B' D'.
Proof.
    intros.
    prolong_bet A C E.
    prolong A' C' E' C E.
    (* Mq ACED en configuration 5 segments *)
    assert(IFSC A C E D A' C' E' D').
      apply IFSC_prolong_to_IFSC with B B'; try assumption.
      right; assumption.
    (* Mq ECBD en configuration 5 segments *)
    assert(OFSC E C B D E' C' B' D').
      apply IFSC_IFSC_swap_OFSC with A A'; assumption.
    apply (OFSC_cong_34 E C B D E' C' B' D').
      assumption.
      left.
      apply diff_symmetry.
      assumption.
Qed.

Lemma l4_2_eq : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D' -> A=C -> Cong B D B' D'.
Proof.
    intros.
    apply IFSC_to_def in H.
    subst.
    spliter.
    apply cong_reverse_identity in H1.
    subst.
    apply between_identity in H.
    subst.
    apply between_identity in H0.
    subst.
    assumption.
Qed.

Lemma l4_2 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D' -> Cong B D B' D'.
Proof.
  intros.
  induction (eq_dec_points A C).
    apply l4_2_eq with A C A' C'; assumption.
    apply l4_2_neq with A C A' C'; assumption.
Qed.

Definition IFSC_cong_24 A B C D A' B' C' D' :=
  l4_2 A B C D A' B' C' D'.

Lemma l4_17_IFSC : forall A B C P Q,
  Bet A C B
  -> Cong A P A Q -> Cong B P B Q 
  -> Cong C P C Q.
Proof.
    intros.
    assert (IFSC A C B P A C B Q).
      apply IFSC_axial_sym; assumption.
    apply IFSC_cong_24 with A B A B; assumption.
Qed.

Lemma IFSC_cong3_234 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Cong_3 B C D B' C' D'.
Proof.
    intros.
    assert (Cong B D B' D').
      apply l4_2 with A C A' C'; assumption.
    apply IFSC_to_def in H.
    spliter.
    apply def_to_cong3; assumption.
Qed.

Lemma l4_3 : forall A B C A' B' C',
  Bet A B C -> Bet A' B' C' 
  -> Cong A C A' C' -> Cong B C B' C' 
  -> Cong A B A' B'.
Proof.
    intros.
    apply cong_commutativity.
    apply (l4_2 A B C A A' B' C' A').
    assert (Cong A A A' A').
        apply cong_1122.
    assert(Cong C A C' A').
        apply cong_commutativity.
        assumption.
    apply def_to_IFSC; assumption.
Qed.

Lemma IFSC_cong_12 : forall A B C D A' B' C' D',
  IFSC A B C D A' B' C' D' -> Cong A B A' B'.
Proof.
    intros.
    apply IFSC_to_def in H.
    spliter.
    apply l4_3 with C C'; assumption.
Qed.

Lemma IFSC_cong3_123 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Cong_3 A B C A' B' C'.
Proof.
    intros.
    apply def_to_cong3. 
    apply IFSC_cong_12 with C D C' D'; assumption.
    apply IFSC_cong_13 with B D B' D'; assumption.
    apply IFSC_cong_23 with A D A' D'; assumption.
Qed.

Lemma IFSC_cong3_124 : forall A B C D A' B' C' D', 
  IFSC A B C D A' B' C' D'
  -> Cong_3 A B D A' B' D'.
Proof.
    intros.
    apply def_to_cong3.
    apply IFSC_cong_12 with C D C' D'; assumption.
    apply H.
    apply l4_2 with A C A' C'; assumption.
Qed.

Lemma IFSC_cong3 : forall A B C D A' B' C' D',
  IFSC A B C D A' B' C' D'
  -> Bet A B C /\ Bet A' B' C' /\
     Cong_3 A B C A' B' C' /\
     Cong_3 A B D A' B' D' /\
     Cong_3 B C D B' C' D' /\
     Cong_3 A C D A' C' D'.
Proof.
    intros.
    split. apply H.
    split. apply H.
    split. apply IFSC_cong3_123 with D D'; assumption.
    split. apply IFSC_cong3_124 with C C'; assumption.
    split. apply IFSC_cong3_234 with A A'; assumption.
    apply IFSC_cong3_134 with B B'; assumption.
Qed.

Lemma IFSC_cong4 : forall A B C D A' B' C' D',
  IFSC A B C D A' B' C' D'
  -> Bet A B C /\ Bet A' B' C' /\
     Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    apply IFSC_cong3 in H.
    spliter.
    split.
      assumption.
    split.
      assumption.
    apply def_to_cong4_with_cong3; assumption.
Qed.

(* necessite des 2 Bet ??? *)
Lemma cong3_IFSC : forall A B C D A' B' C' D',
  Bet A B C -> Bet A' B' C'
  -> Cong_3 B C D B' C' D' \/ Cong_3 A B C A' B' C'
  -> Cong_3 A C D A' C' D' 
  -> IFSC A B C D A' B' C' D'.
Proof.
    intros.
    assert(Cong B C B' C').
      induction H1.
      apply cong3_1245 with D D'; assumption.
      apply cong3_2356 with A A'; assumption.
    apply def_to_IFSC_with_cong3; assumption.
Qed.


Lemma l4_3_1 : forall A B C A' B' C',
 Bet A B C -> Bet A' B' C' 
  -> Cong A B A' B' -> Cong A C A' C' 
  -> Cong B C B' C'.
Proof.
    intros.
    apply cong_commutativity.
    apply between_symmetry in H.
    apply between_symmetry in H0.
    apply cong_commutativity in H1.
    apply cong_commutativity in H2.
    apply l4_3 with A A'; assumption.
Qed.

Lemma IFSC_symmetry : forall A B C D A' B' C' D',
  IFSC A B C D A' B' C' D'
  -> IFSC A' B' C' D' A B C D.
Proof.
    intros.
    apply IFSC_cong3 in H.
    spliter.
    apply def_to_IFSC_with_cong3.
    assumption.
    assumption.
    apply cong3_4512 with D D'; assumption.
    apply cong3_symmetry; assumption.
Qed.

Lemma IFSC_symmetry_24 : forall A B C D A' B' C' D',
  IFSC A B C D A' B' C' D'
  -> IFSC C B A D C' B' A' D'.
Proof.
    intros.
    apply def_to_IFSC_with_cong3.
    apply between_symmetry; apply H.
    apply between_symmetry; apply H.
    apply cong_2143.
    apply IFSC_cong_12 with C D C' D'.
    assumption.
    apply cong3_swap_213.
    apply IFSC_to_def_with_cong3 with B B'.
    apply H.
Qed.

Lemma IFSC_eq : forall  A B C X,
  IFSC A B C B A B C X ->  B = X.
Proof.
    intros.
    assert (Cong B B B X).
      apply l4_2 with A C A C; assumption.
    apply cong_reverse_identity with B.
    assumption.
Qed.

Lemma IFSC_to_OFSC : forall A B C D A' B' C' D',
  IFSC A B C D A' B' C' D' -> OFSC A B C D A' B' C' D'.
Proof.
    intros.
    apply IFSC_cong3 in H.
    apply def_to_OFSC_with_cong3; apply H.
Qed.

End T3.

Print All.


