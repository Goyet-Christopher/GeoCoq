Require Export GeoCoq.Tarski_dev.Ch05_le_lt_ge_gt.Ch05_final.

Section Out_def.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma def_to_out :  forall P A B, 
   P <> A -> P <> B ->
  (Bet P A B \/ Bet P B A) -> Out P A B.
Proof.
    intros.
    repeat split; assumption.
Qed.

Lemma out_to_def :  forall P A B, 
  Out P A B -> P <> A /\ P <> B /\
              (Bet P A B \/ Bet P B A).
Proof.
    intros.
    assumption.
Qed.

Lemma out_diff1 :  forall P A B, 
  Out P A B -> P <> A .
Proof.
    intros.
    apply H.
Qed.

Lemma out_diff1_sym :  forall P A B, 
  Out P A B -> A <> P .
Proof.
    intros.
    apply diff_symmetry.
    apply H.
Qed.

Lemma out_diff2 :  forall P A B, 
  Out P A B -> P <> B.
Proof.
    intros.
    apply H.
Qed.

Lemma out_diff2_sym :  forall P A B, 
  Out P A B -> B <> P.
Proof.
    intros.
    apply diff_symmetry.
    apply H.
Qed.

Lemma out_betOr :  forall P A B, 
  Out P A B -> Bet P A B \/ Bet P B A.
Proof.
    intros.
    apply H.
Qed.

Lemma out_betOr_sym :  forall P A B, 
  Out P A B -> Bet P B A \/ Bet P A B.
Proof.
    intros.
    apply disjunction_commutativity.
    apply out_betOr.
    assumption.
Qed.

Lemma out_col : forall A B C, 
  Out A B C -> Col A B C.
Proof.
    intros.
    apply out_to_def in H.
    spliter.
    induction H1.
      apply bet_col_123; assumption.
      apply bet_col_132; assumption.
Qed.

Lemma out_distinct : forall A B C,
  Out A B C -> A <> B /\ A <> C.
Proof.
    intros.
    split.
      apply out_diff1 with C; assumption.
      apply out_diff2 with B; assumption.
Qed.

Lemma out_distinct_sym : forall A B C,
  Out A B C -> B <> A /\ C <> A.
Proof.
    intros.
    split.
      apply out_diff1_sym with C; assumption.
      apply out_diff2_sym with B; assumption.
Qed.

End Out_def.


Section Out_prop.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma out_symmetry : forall P A B, 
  Out P A B -> Out P B A.
Proof.
    intros.
    apply out_to_def in H.
    spliter.
    apply disjunction_commutativity in H1.
    apply def_to_out; assumption.
Qed.

Lemma bet_out : forall A B C, 
  A <> B -> Bet A B C -> Out A B C.
Proof.
    intros.
    apply def_to_out.
    repeat split.
      assumption.
      apply bet_neq12__neq with B; assumption.
    left.
    assumption.
Qed.

Lemma bet_out2 : forall A B C, 
  A <> C -> Bet A C B -> Out A B C.
Proof.
    intros.
    apply out_symmetry.
    apply bet_out; assumption.
Qed.

Lemma out_trivial : forall P A,
  A<>P -> Out P A A.
Proof.
    intros.
    apply def_to_out.
    apply diff_symmetry in H.
    repeat split; try assumption.
      apply diff_symmetry; assumption.
    right.
    apply between_trivial_122.
Qed.



(** out transitivity *)

Lemma out_transitivity_2 : forall P A B C,
  Out P A B -> Out P B C -> Out P A C.
Proof.
    intros.
    apply out_to_def in H.
    apply out_to_def in H0.
    spliter.
    repeat split; try assumption.
    induction H4; induction H2.
      left; apply between_exchange_3 with B; assumption.
      apply l5_3 with B; assumption.
      apply l5_1 with B; assumption.
      right; apply between_exchange_3 with B; assumption.
Qed.

Lemma out_transitivity_1 : forall P A B C,
  Out P A B -> Out P A C -> Out P B C.
Proof.
    intros.
    apply out_to_def in H.
    apply out_to_def in H0.
    spliter.
    repeat split.
      assumption.
      assumption.
    induction H2; induction H4.
      apply l5_1 with A; assumption.
      left. apply between_exchange_3 with A; assumption.
      right. apply between_exchange_3 with A; assumption.
      apply l5_3 with A; assumption.
Qed.

Lemma out_transitivity_3 : forall P A B C,
  Out P A C -> Out P B C -> Out P A B.
Proof.
    intros.
    eapply out_transitivity_1 with C.
      apply out_symmetry.
      assumption.
    apply out_symmetry.
    assumption.
Qed.

End Out_prop.

Print All.

